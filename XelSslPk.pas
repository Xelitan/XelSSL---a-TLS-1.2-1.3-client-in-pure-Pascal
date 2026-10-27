// XelSSL - signature verification: RSA PKCS#1 v1.5, RSA-PSS (RFC 8017),
// ECDSA on P-256 / P-384 / P-521 (FIPS 186-4). Public data only.
// Curve parameters: XelSslCurves. License: MIT.
unit XelSslPk;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils, XelSslHash, XelSslBigNum;

type
  TEcCurveId = (ecNone, ecP256, ecP384, ecP521);

// Hashed = message digest (already computed with Alg).
function RsaPkcs1Verify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes): Boolean;
// SaltLen < 0: any salt length (read from the signature). MGF1 with the same hash.
function RsaPssVerify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes; SaltLen: Integer): Boolean;
// Pub = uncompressed point 04||X||Y; SigDer = SEQUENCE{INTEGER r, INTEGER s}.
function EcdsaVerify(Curve: TEcCurveId; const Pub, Hashed, SigDer: TBytes): Boolean;
function EcCoordLen(Curve: TEcCurveId): Integer;

implementation

uses XelSslCurves, XelSslEcdh;

// ================= RSA =================

const
  // DigestInfo DER (RFC 8017 9.2, note 1)
  DI_SHA1   = '3021300906052b0e03021a05000414';
  DI_SHA256 = '3031300d060960864801650304020105000420';
  DI_SHA384 = '3041300d060960864801650304020205000430';
  DI_SHA512 = '3051300d060960864801650304020305000440';

function RsaPublic(const N, E, Sig: TBytes; out EM: TBytes): Boolean;
var bn, be, bs: TBig;
begin
  Result := False; EM := nil;
  bn := BigFromBytes(N); be := BigFromBytes(E); bs := BigFromBytes(Sig);
  if (BigBits(bn) < 1024) or (Length(Sig) <> (BigBits(bn) + 7) div 8) then Exit;   // min. 1024 bits
  if BigCmp(bs, bn) >= 0 then Exit;
  EM := BigToBytes(BigModExp(bs, be, bn), Length(Sig));
  Result := True;
end;

var
  // DigestInfo prefixes as bytes (converted once)
  DigestInfos: array[THashAlg] of TBytes;

procedure InitDigestInfos;
var a: THashAlg;
begin
  for a := Low(THashAlg) to High(THashAlg) do
    case a of
      haSHA1: DigestInfos[a] := FromHex(DI_SHA1);
      haSHA256: DigestInfos[a] := FromHex(DI_SHA256);
      haSHA384: DigestInfos[a] := FromHex(DI_SHA384);
    else DigestInfos[a] := FromHex(DI_SHA512);
    end;
end;

function RsaPkcs1Verify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes): Boolean;
var em, exp, di: TBytes; k, i: Integer;
begin
  Result := False;
  if not RsaPublic(N, E, Sig, em) then Exit;
  if Length(Hashed) <> HashSize(Alg) then Exit;
  di := Concat(DigestInfos[Alg], Hashed);
  k := Length(em);
  if k < Length(di) + 11 then Exit;
  // build the expected EM = 00 01 FF..FF 00 DigestInfo and compare it whole
  SetLength(exp, k);
  exp[0] := 0; exp[1] := 1;
  for i := 2 to k - Length(di) - 2 do exp[i] := $FF;
  exp[k - Length(di) - 1] := 0;
  Move(di[0], exp[k - Length(di)], Length(di));
  Result := SameBytesCT(em, exp);
end;

function Mgf1(Alg: THashAlg; const Seed: TBytes; Len: Integer): TBytes;
var c: UInt32; t, blk: TBytes; off: Integer;
begin
  SetLength(Result, Len);
  c := 0; off := 0;
  while off < Len do
  begin
    blk := Concat(Seed, TBytes.Create(Byte(c shr 24), Byte(c shr 16), Byte(c shr 8), Byte(c)));
    t := Hash(Alg, blk);
    if Len - off < Length(t) then Move(t[0], Result[off], Len - off) else Move(t[0], Result[off], Length(t));
    Inc(off, Length(t)); Inc(c);
  end;
end;

function RsaPssVerify(const N, E: TBytes; Alg: THashAlg; const Hashed, Sig: TBytes; SaltLen: Integer): Boolean;
var
  em, db, h, mask, salt, m2: TBytes;
  modBits, emBits, emLen, hLen, i, ps, topBits: Integer;
begin
  Result := False;
  if not RsaPublic(N, E, Sig, em) then Exit;
  hLen := HashSize(Alg);
  if Length(Hashed) <> hLen then Exit;
  modBits := BigBits(BigFromBytes(N));
  emBits := modBits - 1;
  emLen := (emBits + 7) div 8;
  if Length(em) > emLen then          // modBits = 8k+1: the leading byte must be zero
  begin
    if em[0] <> 0 then Exit;
    em := Copy(em, 1, emLen);
  end;
  if emLen < hLen + 2 then Exit;
  if em[emLen - 1] <> $BC then Exit;
  db := Copy(em, 0, emLen - hLen - 1);
  h := Copy(em, emLen - hLen - 1, hLen);
  topBits := 8 * emLen - emBits;
  if (db[0] and not ($FF shr topBits)) <> 0 then Exit;
  mask := Mgf1(Alg, h, Length(db));
  for i := 0 to High(db) do db[i] := db[i] xor mask[i];
  db[0] := db[0] and ($FF shr topBits);
  // DB = 00..00 || 01 || salt
  ps := 0;
  while (ps < Length(db)) and (db[ps] = 0) do Inc(ps);
  if (ps >= Length(db)) or (db[ps] <> 1) then Exit;
  salt := Copy(db, ps + 1, Length(db) - ps - 1);
  if (SaltLen >= 0) and (Length(salt) <> SaltLen) then Exit;
  SetLength(m2, 8); FillChar(m2[0], 8, 0);
  m2 := Concat(m2, Hashed, salt);
  Result := SameBytesCT(Hash(Alg, m2), h);
end;

// ================= ECDSA =================

type
  TCurve = record
    P, B, N, Gx, Gy: TBig;
    Len: Integer;                  // coordinate bytes
  end;
  TJac = record X, Y, Z: TBig; end;   // Z = 0 -> point at infinity

var
  // curve parameters parsed once (initialization section - thread-safe afterwards)
  Curves: array[TEcCurveId] of TCurve;

function GetCurve(Id: TEcCurveId; out C: TCurve): Boolean;
begin
  if not (Id in [ecP256, ecP384, ecP521]) then Exit(False);
  C := Curves[Id];
  Result := True;
end;

procedure InitCurves;
var id: TEcCurveId; i: Integer;
begin
  for id := Low(TEcCurveId) to High(TEcCurveId) do
  begin
    case id of
      ecP256: i := CURVE_P256;
      ecP384: i := CURVE_P384;
      ecP521: i := CURVE_P521;
    else
      Continue;
    end;
    Curves[id].P := BigFromHex(CurveParams[i].P);
    Curves[id].B := BigFromHex(CurveParams[i].B);
    Curves[id].N := BigFromHex(CurveParams[i].N);
    Curves[id].Gx := BigFromHex(CurveParams[i].Gx);
    Curves[id].Gy := BigFromHex(CurveParams[i].Gy);
    Curves[id].Len := CurveParams[i].Len;
  end;
end;

function EcCoordLen(Curve: TEcCurveId): Integer;
begin
  case Curve of
    ecP256: Result := 32;
    ecP384: Result := 48;
    ecP521: Result := 66;
  else Result := 0;
  end;
end;

// doubling, a = -3 (dbl-2001-b)
function JDouble(const C: TCurve; const A: TJac): TJac;
var delta, gamma, beta, alpha, t, p: TBig;
begin
  p := C.P;
  if BigIsZero(A.Z) or BigIsZero(A.Y) then begin Result.X := nil; Result.Y := BigFromInt(1); Result.Z := nil; Exit; end;
  delta := BigModMul(A.Z, A.Z, p);
  gamma := BigModMul(A.Y, A.Y, p);
  beta := BigModMul(A.X, gamma, p);
  t := BigModMul(BigModSub(A.X, delta, p), BigModAdd(A.X, delta, p), p);
  alpha := BigModAdd(BigModAdd(t, t, p), t, p);
  t := BigModAdd(beta, beta, p); t := BigModAdd(t, t, p); t := BigModAdd(t, t, p);   // 8*beta
  Result.X := BigModSub(BigModMul(alpha, alpha, p), t, p);
  t := BigModAdd(A.Y, A.Z, p);
  Result.Z := BigModSub(BigModSub(BigModMul(t, t, p), gamma, p), delta, p);
  t := BigModAdd(beta, beta, p); t := BigModAdd(t, t, p);                           // 4*beta
  gamma := BigModMul(gamma, gamma, p);
  gamma := BigModAdd(gamma, gamma, p); gamma := BigModAdd(gamma, gamma, p); gamma := BigModAdd(gamma, gamma, p); // 8*gamma^2
  Result.Y := BigModSub(BigModMul(alpha, BigModSub(t, Result.X, p), p), gamma, p);
end;

// addition (add-2007-bl)
function JAdd(const C: TCurve; const A, B: TJac): TJac;
var z1z1, z2z2, u1, u2, s1, s2, h, i, j, r, v, t, p: TBig;
begin
  p := C.P;
  if BigIsZero(A.Z) then Exit(B);
  if BigIsZero(B.Z) then Exit(A);
  z1z1 := BigModMul(A.Z, A.Z, p);
  z2z2 := BigModMul(B.Z, B.Z, p);
  u1 := BigModMul(A.X, z2z2, p);
  u2 := BigModMul(B.X, z1z1, p);
  s1 := BigModMul(BigModMul(A.Y, B.Z, p), z2z2, p);
  s2 := BigModMul(BigModMul(B.Y, A.Z, p), z1z1, p);
  h := BigModSub(u2, u1, p);
  r := BigModSub(s2, s1, p);
  if BigIsZero(h) then
  begin
    if BigIsZero(r) then Exit(JDouble(C, A));
    Result.X := nil; Result.Y := BigFromInt(1); Result.Z := nil; Exit;      // P + (-P)
  end;
  r := BigModAdd(r, r, p);
  t := BigModAdd(h, h, p);
  i := BigModMul(t, t, p);
  j := BigModMul(h, i, p);
  v := BigModMul(u1, i, p);
  Result.X := BigModSub(BigModSub(BigModMul(r, r, p), j, p), BigModAdd(v, v, p), p);
  t := BigModMul(s1, j, p);
  Result.Y := BigModSub(BigModMul(r, BigModSub(v, Result.X, p), p), BigModAdd(t, t, p), p);
  t := BigModAdd(A.Z, B.Z, p);
  Result.Z := BigModMul(BigModSub(BigModSub(BigModMul(t, t, p), z1z1, p), z2z2, p), h, p);
end;

function OnCurve(const C: TCurve; const X, Y: TBig): Boolean;
var l, r, x3, three: TBig;
begin
  // y^2 = x^3 - 3x + b
  if (BigCmp(X, C.P) >= 0) or (BigCmp(Y, C.P) >= 0) then Exit(False);
  l := BigModMul(Y, Y, C.P);
  x3 := BigModMul(BigModMul(X, X, C.P), X, C.P);
  three := BigModMul(BigFromInt(3), X, C.P);
  r := BigModAdd(BigModSub(x3, three, C.P), C.B, C.P);
  Result := BigCmp(l, r) = 0;
end;

// simple parser for SEQUENCE { INTEGER r, INTEGER s }
function ParseEcdsaSig(const D: TBytes; out R, S: TBig): Boolean;
var pos: Integer;
  function ReadLen(out L: Integer): Boolean;
  var nb, k: Integer;
  begin
    Result := False;
    if pos >= Length(D) then Exit;
    L := D[pos]; Inc(pos);
    if L < $80 then Exit(True);
    nb := L and $7F;
    if (nb = 0) or (nb > 2) or (pos + nb > Length(D)) then Exit;
    L := 0;
    for k := 1 to nb do begin L := (L shl 8) or D[pos]; Inc(pos); end;
    Result := True;
  end;
  function ReadInt(out V: TBig): Boolean;
  var l: Integer;
  begin
    Result := False;
    if (pos >= Length(D)) or (D[pos] <> $02) then Exit;
    Inc(pos);
    if not ReadLen(l) or (l = 0) or (pos + l > Length(D)) then Exit;
    if (D[pos] and $80) <> 0 then Exit;                 // negative
    V := BigFromBytes(Copy(D, pos, l));
    Inc(pos, l);
    Result := True;
  end;
var l: Integer;
begin
  Result := False; pos := 0;
  if (Length(D) < 8) or (D[0] <> $30) then Exit;
  Inc(pos);
  if not ReadLen(l) or (pos + l <> Length(D)) then Exit;
  if not ReadInt(R) then Exit;
  if not ReadInt(S) then Exit;
  Result := pos = Length(D);
end;

function EcdsaVerify(Curve: TEcCurveId; const Pub, Hashed, SigDer: TBytes): Boolean;
var C: TCurve; r, s, e, w, u1, u2: TBig; nb: Integer; ec: TEcdhCurve;
begin
  Result := False;
  if not GetCurve(Curve, C) then Exit;
  if not ParseEcdsaSig(SigDer, r, s) then Exit;
  if BigIsZero(r) or BigIsZero(s) or (BigCmp(r, C.N) >= 0) or (BigCmp(s, C.N) >= 0) then Exit;
  // e = leftmost bits of the hash (as many as n has)
  e := BigFromBytes(Hashed);
  nb := BigBits(C.N);
  if Length(Hashed) * 8 > nb then e := BigShr(e, Length(Hashed) * 8 - nb);
  w := BigModInvOdd(s, C.N);                   // public value: fast variable-time inverse
  u1 := BigModMul(BigMod(e, C.N), w, C.N);
  u2 := BigModMul(r, w, C.N);
  case Curve of
    ecP256: ec := ecdhP256;
    ecP384: ec := ecdhP384;
  else ec := ecdhP521;
  end;
  // u1*G + u2*Q with the fast field arithmetic of XelSslEcdh (point checked there)
  Result := EcVerifyCombination(ec, Pub, BigToBytes(u1), BigToBytes(u2), BigToBytes(r));
end;

initialization
  InitCurves;
  InitDigestInfos;
end.
