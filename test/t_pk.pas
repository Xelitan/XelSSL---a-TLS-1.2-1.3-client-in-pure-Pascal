// XelSSL signature verification tests on openssl vectors (gen_pk.py).
program t_pk;

{$mode objfpc}{$H+}

uses
  SysUtils, Classes, XelSslCpu, XelSslHash, XelSslBigNum, XelSslPk, XelSslEcdh;

var
  pass: Integer;
  Fails, Checks: Integer;

procedure Check(const Name: string; Ok: Boolean);
begin
  Inc(Checks);
  if not Ok then begin Inc(Fails); WriteLn('FAIL: ', Name); end;
end;

function HashOf(const S: string): THashAlg;
begin
  if S = 'sha1' then Result := haSHA1
  else if S = 'sha256' then Result := haSHA256
  else if S = 'sha384' then Result := haSHA384
  else Result := haSHA512;
end;

function CurveOf(const S: string): TEcCurveId;
begin
  if S = 'P-256' then Result := ecP256
  else if S = 'P-384' then Result := ecP384
  else Result := ecP521;
end;

function Flip(const B: TBytes; I: Integer): TBytes;
begin
  Result := Copy(B);
  Result[I mod Length(Result)] := Result[I mod Length(Result)] xor $01;
end;

// Montgomery BigModExp against the division-based one: odd moduli of 1..70 limbs,
// short and long exponents, bases larger than the modulus
// BigModInvOdd: a * a^-1 = 1 (mod m) for random odd moduli of 1..40 limbs
procedure TestModInv;
var i, k: Integer; m, a, x: TBig;
begin
  for i := 1 to 400 do
  begin
    k := 1 + Random(40);
    SetLength(m, k);
    for k := 0 to High(m) do m[k] := UInt32(Random($10000)) or (UInt32(Random($10000)) shl 16);
    m[0] := m[0] or 1;
    m[High(m)] := m[High(m)] or 1;
    SetLength(a, 1 + Random(Length(m) + 1));
    for k := 0 to High(a) do a[k] := UInt32(Random($10000)) or (UInt32(Random($10000)) shl 16);
    while (Length(a) > 0) and (a[High(a)] = 0) do SetLength(a, Length(a) - 1);
    x := BigModInvOdd(a, m);
    if x = nil then
    begin
      // no inverse: gcd > 1 or a = 0 mod m (the bit-by-bit Euclid agrees)
      Check(Format('modinv none %d limbs', [Length(m)]), BigModInvOdd32(a, m) = nil);
      Continue;
    end;
    Check(Format('modinv %d limbs', [Length(m)]), BigCmp(BigModMul(a, x, m), BigFromInt(1)) = 0);
  end;
  // P-256 / P-384 group orders, the values used by ECDSA; edges 1, 2, n - 1, a > m;
  // a common factor (m = 3 * 5 * ...)
  for i := 1 to 3000 do
  begin
    case i mod 3 of
      0: m := BigFromBytes(FromHex('FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551'));
      1: m := BigFromBytes(FromHex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973'));
    else
      begin
        SetLength(m, 1 + Random(21));
        for k := 0 to High(m) do m[k] := UInt32(Random($10000)) or (UInt32(Random($10000)) shl 16);
        m[0] := m[0] or 1; if m[High(m)] = 0 then m[High(m)] := 1;
      end;
    end;
    SetLength(a, Length(m));
    for k := 0 to High(a) do a[k] := UInt32(Random($10000)) or (UInt32(Random($10000)) shl 16);
    case i mod 17 of
      0: a := BigFromInt(1);
      1: a := BigFromInt(2);
      2: a := BigSub(m, BigFromInt(1));
      3: a := BigAdd(m, BigFromInt(5));
      4: a := BigFromInt(3 * (1 + Random(1000)));
    end;
    while (Length(a) > 0) and (a[High(a)] = 0) do SetLength(a, Length(a) - 1);
    if i mod 23 = 0 then m := BigMul(m, BigFromInt(3));
    if (m[0] and 1) = 0 then Continue;
    x := BigModInvOdd(a, m);
    if x = nil then
    begin
      Check(Format('modinv(2) none %d', [i]), BigModInvOdd32(a, m) = nil);
      Continue;
    end;
    Check(Format('modinv(2) %d', [i]), (BigCmp(x, m) < 0) and (BigCmp(BigModMul(a, x, m), BigFromInt(1)) = 0));
  end;
end;

procedure TestModExp;
var i, k, k2: Integer; m, b, e, r1, r2: TBig;
  function RndBig(Limbs: Integer): TBig;
  var j: Integer;
  begin
    SetLength(Result, Limbs);
    for j := 0 to Limbs - 1 do Result[j] := UInt32(Random($10000)) or (UInt32(Random($10000)) shl 16);
    while (Length(Result) > 0) and (Result[High(Result)] = 0) do SetLength(Result, Length(Result) - 1);
  end;
begin
  for i := 1 to 400 do
  begin
    k := 1 + Random(70);
    if i mod 50 = 0 then k := 64;                          // RSA-2048
    if i mod 3 = 0 then k := 8 * (1 + Random(16));         // multiples of 256 bits: MULX kernel
    m := RndBig(k);
    if Length(m) = 0 then Continue;
    m[0] := m[0] or 1;
    if (Length(m) = 1) and (m[0] = 1) then Continue;
    b := RndBig(1 + Random(k + 2));
    if i mod 7 = 0 then
    begin
      for k2 := 0 to High(m) do m[k2] := $FFFFFFFF;    // N = 2^(32k) - 1 (odd), base = N - 1
      b := Copy(m); b[0] := b[0] - 1;
    end;
    case Random(4) of
      0: e := BigFromInt(65537);
      1: e := RndBig(1 + Random(2));
      2: e := RndBig(1 + Random(k));
    else e := BigFromInt(Random(5));
    end;
    BigUseMont := False; r1 := BigModExp(b, e, m);
    BigUseMont := True;  r2 := BigModExp(b, e, m);
    Check(Format('modexp %d limbs, exp %d bits', [k, BigBits(e)]), BigCmp(r1, r2) = 0);
    BigUseMontx := False; r2 := BigModExp(b, e, m); BigUseMontx := True;
    Check(Format('modexp without MULX %d limbs', [k]), BigCmp(r1, r2) = 0);
    BigUseMontSqr := False; r2 := BigModExp(b, e, m); BigUseMontSqr := True;
    Check(Format('modexp without the squaring kernel %d limbs', [k]), BigCmp(r1, r2) = 0);
  end;
end;

var
  L: TStringList; f: TStringArray; i: Integer; t0: QWord;
  n, e, h, sig, pub: TBytes; alg: THashAlg; nm: string; ms: QWord;
begin
  // XELSSL_TEST_NOMULX=1: the P-256 multiplication without MULX/ADX
  if GetEnvironmentVariable('XELSSL_TEST_NOMULX') = '1' then EcdhUseMulx := False;
  Fails := 0; Checks := 0;
  L := TStringList.Create;
  L.LoadFromFile(ExtractFilePath(ParamStr(0)) + 'pk_vectors.txt');
  // pass 1 with the assembler additions, pass 2 Pascal only
  for pass := 1 to 2 do
  begin
  XelSslAsm := pass = 1;
  WriteLn('  assembler additions: ', XelSslAsm and (CpuFeatures <> []));
  TestModExp;
  TestModInv;
  t0 := GetTickCount64;
  for i := 0 to L.Count - 1 do
  begin
    if L[i] = '' then Continue;
    f := L[i].Split(['|']);
    nm := Format('#%d %s %s', [i, f[0], f[1]]);
    if f[0] = 'rsa1' then
    begin
      alg := HashOf(f[1]); n := FromHex(f[2]); e := FromHex(f[3]); h := FromHex(f[4]); sig := FromHex(f[5]);
      Check(nm + ' ok', RsaPkcs1Verify(n, e, alg, h, sig));
      Check(nm + ' bad signature', not RsaPkcs1Verify(n, e, alg, h, Flip(sig, 17)));
      Check(nm + ' bad hash', not RsaPkcs1Verify(n, e, alg, Flip(h, 3), sig));
    end
    else if f[0] = 'pss' then
    begin
      alg := HashOf(f[1]); n := FromHex(f[2]); e := FromHex(f[3]); h := FromHex(f[4]); sig := FromHex(f[5]);
      Check(nm + ' ok', RsaPssVerify(n, e, alg, h, sig, StrToInt(f[6])));
      Check(nm + ' ok (any salt)', RsaPssVerify(n, e, alg, h, sig, -1));
      Check(nm + ' wrong salt', not RsaPssVerify(n, e, alg, h, sig, StrToInt(f[6]) + 1));
      Check(nm + ' bad signature', not RsaPssVerify(n, e, alg, h, Flip(sig, 5), -1));
      Check(nm + ' bad hash', not RsaPssVerify(n, e, alg, Flip(h, 0), sig, -1));
      Check(nm + ' pkcs1 != pss', not RsaPkcs1Verify(n, e, alg, h, sig));
    end
    else if f[0] = 'ec' then
    begin
      pub := FromHex(f[2]); h := FromHex(f[4]); sig := FromHex(f[5]);
      ms := GetTickCount64;
      Check(nm + ' ok', EcdsaVerify(CurveOf(f[1]), pub, h, sig));
      if i mod 4 = 0 then WriteLn(Format('  %s %s verification %d ms', [f[1], f[3], GetTickCount64 - ms]));
      Check(nm + ' bad hash', not EcdsaVerify(CurveOf(f[1]), pub, Flip(h, 1), sig));
      Check(nm + ' bad signature', not EcdsaVerify(CurveOf(f[1]), pub, h, Flip(sig, Length(sig) - 2)));
      Check(nm + ' bad key', not EcdsaVerify(CurveOf(f[1]), Flip(pub, 10), h, sig));
    end;
  end;
  WriteLn(Format('  %d ms', [GetTickCount64 - t0]));
  end;
  XelSslAsm := True;
  WriteLn(Format('signatures: %d checks, %d failures', [Checks, Fails]));
  L.Free;
  if Fails > 0 then Halt(1);
end.
