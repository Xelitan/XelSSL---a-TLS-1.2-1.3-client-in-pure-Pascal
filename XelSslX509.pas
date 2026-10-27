// XelSSL - X.509 certificates (RFC 5280): DER parser, signature verification,
// path building and validation (dates, basicConstraints/pathLen, keyUsage, EKU
// serverAuth, nameConstraints dNSName/iPAddress/directoryName, unknown critical
// extensions), host name matching (RFC 6125) and TLS signature verification
// (SignatureScheme). License: MIT.
unit XelSslX509;

{$mode objfpc}{$H+}{$Q-}{$R-}

interface

uses
  SysUtils, XelSslHash, XelSslPk;

type
  TBytesArray = array of TBytes;
  TKeyKind = (kkUnknown, kkRsa, kkRsaPss, kkEc, kkEd25519);

  TCert = record
    Raw, Tbs: TBytes;
    SigAlg: string;                 // signature OID (outer == inner)
    SigParams: TBytes;              // parameters (RSASSA-PSS)
    Signature: TBytes;
    Version: Integer;
    Serial: TBytes;
    IssuerRaw, SubjectRaw: TBytes;  // DER Name - compared byte-wise
    SubjectCN, IssuerCN: string;
    NotBefore, NotAfter: TDateTime; // UTC
    KeyKind: TKeyKind;
    Curve: TEcCurveId;
    PubKey: TBytes;                 // EC: point; Ed25519: 32 bytes
    RsaN, RsaE: TBytes;
    SpkiRaw: TBytes;
    HasBC, IsCA: Boolean;
    PathLen: Integer;               // -1 = no limit
    HasKU: Boolean; KeyUsage: Word; // bit 0 = digitalSignature ... bit 5 = keyCertSign (RFC numbering)
    HasEKU, EkuServerAuth: Boolean;
    DnsNames: TStringArray;
    IpAddrs: TBytesArray;
    HasNC: Boolean;
    PermDns, ExclDns: TStringArray;
    PermIp, ExclIp: TBytesArray;         // address || mask
    PermDir, ExclDir: TBytesArray;       // [4] Name (content)
    UnknownCritical: Boolean;
  end;
  TCertArray = array of TCert;

  TVerifyResult = (vrOk, vrBadCert, vrExpired, vrUnknownCA, vrBadSignature,
    vrNameMismatch, vrBadUsage, vrUnsupported);

function ParseCert(const Der: TBytes; out C: TCert): Boolean;
function CertSignedBy(const C, Issuer: TCert): Boolean;
function HostMatches(const C: TCert; const Host: string): Boolean;

// Server chain validation. Chain[0] = server certificate, the rest = intermediates
// (any order). Anchors = trusted roots, Pool = extra intermediates
// (e.g. the system CA store). NowUtc = validation time.
function VerifyChain(const Chain: array of TBytes; const Host: string;
  const Anchors, Pool: TCertArray; NowUtc: TDateTime; out Err: string): TVerifyResult;

// TLS signature (SignatureScheme from RFC 8446) with the certificate key.
function TlsVerifySignature(const Leaf: TCert; Scheme: Word; const Data, Sig: TBytes): Boolean;
function TlsSchemeSupported(Scheme: Word): Boolean;

function ParseIp(const S: string; out Ip: TBytes): Boolean;
function NowUtc: TDateTime;

implementation

uses DateUtils, StrUtils;

// ================= DER =================

type
  TDer = record
    Tag: Byte;
    Start, Len: Integer;     // content: B[Start .. Start+Len-1]
    Next: Integer;           // position of the next element
    HdrStart: Integer;
  end;

function DerRead(const B: TBytes; Pos, Limit: Integer; out D: TDer): Boolean;
var l, nb, i: Integer;
begin
  Result := False;
  if Limit > Length(B) then Limit := Length(B);
  if Pos + 2 > Limit then Exit;
  D.HdrStart := Pos;
  D.Tag := B[Pos]; Inc(Pos);
  if (D.Tag and $1F) = $1F then Exit;            // multi-byte tags do not occur in X.509
  l := B[Pos]; Inc(Pos);
  if l >= $80 then
  begin
    nb := l and $7F;
    if (nb = 0) or (nb > 3) or (Pos + nb > Limit) then Exit;
    l := 0;
    for i := 1 to nb do begin l := (l shl 8) or B[Pos]; Inc(Pos); end;
  end;
  if (l < 0) or (Pos + l > Limit) then Exit;
  D.Start := Pos; D.Len := l; D.Next := Pos + l;
  Result := True;
end;

function DerBytes(const B: TBytes; const D: TDer): TBytes;
begin
  Result := Copy(B, D.Start, D.Len);
end;

function DerWhole(const B: TBytes; const D: TDer): TBytes;
begin
  Result := Copy(B, D.HdrStart, D.Next - D.HdrStart);
end;

function OidStr(const B: TBytes; const D: TDer): string;
var i: Integer; v: QWord; first: Boolean;
begin
  Result := ''; v := 0; first := True;
  for i := D.Start to D.Start + D.Len - 1 do
  begin
    v := (v shl 7) or (B[i] and $7F);
    if (B[i] and $80) = 0 then
    begin
      if first then
      begin
        if v < 40 then Result := '0.' + IntToStr(v)
        else if v < 80 then Result := '1.' + IntToStr(v - 40)
        else Result := '2.' + IntToStr(v - 80);
        first := False;
      end
      else Result := Result + '.' + IntToStr(v);
      v := 0;
    end;
  end;
end;

function ParseTime(const B: TBytes; const D: TDer; out T: TDateTime): Boolean;
var s: string; y, mo, dd, h, mi, se: Integer;
begin
  Result := False;
  SetString(s, PAnsiChar(@B[D.Start]), D.Len);
  if (Length(s) < 13) or (s[Length(s)] <> 'Z') then Exit;
  if D.Tag = $17 then                                // UTCTime YYMMDDHHMMSSZ
  begin
    if Length(s) <> 13 then Exit;
    y := StrToIntDef(Copy(s, 1, 2), -1);
    if y < 0 then Exit;
    if y >= 50 then y := 1900 + y else y := 2000 + y;
    Delete(s, 1, 2);
  end
  else if D.Tag = $18 then                           // GeneralizedTime YYYYMMDDHHMMSSZ
  begin
    if Length(s) <> 15 then Exit;
    y := StrToIntDef(Copy(s, 1, 4), -1);
    Delete(s, 1, 4);
  end
  else Exit;
  mo := StrToIntDef(Copy(s, 1, 2), -1); dd := StrToIntDef(Copy(s, 3, 2), -1);
  h := StrToIntDef(Copy(s, 5, 2), -1); mi := StrToIntDef(Copy(s, 7, 2), -1);
  se := StrToIntDef(Copy(s, 9, 2), -1);
  Result := TryEncodeDateTime(y, mo, dd, h, mi, se, 0, T);
end;

// CN from a Name (for messages only)
function NameCN(const B: TBytes; const Name: TDer): string;
var rdn, atv, oid, val: TDer; p, q: Integer;
begin
  Result := '';
  p := Name.Start;
  while (p < Name.Start + Name.Len) and DerRead(B, p, Name.Start + Name.Len, rdn) do
  begin
    q := rdn.Start;
    while (q < rdn.Next) and DerRead(B, q, rdn.Next, atv) do
    begin
      if DerRead(B, atv.Start, atv.Next, oid) and (oid.Tag = 6) and (OidStr(B, oid) = '2.5.4.3') and
         DerRead(B, oid.Next, atv.Next, val) then
        SetString(Result, PAnsiChar(@B[val.Start]), val.Len);
      q := atv.Next;
    end;
    p := rdn.Next;
  end;
end;

// ================= extensions =================

procedure AddStr(var A: TStringArray; const S: string);
begin SetLength(A, Length(A) + 1); A[High(A)] := S; end;

procedure AddBytes(var A: TBytesArray; const S: TBytes);
begin SetLength(A, Length(A) + 1); A[High(A)] := S; end;

function ParseSubtrees(const B: TBytes; const D: TDer; var Dns: TStringArray;
  var Ip: TBytesArray; var Dir: TBytesArray): Boolean;
var sub, base: TDer; p: Integer; s: string;
begin
  Result := True;
  p := D.Start;
  while p < D.Next do
  begin
    if not DerRead(B, p, D.Next, sub) or (sub.Tag <> $30) then Exit(False);
    if not DerRead(B, sub.Start, sub.Next, base) then Exit(False);
    case base.Tag of
      $82: begin SetString(s, PAnsiChar(@B[base.Start]), base.Len); AddStr(Dns, LowerCase(s)); end;
      $87: if base.Len in [8, 32] then AddBytes(Ip, DerBytes(B, base)) else Exit(False);
      $A4: AddBytes(Dir, DerBytes(B, base));          // [4] Name (explicit) -> contains a SEQUENCE
    end;                                               // other types (email, URI) do not apply to TLS
    p := sub.Next;
  end;
end;

function ParseExtensions(const B: TBytes; const D: TDer; var C: TCert): Boolean;
var ext, oid, crit, val, inner, it, x: TDer; p, q, i: Integer; o, s: string; isCrit: Boolean;
begin
  Result := False;
  p := D.Start;
  while p < D.Next do
  begin
    if not DerRead(B, p, D.Next, ext) or (ext.Tag <> $30) then Exit;
    if not DerRead(B, ext.Start, ext.Next, oid) or (oid.Tag <> 6) then Exit;
    o := OidStr(B, oid);
    isCrit := False;
    if not DerRead(B, oid.Next, ext.Next, crit) then Exit;
    if crit.Tag = 1 then
    begin
      isCrit := (crit.Len = 1) and (B[crit.Start] <> 0);
      if not DerRead(B, crit.Next, ext.Next, val) then Exit;
    end
    else val := crit;
    if val.Tag <> 4 then Exit;
    if not DerRead(B, val.Start, val.Next, inner) then Exit;

    if o = '2.5.29.19' then                        // basicConstraints
    begin
      C.HasBC := True;
      q := inner.Start;
      if (q < inner.Next) and DerRead(B, q, inner.Next, it) and (it.Tag = 1) then
      begin
        C.IsCA := (it.Len = 1) and (B[it.Start] <> 0);
        q := it.Next;
      end;
      if (q < inner.Next) and DerRead(B, q, inner.Next, it) and (it.Tag = 2) then
      begin
        C.PathLen := 0;
        for i := it.Start to it.Next - 1 do C.PathLen := (C.PathLen shl 8) or B[i];
        if C.PathLen > 100 then C.PathLen := 100;
      end;
    end
    else if o = '2.5.29.15' then                   // keyUsage (BIT STRING)
    begin
      if (inner.Tag <> 3) or (inner.Len < 2) then Exit;
      C.HasKU := True;
      C.KeyUsage := 0;
      for i := 0 to 7 do                           // bits numbered from the most significant
        if (B[inner.Start + 1] and ($80 shr i)) <> 0 then C.KeyUsage := C.KeyUsage or (1 shl i);
      if (inner.Len >= 3) and ((B[inner.Start + 2] and $80) <> 0) then C.KeyUsage := C.KeyUsage or (1 shl 8);
    end
    else if o = '2.5.29.37' then                   // extKeyUsage
    begin
      C.HasEKU := True;
      q := inner.Start;
      while (q < inner.Next) and DerRead(B, q, inner.Next, it) do
      begin
        s := OidStr(B, it);
        if (s = '1.3.6.1.5.5.7.3.1') or (s = '2.5.29.37.0') then C.EkuServerAuth := True;
        q := it.Next;
      end;
    end
    else if o = '2.5.29.17' then                   // subjectAltName
    begin
      q := inner.Start;
      while (q < inner.Next) and DerRead(B, q, inner.Next, it) do
      begin
        if it.Tag = $82 then
        begin
          SetString(s, PAnsiChar(@B[it.Start]), it.Len);
          SetLength(C.DnsNames, Length(C.DnsNames) + 1);
          C.DnsNames[High(C.DnsNames)] := LowerCase(s);
        end
        else if (it.Tag = $87) and (it.Len in [4, 16]) then
        begin
          SetLength(C.IpAddrs, Length(C.IpAddrs) + 1);
          C.IpAddrs[High(C.IpAddrs)] := DerBytes(B, it);
        end;
        q := it.Next;
      end;
    end
    else if o = '2.5.29.30' then                   // nameConstraints
    begin
      C.HasNC := True;
      q := inner.Start;
      while (q < inner.Next) and DerRead(B, q, inner.Next, x) do
      begin
        if x.Tag = $A0 then
        begin
          if not ParseSubtrees(B, x, C.PermDns, C.PermIp, C.PermDir) then Exit;
        end
        else if x.Tag = $A1 then
        begin
          if not ParseSubtrees(B, x, C.ExclDns, C.ExclIp, C.ExclDir) then Exit;
        end;
        q := x.Next;
      end;
    end
    else if isCrit then
    begin
      // known, not affecting TLS validation: policies, SKI/AKI, CRL DP, AIA, SCT, TLS feature
      if not ((o = '2.5.29.32') or (o = '2.5.29.14') or (o = '2.5.29.35') or (o = '2.5.29.31') or
              (o = '2.5.29.36') or (o = '2.5.29.54') or (o = '1.3.6.1.5.5.7.1.1') or
              (o = '1.3.6.1.4.1.11129.2.4.2') or (o = '1.3.6.1.5.5.7.1.24')) then
        C.UnknownCritical := True;
    end;
    p := ext.Next;
  end;
  Result := True;
end;

// ================= certificate =================

function ParseSpki(const B: TBytes; const D: TDer; var C: TCert): Boolean;
var alg, oid, par, bits, rsa, n, e: TDer; o, co: string; key: TBytes;
begin
  Result := False;
  C.SpkiRaw := DerWhole(B, D);
  if not DerRead(B, D.Start, D.Next, alg) or (alg.Tag <> $30) then Exit;
  if not DerRead(B, alg.Start, alg.Next, oid) or (oid.Tag <> 6) then Exit;
  o := OidStr(B, oid);
  if not DerRead(B, alg.Next, D.Next, bits) or (bits.Tag <> 3) or (bits.Len < 1) or (B[bits.Start] <> 0) then Exit;
  key := Copy(B, bits.Start + 1, bits.Len - 1);
  if (o = '1.2.840.113549.1.1.1') or (o = '1.2.840.113549.1.1.10') then
  begin
    if o = '1.2.840.113549.1.1.1' then C.KeyKind := kkRsa else C.KeyKind := kkRsaPss;
    if not DerRead(key, 0, Length(key), rsa) or (rsa.Tag <> $30) then Exit;
    if not DerRead(key, rsa.Start, rsa.Next, n) or (n.Tag <> 2) then Exit;
    if not DerRead(key, n.Next, rsa.Next, e) or (e.Tag <> 2) then Exit;
    C.RsaN := DerBytes(key, n); C.RsaE := DerBytes(key, e);
    while (Length(C.RsaN) > 1) and (C.RsaN[0] = 0) do Delete(C.RsaN, 0, 1);
    while (Length(C.RsaE) > 1) and (C.RsaE[0] = 0) do Delete(C.RsaE, 0, 1);
  end
  else if o = '1.2.840.10045.2.1' then
  begin
    C.KeyKind := kkEc;
    if not DerRead(B, oid.Next, alg.Next, par) or (par.Tag <> 6) then Exit;
    co := OidStr(B, par);
    if co = '1.2.840.10045.3.1.7' then C.Curve := ecP256
    else if co = '1.3.132.0.34' then C.Curve := ecP384
    else if co = '1.3.132.0.35' then C.Curve := ecP521
    else C.Curve := ecNone;
    C.PubKey := key;
  end
  else if o = '1.3.101.112' then
  begin
    C.KeyKind := kkEd25519;
    C.PubKey := key;
  end
  else C.KeyKind := kkUnknown;
  Result := True;
end;

function ParseCert(const Der: TBytes; out C: TCert): Boolean;
var
  cert, tbs, sa, sv, x, ver, ser, sig2, iss, valid, nb, na, subj, spki: TDer;
  p: Integer;
begin
  Result := False;
  C := Default(TCert);
  C.PathLen := -1;
  C.Raw := Der;
  if not DerRead(Der, 0, Length(Der), cert) or (cert.Tag <> $30) or (cert.Next <> Length(Der)) then Exit;
  if not DerRead(Der, cert.Start, cert.Next, tbs) or (tbs.Tag <> $30) then Exit;
  if not DerRead(Der, tbs.Next, cert.Next, sa) or (sa.Tag <> $30) then Exit;
  if not DerRead(Der, sa.Next, cert.Next, sv) or (sv.Tag <> 3) or (sv.Len < 1) or (Der[sv.Start] <> 0) then Exit;
  C.Tbs := DerWhole(Der, tbs);
  C.Signature := Copy(Der, sv.Start + 1, sv.Len - 1);
  if not DerRead(Der, sa.Start, sa.Next, x) or (x.Tag <> 6) then Exit;
  C.SigAlg := OidStr(Der, x);
  if x.Next < sa.Next then C.SigParams := Copy(Der, x.Next, sa.Next - x.Next);
  // TBS
  p := tbs.Start;
  C.Version := 1;
  if not DerRead(Der, p, tbs.Next, x) then Exit;
  if x.Tag = $A0 then
  begin
    if not DerRead(Der, x.Start, x.Next, ver) or (ver.Tag <> 2) or (ver.Len <> 1) then Exit;
    C.Version := Der[ver.Start] + 1;
    p := x.Next;
  end;
  if not DerRead(Der, p, tbs.Next, ser) or (ser.Tag <> 2) then Exit;
  C.Serial := DerBytes(Der, ser);
  if not DerRead(Der, ser.Next, tbs.Next, sig2) or (sig2.Tag <> $30) then Exit;
  if not SameBytesCT(DerWhole(Der, sig2), DerWhole(Der, sa)) then Exit;   // RFC 5280 4.1.1.2
  if not DerRead(Der, sig2.Next, tbs.Next, iss) or (iss.Tag <> $30) then Exit;
  C.IssuerRaw := DerWhole(Der, iss);
  C.IssuerCN := NameCN(Der, iss);
  if not DerRead(Der, iss.Next, tbs.Next, valid) or (valid.Tag <> $30) then Exit;
  if not DerRead(Der, valid.Start, valid.Next, nb) or not ParseTime(Der, nb, C.NotBefore) then Exit;
  if not DerRead(Der, nb.Next, valid.Next, na) or not ParseTime(Der, na, C.NotAfter) then Exit;
  if not DerRead(Der, valid.Next, tbs.Next, subj) or (subj.Tag <> $30) then Exit;
  C.SubjectRaw := DerWhole(Der, subj);
  C.SubjectCN := NameCN(Der, subj);
  if not DerRead(Der, subj.Next, tbs.Next, spki) or (spki.Tag <> $30) then Exit;
  if not ParseSpki(Der, spki, C) then Exit;
  p := spki.Next;
  while p < tbs.Next do
  begin
    if not DerRead(Der, p, tbs.Next, x) then Exit;
    if x.Tag = $A3 then
    begin
      if not DerRead(Der, x.Start, x.Next, ver) or (ver.Tag <> $30) then Exit;
      if not ParseExtensions(Der, ver, C) then Exit;
    end;
    p := x.Next;
  end;
  Result := True;
end;

// ================= signatures =================

function HashForOid(const O: string; out A: THashAlg): Boolean;
begin
  Result := True;
  if O = '2.16.840.1.101.3.4.2.1' then A := haSHA256
  else if O = '2.16.840.1.101.3.4.2.2' then A := haSHA384
  else if O = '2.16.840.1.101.3.4.2.3' then A := haSHA512
  else if O = '1.3.14.3.2.26' then A := haSHA1
  else Result := False;
end;

// RSASSA-PSS-params ::= SEQUENCE { [0] hash, [1] mgf, [2] saltLength, [3] trailer }
function ParsePssParams(const P: TBytes; out A: THashAlg; out Salt: Integer): Boolean;
var seq, f, alg, oid, mg, mgp, mgo: TDer; q, i: Integer;
begin
  Result := False;
  A := haSHA1; Salt := 20;
  if not DerRead(P, 0, Length(P), seq) or (seq.Tag <> $30) then Exit;
  q := seq.Start;
  while q < seq.Next do
  begin
    if not DerRead(P, q, seq.Next, f) then Exit;
    case f.Tag of
      $A0: begin
             if not DerRead(P, f.Start, f.Next, alg) or not DerRead(P, alg.Start, alg.Next, oid) then Exit;
             if not HashForOid(OidStr(P, oid), A) then Exit;
           end;
      $A1: begin   // MGF1 with the same hash
             if not DerRead(P, f.Start, f.Next, mg) or not DerRead(P, mg.Start, mg.Next, oid) then Exit;
             if OidStr(P, oid) <> '1.2.840.113549.1.1.8' then Exit;
             if not DerRead(P, oid.Next, mg.Next, mgp) or not DerRead(P, mgp.Start, mgp.Next, mgo) then Exit;
           end;
      $A2: begin
             if not DerRead(P, f.Start, f.Next, alg) or (alg.Tag <> 2) or (alg.Len > 2) then Exit;
             Salt := 0;
             for i := alg.Start to alg.Next - 1 do Salt := (Salt shl 8) or P[i];
           end;
    end;
    q := f.Next;
  end;
  Result := A <> haSHA1;     // PSS with SHA-1 is rejected
end;

function VerifyWithKey(const Key: TCert; const Alg: string; const Params, Data, Sig: TBytes): Boolean;
var h: THashAlg; salt: Integer;
begin
  Result := False;
  if (Alg = '1.2.840.113549.1.1.11') or (Alg = '1.2.840.113549.1.1.12') or (Alg = '1.2.840.113549.1.1.13') then
  begin
    if Key.KeyKind <> kkRsa then Exit;
    if Length(Key.RsaN) < 256 then Exit;                         // min. RSA 2048
    if Alg = '1.2.840.113549.1.1.11' then h := haSHA256
    else if Alg = '1.2.840.113549.1.1.12' then h := haSHA384 else h := haSHA512;
    Result := RsaPkcs1Verify(Key.RsaN, Key.RsaE, h, Hash(h, Data), Sig);
  end
  else if Alg = '1.2.840.113549.1.1.10' then
  begin
    if not (Key.KeyKind in [kkRsa, kkRsaPss]) or (Length(Key.RsaN) < 256) then Exit;
    if not ParsePssParams(Params, h, salt) then Exit;
    Result := RsaPssVerify(Key.RsaN, Key.RsaE, h, Hash(h, Data), Sig, salt);
  end
  else if (Alg = '1.2.840.10045.4.3.2') or (Alg = '1.2.840.10045.4.3.3') or (Alg = '1.2.840.10045.4.3.4') then
  begin
    if (Key.KeyKind <> kkEc) or (Key.Curve = ecNone) then Exit;
    if Alg = '1.2.840.10045.4.3.2' then h := haSHA256
    else if Alg = '1.2.840.10045.4.3.3' then h := haSHA384 else h := haSHA512;
    Result := EcdsaVerify(Key.Curve, Key.PubKey, Hash(h, Data), Sig);
  end;
  // sha1WithRSA, Ed25519 and others: unsupported in chains -> False
end;

function CertSignedBy(const C, Issuer: TCert): Boolean;
begin
  Result := SameBytesCT(C.IssuerRaw, Issuer.SubjectRaw) and
    VerifyWithKey(Issuer, C.SigAlg, C.SigParams, C.Tbs, C.Signature);
end;

function TlsSchemeSupported(Scheme: Word): Boolean;
begin
  case Scheme of
    $0201, $0401, $0501, $0601, $0203, $0403, $0503, $0603,
    $0804, $0805, $0806, $0809, $080A, $080B: Result := True;
  else Result := False;
  end;
end;

function TlsVerifySignature(const Leaf: TCert; Scheme: Word; const Data, Sig: TBytes): Boolean;
var h: THashAlg;
begin
  Result := False;
  case Scheme of
    $0201, $0401, $0501, $0601:                       // rsa_pkcs1_*
      begin
        if Leaf.KeyKind <> kkRsa then Exit;
        case Scheme of $0201: h := haSHA1; $0401: h := haSHA256; $0501: h := haSHA384; else h := haSHA512; end;
        Result := RsaPkcs1Verify(Leaf.RsaN, Leaf.RsaE, h, Hash(h, Data), Sig);
      end;
    $0804, $0805, $0806, $0809, $080A, $080B:        // rsa_pss_rsae_* / rsa_pss_pss_*
      begin
        if (Scheme <= $0806) and (Leaf.KeyKind <> kkRsa) then Exit;
        if (Scheme >= $0809) and (Leaf.KeyKind <> kkRsaPss) then Exit;
        case Scheme of $0804, $0809: h := haSHA256; $0805, $080A: h := haSHA384; else h := haSHA512; end;
        Result := RsaPssVerify(Leaf.RsaN, Leaf.RsaE, h, Hash(h, Data), Sig, HashSize(h));
      end;
    $0203, $0403, $0503, $0603:                       // ecdsa_*
      begin
        if (Leaf.KeyKind <> kkEc) or (Leaf.Curve = ecNone) then Exit;
        case Scheme of $0203: h := haSHA1; $0403: h := haSHA256; $0503: h := haSHA384; else h := haSHA512; end;
        Result := EcdsaVerify(Leaf.Curve, Leaf.PubKey, Hash(h, Data), Sig);
      end;
  end;
end;

// ================= names =================

function ParseIp(const S: string; out Ip: TBytes): Boolean;
var parts: TStringArray; i, v, n, dbl, k: Integer; groups: array of Word; t: string;
begin
  Result := False; Ip := nil;
  if Pos(':', S) = 0 then
  begin
    parts := S.Split(['.']);
    if Length(parts) <> 4 then Exit;
    SetLength(Ip, 4);
    for i := 0 to 3 do
    begin
      v := StrToIntDef(parts[i], -1);
      if (v < 0) or (v > 255) or (parts[i] = '') or (Length(parts[i]) > 3) then Exit;
      Ip[i] := v;
    end;
    Exit(True);
  end;
  // IPv6 (no zones): the part before "::" and after it
  t := S;
  if (Length(t) > 2) and (t[1] = '[') and (t[Length(t)] = ']') then t := Copy(t, 2, Length(t) - 2);
  SetLength(groups, 0); dbl := -1;
  k := Pos('::', t);
  if k > 0 then
  begin
    if PosEx('::', t, k + 1) > 0 then Exit;               // two "::"
    parts := Copy(t, 1, k - 1).Split([':']);
    if Copy(t, 1, k - 1) = '' then parts := nil;
  end
  else parts := t.Split([':']);
  for i := 0 to High(parts) do
  begin
    v := StrToIntDef('$' + parts[i], -1);
    if (parts[i] = '') or (v < 0) or (v > $FFFF) or (Length(parts[i]) > 4) then Exit;
    SetLength(groups, Length(groups) + 1); groups[High(groups)] := v;
  end;
  if k > 0 then
  begin
    dbl := Length(groups);
    t := Copy(t, k + 2, MaxInt);
    if t <> '' then
    begin
      parts := t.Split([':']);
      for i := 0 to High(parts) do
      begin
        v := StrToIntDef('$' + parts[i], -1);
        if (parts[i] = '') or (v < 0) or (v > $FFFF) or (Length(parts[i]) > 4) then Exit;
        SetLength(groups, Length(groups) + 1); groups[High(groups)] := v;
      end;
    end;
  end;
  n := Length(groups);
  if (n > 8) or ((dbl < 0) and (n <> 8)) then Exit;
  SetLength(Ip, 16); FillChar(Ip[0], 16, 0);
  k := 0;
  for i := 0 to n - 1 do
  begin
    if (dbl >= 0) and (i = dbl) then k := 8 - (n - dbl);
    Ip[k * 2] := Hi(groups[i]); Ip[k * 2 + 1] := Lo(groups[i]);
    Inc(k);
  end;
  Result := True;
end;

// RFC 6125: '*' only as the complete, left-most label; at least 2 labels after it
function DnsMatch(const Pattern, Host: string): Boolean;
var p, h, rest: string; dot: Integer;
begin
  p := LowerCase(Pattern); h := LowerCase(Host);
  if (p <> '') and (p[Length(p)] = '.') then Delete(p, Length(p), 1);
  if (h <> '') and (h[Length(h)] = '.') then Delete(h, Length(h), 1);
  if (p = '') or (h = '') then Exit(False);
  if Copy(p, 1, 2) = '*.' then
  begin
    rest := Copy(p, 3, MaxInt);
    if Pos('.', rest) = 0 then Exit(False);          // *.com - too broad
    if Pos('*', rest) > 0 then Exit(False);
    dot := Pos('.', h);
    if dot <= 1 then Exit(False);
    Result := Copy(h, dot + 1, MaxInt) = rest;
  end
  else
    Result := (Pos('*', p) = 0) and (p = h);
end;

function HostMatches(const C: TCert; const Host: string): Boolean;
var ip: TBytes; i: Integer;
begin
  Result := False;
  if ParseIp(Host, ip) then
  begin
    for i := 0 to High(C.IpAddrs) do
      if SameBytesCT(C.IpAddrs[i], ip) then Exit(True);
    Exit;
  end;
  for i := 0 to High(C.DnsNames) do
    if DnsMatch(C.DnsNames[i], Host) then Exit(True);
end;

// nameConstraints: dNSName - name within the subtree (equal to or ending with .base)
function DnsInSubtree(const Name, Base: string): Boolean;
var n, b: string;
begin
  n := LowerCase(Name); b := LowerCase(Base);
  if b = '' then Exit(True);
  if b[1] = '.' then Delete(b, 1, 1);
  if n = b then Exit(True);
  Result := (Length(n) > Length(b)) and (Copy(n, Length(n) - Length(b), MaxInt) = '.' + b);
end;

function IpInSubtree(const Ip, BaseMask: TBytes): Boolean;
var i, l: Integer;
begin
  l := Length(Ip);
  if Length(BaseMask) <> 2 * l then Exit(False);
  for i := 0 to l - 1 do
    if (Ip[i] and BaseMask[l + i]) <> (BaseMask[i] and BaseMask[l + i]) then Exit(False);
  Result := True;
end;

// Name (SEQUENCE) starts with the base's RDNs (byte-wise)
function DirInSubtree(const SubjectRaw, BaseContent: TBytes): Boolean;
var s, bo, bi: TDer; n: Integer;
begin
  Result := False;
  // BaseContent = content of [4] = SEQUENCE Name; compare the RDNSequence contents
  if not DerRead(BaseContent, 0, Length(BaseContent), bo) or (bo.Tag <> $30) then Exit;
  if not DerRead(SubjectRaw, 0, Length(SubjectRaw), s) or (s.Tag <> $30) then Exit;
  n := bo.Len;
  if n = 0 then Exit(True);
  if n > s.Len then Exit;
  Result := CompareMem(@BaseContent[bo.Start], @SubjectRaw[s.Start], n);
  if Result and (n < s.Len) then   // the boundary must fall on an RDN boundary
    Result := DerRead(SubjectRaw, s.Start + n, s.Next, bi);
end;

function NamesAllowed(const CA, C: TCert; IsLeaf: Boolean): Boolean;
var i, j: Integer; ok: Boolean; names: TStringArray;
begin
  Result := True;
  if not CA.HasNC then Exit;
  // directoryName applies to the subject of every certificate below (empty subjects skipped)
  if Length(C.SubjectRaw) > 2 then
  begin
    for j := 0 to High(CA.ExclDir) do
      if DirInSubtree(C.SubjectRaw, CA.ExclDir[j]) then Exit(False);
    if Length(CA.PermDir) > 0 then
    begin
      ok := False;
      for j := 0 to High(CA.PermDir) do if DirInSubtree(C.SubjectRaw, CA.PermDir[j]) then ok := True;
      if not ok then Exit(False);
    end;
  end;
  if not IsLeaf then Exit;
  names := C.DnsNames;
  for i := 0 to High(names) do
  begin
    for j := 0 to High(CA.ExclDns) do
      if DnsInSubtree(names[i], CA.ExclDns[j]) then Exit(False);
    if Length(CA.PermDns) > 0 then
    begin
      ok := False;
      for j := 0 to High(CA.PermDns) do if DnsInSubtree(names[i], CA.PermDns[j]) then ok := True;
      if not ok then Exit(False);
    end;
  end;
  for i := 0 to High(C.IpAddrs) do
  begin
    for j := 0 to High(CA.ExclIp) do
      if IpInSubtree(C.IpAddrs[i], CA.ExclIp[j]) then Exit(False);
    ok := Length(CA.PermIp) = 0;
    for j := 0 to High(CA.PermIp) do if IpInSubtree(C.IpAddrs[i], CA.PermIp[j]) then ok := True;
    // no IP constraint for this family (v4/v6) while others exist = allowed only if none has this length
    if not ok then
    begin
      ok := True;
      for j := 0 to High(CA.PermIp) do if Length(CA.PermIp[j]) = 2 * Length(C.IpAddrs[i]) then ok := False;
      if not ok then Exit(False);
    end;
  end;
end;

// ================= path =================

function NowUtc: TDateTime;
begin
  Result := LocalTimeToUniversal(Now);
end;

function TimeOk(const C: TCert; T: TDateTime): Boolean;
begin
  Result := (T >= C.NotBefore) and (T <= C.NotAfter);
end;

function CaUsable(const C: TCert): Boolean;
begin
  Result := (C.Version >= 3) and C.HasBC and C.IsCA and not C.UnknownCritical;
  if Result and C.HasKU then Result := (C.KeyUsage and (1 shl 5)) <> 0;   // keyCertSign
  if Result and C.HasEKU then Result := C.EkuServerAuth;
end;

function VerifyChain(const Chain: array of TBytes; const Host: string;
  const Anchors, Pool: TCertArray; NowUtc: TDateTime; out Err: string): TVerifyResult;
var
  certs: TCertArray;
  path: array of Integer;        // indexes into cands; path[0] = leaf
  cands: TCertArray;             // [0] leaf, then the server's intermediates, then the pool
  i, nCands: Integer;
  best: TVerifyResult;

  procedure Note(R: TVerifyResult; const Msg: string);
  begin
    // keep the first specific error (other than "unknown issuer")
    if (best = vrUnknownCA) and (R <> vrUnknownCA) then begin best := R; Err := Msg; end;
  end;

  // constraints on the found path: pathLen and nameConstraints (including the anchor)
  function PathConstraintsOk(const Anchor: TCert): Boolean;
  var k, m, below: Integer;
  begin
    Result := False;
    // pathLen: number of intermediates (excluding the leaf) below the given CA
    for k := 1 to High(path) do
    begin
      below := k - 1;
      if (cands[path[k]].PathLen >= 0) and (below > cands[path[k]].PathLen) then
      begin Note(vrBadUsage, 'pathLenConstraint exceeded'); Exit; end;
    end;
    if (Anchor.PathLen >= 0) and (Length(path) - 1 > Anchor.PathLen) and Anchor.HasBC then
    begin Note(vrBadUsage, 'root pathLenConstraint exceeded'); Exit; end;
    // nameConstraints: every CA constrains all certificates below it
    for k := 1 to High(path) do
      for m := 0 to k - 1 do
        if not NamesAllowed(cands[path[k]], cands[path[m]], m = 0) then
        begin Note(vrBadUsage, 'nameConstraints violation'); Exit; end;
    for m := 0 to High(path) do
      if not NamesAllowed(Anchor, cands[path[m]], m = 0) then
      begin Note(vrBadUsage, 'root nameConstraints violation'); Exit; end;
    Result := True;
  end;

  function Search(Depth: Integer): Boolean;
  var cur: TCert; a, k, j: Integer; used: Boolean;
  begin
    Result := False;
    cur := cands[path[High(path)]];
    // 1) is the current certificate directly trusted or signed by an anchor
    for a := 0 to High(Anchors) do
    begin
      if SameBytesCT(cur.Raw, Anchors[a].Raw) then
      begin
        if PathConstraintsOk(Default(TCert)) then Exit(True);
        Continue;
      end;
      if SameBytesCT(cur.IssuerRaw, Anchors[a].SubjectRaw) then
      begin
        if VerifyWithKey(Anchors[a], cur.SigAlg, cur.SigParams, cur.Tbs, cur.Signature) then
        begin
          if PathConstraintsOk(Anchors[a]) then Exit(True);
        end
        else Note(vrBadSignature, 'invalid signature on certificate "' + cur.SubjectCN + '"');
      end;
    end;
    if Depth >= 8 then Exit;
    // 2) intermediates: from the server and from the pool
    for k := 1 to nCands - 1 do
    begin
      used := False;
      for j := 0 to High(path) do if path[j] = k then used := True;
      if used or not SameBytesCT(cur.IssuerRaw, cands[k].SubjectRaw) then Continue;
      if not CaUsable(cands[k]) then begin Note(vrBadUsage, 'intermediate "' + cands[k].SubjectCN + '" is not a CA usable for TLS'); Continue; end;
      if not TimeOk(cands[k], NowUtc) then begin Note(vrExpired, 'intermediate "' + cands[k].SubjectCN + '" is expired or not yet valid'); Continue; end;
      if not VerifyWithKey(cands[k], cur.SigAlg, cur.SigParams, cur.Tbs, cur.Signature) then
      begin Note(vrBadSignature, 'invalid signature on "' + cur.SubjectCN + '"'); Continue; end;
      SetLength(path, Length(path) + 1);
      path[High(path)] := k;
      if Search(Depth + 1) then Exit(True);
      SetLength(path, Length(path) - 1);
    end;
  end;

begin
  Err := '';
  best := vrUnknownCA;
  if Length(Chain) = 0 then begin Err := 'missing certificate'; Exit(vrBadCert); end;
  SetLength(certs, Length(Chain));
  for i := 0 to High(Chain) do
    if not ParseCert(Chain[i], certs[i]) then
    begin
      if i = 0 then begin Err := 'cannot parse the server certificate'; Exit(vrBadCert); end;
      certs[i].Raw := nil;           // broken intermediate - skipped
    end;
  // leaf
  if certs[0].UnknownCritical then begin Err := 'unknown critical extension'; Exit(vrBadCert); end;
  if not TimeOk(certs[0], NowUtc) then
  begin Err := 'the server certificate is expired or not yet valid'; Exit(vrExpired); end;
  if certs[0].HasEKU and not certs[0].EkuServerAuth then
  begin Err := 'the certificate is not intended for a TLS server (EKU)'; Exit(vrBadUsage); end;
  if certs[0].HasKU and ((certs[0].KeyUsage and 1) = 0) then
  begin Err := 'keyUsage without digitalSignature'; Exit(vrBadUsage); end;
  if (Host <> '') and not HostMatches(certs[0], Host) then
  begin Err := 'host name "' + Host + '" does not match the certificate'; Exit(vrNameMismatch); end;
  // candidates: leaf, server intermediates, pool
  SetLength(cands, Length(certs) + Length(Pool));
  nCands := 0;
  for i := 0 to High(certs) do
    if Length(certs[i].Raw) > 0 then begin cands[nCands] := certs[i]; Inc(nCands); end;
  for i := 0 to High(Pool) do begin cands[nCands] := Pool[i]; Inc(nCands); end;
  SetLength(path, 1);
  path[0] := 0;
  if Search(0) then begin Err := ''; Exit(vrOk); end;
  Result := best;
  if Err = '' then Err := 'no trusted issuer found for "' + certs[0].IssuerCN + '"';
end;

end.
