// XelSSL primitive tests: RFC / FIPS / NIST vectors + vectors computed with the Python
// "cryptography" package (gen_prim.py -> out/prim_vectors.txt) and OpenSSL (gen_ecdh.py).
// AES and GCM run with the CPU instructions and with the portable code.
program t_prim;

{$mode objfpc}{$H+}

uses
  SysUtils, Classes, XelSslCpu, XelSslFe25519, XelSslHash, XelSslAes, XelSslChaCha, XelSslX25519, XelSslEcdh, XelSslBigNum;

var
  Fails, Checks: Integer;
  HwAvail: Boolean;

procedure Check(const Name: string; Ok: Boolean);
begin
  Inc(Checks);
  if not Ok then begin Inc(Fails); if Fails < 30 then WriteLn('FAIL: ', Name); end;
end;

procedure CheckHex(const Name: string; const Got: TBytes; const Exp: string);
begin
  Inc(Checks);
  if ToHex(Got) <> LowerCase(Exp) then
  begin
    Inc(Fails);
    WriteLn('FAIL: ', Name); WriteLn('  got ', ToHex(Got)); WriteLn('  exp ', LowerCase(Exp));
  end;
end;

function Rnd(N: Integer): TBytes;
var i: Integer;
begin
  SetLength(Result, N);
  for i := 0 to N - 1 do Result[i] := Random(256);
end;

function AlgOf(const S: string): THashAlg;
begin
  if S = 'sha1' then Result := haSHA1
  else if S = 'sha256' then Result := haSHA256
  else if S = 'sha384' then Result := haSHA384
  else Result := haSHA512;
end;

function AesEcb(const Key, Plain: TBytes): TBytes;
var K: TAesKey;
begin
  AesSetKey(K, Key);
  SetLength(Result, Length(Plain));
  if Length(Plain) > 0 then AesEncryptBlocks(K, @Plain[0], @Result[0], Length(Plain) div 16);
end;

function Gcm(const Key, Nonce, AAD, Plain: TBytes): TBytes;
var G: TGcmKey;
begin
  GcmSetKey(G, Key);
  Result := GcmSeal(G, Nonce, AAD, Plain);
end;

// runs P with the assembler additions (if the CPU has them) and with the Pascal code
procedure BothPaths(const Name: string; P: TProcedure);
begin
  if CpuFeatures <> [] then
  begin
    XelSslAsm := True;
    WriteLn('  ', Name, ': assembler additions');
    P;
  end;
  XelSslAsm := False;
  WriteLn('  ', Name, ': Pascal');
  P;
  XelSslAsm := True;
end;

// ---- fixed vectors ----

procedure TestFixedAes;
begin
  // FIPS-197 appendix C
  CheckHex('aes-128 fips197', AesEcb(FromHex('000102030405060708090a0b0c0d0e0f'),
    FromHex('00112233445566778899aabbccddeeff')), '69c4e0d86a7b0430d8cdb78070b4c55a');
  CheckHex('aes-192 fips197', AesEcb(FromHex('000102030405060708090a0b0c0d0e0f1011121314151617'),
    FromHex('00112233445566778899aabbccddeeff')), 'dda97ca4864cdfe06eaf70a0ec0d7191');
  CheckHex('aes-256 fips197', AesEcb(FromHex('000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f'),
    FromHex('00112233445566778899aabbccddeeff')), '8ea2b7ca516745bfeafc49904b496089');
  // GCM spec (McGrew/Viega) test cases 1, 2, 4 and 16
  CheckHex('gcm tc1', Gcm(FromHex('00000000000000000000000000000000'), FromHex('000000000000000000000000'), nil, nil),
    '58e2fccefa7e3061367f1d57a4e7455a');
  CheckHex('gcm tc2', Gcm(FromHex('00000000000000000000000000000000'), FromHex('000000000000000000000000'), nil,
    FromHex('00000000000000000000000000000000')), '0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf');
  CheckHex('gcm tc4', Gcm(FromHex('feffe9928665731c6d6a8f9467308308'), FromHex('cafebabefacedbaddecaf888'),
    FromHex('feedfacedeadbeeffeedfacedeadbeefabaddad2'),
    FromHex('d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39')),
    '42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091' +
    '5bc94fbc3221a5db94fae95ae7121a47');
  CheckHex('gcm tc16', Gcm(FromHex('feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308'),
    FromHex('cafebabefacedbaddecaf888'), FromHex('feedfacedeadbeeffeedfacedeadbeefabaddad2'),
    FromHex('d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39')),
    '522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa8cb08e48590dbb3da7b08b1056828838c5f61e6393ba7a0abcc9f662' +
    '76fc6ece0f4e1768cddf8853bb2d551b');
end;

procedure TestFixedOther;
var okm: TBytes;
begin
  CheckHex('sha256 abc', Hash(haSHA256, BytesOf('abc')), 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad');
  CheckHex('sha1 abc', Hash(haSHA1, BytesOf('abc')), 'a9993e364706816aba3e25717850c26c9cd0d89d');
  CheckHex('sha384 abc', Hash(haSHA384, BytesOf('abc')),
    'cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7');
  CheckHex('sha512 abc', Hash(haSHA512, BytesOf('abc')),
    'ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f');
  // RFC 4231 tests 1, 2, 6
  CheckHex('hmac-sha256 t1', Hmac(haSHA256, FromHex('0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b'), BytesOf('Hi There')),
    'b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7');
  CheckHex('hmac-sha512 t2', Hmac(haSHA512, BytesOf('Jefe'), BytesOf('what do ya want for nothing?')),
    '164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737');
  CheckHex('hmac-sha256 t6', Hmac(haSHA256, FromHex(StringOfChar('a', 262)),
    BytesOf('Test Using Larger Than Block-Size Key - Hash Key First')),
    '60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54');
  // RFC 5869 test 1
  okm := HkdfExpand(haSHA256, HkdfExtract(haSHA256, FromHex('000102030405060708090a0b0c'),
    FromHex('0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b')), FromHex('f0f1f2f3f4f5f6f7f8f9'), 42);
  CheckHex('hkdf rfc5869 t1', okm,
    '3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865');
  // RFC 8448 (TLS 1.3 trace)
  CheckHex('tls13 early secret', HkdfExtract(haSHA256, nil, FromHex(StringOfChar('0', 64))),
    '33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a');
  CheckHex('tls13 derived', HkdfExpandLabel(haSHA256,
    FromHex('33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a'), 'derived',
    Hash(haSHA256, nil), 32), '6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba');
  // RFC 8439 2.8.2
  CheckHex('chacha20poly1305 rfc8439', ChaChaPolySeal(
    FromHex('808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f'),
    FromHex('070000004041424344454647'), FromHex('50515253c0c1c2c3c4c5c6c7'),
    BytesOf('Ladies and Gentlemen of the class of ''99: If I could offer you only one tip for the future, sunscreen would be it.')),
    'd31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116' +
    '1ae10b594f09e26a7e902ecbd0600691');
  // RFC 7748 5.2 and 6.1
  CheckHex('x25519 rfc7748 1', X25519(FromHex('a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4'),
    FromHex('e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c')),
    'c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552');
  CheckHex('x25519 alice pub', X25519Base(FromHex('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a')),
    '8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a');
end;

// field elements near p and the iterated X25519 test of RFC 7748 5.2
procedure TestField;
const
  // little-endian values and their canonical form mod p = 2^255 - 19
  Cases: array[0..5, 0..1] of string = (
    ('ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f', 'ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f'),
    ('edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f', '0000000000000000000000000000000000000000000000000000000000000000'),
    ('eeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f', '0100000000000000000000000000000000000000000000000000000000000000'),
    ('ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f', '1200000000000000000000000000000000000000000000000000000000000000'),
    ('ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff', '1200000000000000000000000000000000000000000000000000000000000000'),
    ('0000000000000000000000000000000000000000000000000000000000000080', '0000000000000000000000000000000000000000000000000000000000000000'));
var i: Integer; f, g: TFe; b, k, u, t: TBytes;
begin
  FeSelect;
  SetLength(b, 32);
  for i := 0 to High(Cases) do
  begin
    FeFromBytes(f, @FromHex(Cases[i, 0])[0]);
    FeToBytes(@b[0], f);
    CheckHex('field canonical ' + IntToStr(i), b, Cases[i, 1]);
  end;
  // (p - 1) * (p - 1) = 1, (p - 1) + 1 = 0
  FeFromBytes(f, @FromHex('ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f')[0]);
  FeMul(g, f, f); FeToBytes(@b[0], g);
  CheckHex('field (p-1)^2', b, '0100000000000000000000000000000000000000000000000000000000000000');
  FeOne(g); FeAdd(g, f, g); FeToBytes(@b[0], g);
  CheckHex('field (p-1)+1', b, '0000000000000000000000000000000000000000000000000000000000000000');
  FeSub(g, g, f); FeToBytes(@b[0], g);
  CheckHex('field 0-(p-1)', b, '0100000000000000000000000000000000000000000000000000000000000000');
  // RFC 7748 5.2: k = u = 9, then k, u := X25519(k, u), k
  k := FromHex('0900000000000000000000000000000000000000000000000000000000000000');
  u := Copy(k);
  for i := 1 to 1000 do
  begin
    t := X25519(k, u);
    u := k; k := t;
    if i = 1 then CheckHex('x25519 iterated 1', k, '422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079');
  end;
  CheckHex('x25519 iterated 1000', k, '684cf59ba83309552800ef566f2f4d3c1c3887c49360e3875f2eb94d99532c51');
end;

// ---- vectors from gen_prim.py ----

var
  Vec: TStringList;

procedure TestVectorsAes;
var i: Integer; f: TStringArray; c, back: TBytes; G: TGcmKey; n: Integer;
begin
  n := 0;
  for i := 0 to Vec.Count - 1 do
  begin
    f := Vec[i].Split(['|']);
    if f[0] = 'aes' then
    begin
      CheckHex('aes ' + IntToStr(i), AesEcb(FromHex(f[1]), FromHex(f[2])), f[3]);
      Inc(n);
    end
    else if f[0] = 'gcm' then
    begin
      GcmSetKey(G, FromHex(f[1]));
      c := GcmSeal(G, FromHex(f[2]), FromHex(f[3]), FromHex(f[4]));
      CheckHex('gcm seal ' + IntToStr(i), c, f[5]);
      Check('gcm open ' + IntToStr(i), GcmOpen(G, FromHex(f[2]), FromHex(f[3]), c, back) and (ToHex(back) = f[4]));
      c[Random(Length(c))] := c[Random(Length(c))] xor (1 shl Random(8));
      if ToHex(c) <> f[5] then
        Check('gcm rejects a modified message ' + IntToStr(i), not GcmOpen(G, FromHex(f[2]), FromHex(f[3]), c, back));
      Inc(n);
    end;
  end;
  WriteLn('    ', n, ' AES / GCM vectors');
end;

procedure TestVectorsOther;
var i: Integer; f: TStringArray; c, back: TBytes; ok: Boolean;
begin
  for i := 0 to Vec.Count - 1 do
  begin
    f := Vec[i].Split(['|']);
    if f[0] = 'hash' then CheckHex('hash ' + IntToStr(i), Hash(AlgOf(f[1]), FromHex(f[2])), f[3])
    else if f[0] = 'hmac' then CheckHex('hmac ' + IntToStr(i), Hmac(AlgOf(f[1]), FromHex(f[2]), FromHex(f[3])), f[4])
    else if f[0] = 'hkdf' then
      CheckHex('hkdf ' + IntToStr(i), HkdfExpand(AlgOf(f[1]), HkdfExtract(AlgOf(f[1]), FromHex(f[2]), FromHex(f[3])),
        FromHex(f[4]), StrToInt(f[5])), f[6])
    else if f[0] = 'chacha' then
    begin
      c := ChaChaPolySeal(FromHex(f[1]), FromHex(f[2]), FromHex(f[3]), FromHex(f[4]));
      CheckHex('chacha seal ' + IntToStr(i), c, f[5]);
      ok := ChaChaPolyOpen(FromHex(f[1]), FromHex(f[2]), FromHex(f[3]), c, back);
      Check('chacha open ' + IntToStr(i), ok and (ToHex(back) = f[4]));
    end
    else if f[0] = 'x25519' then CheckHex('x25519 ' + IntToStr(i), X25519(FromHex(f[1]), FromHex(f[2])), f[3]);
  end;
end;

// the two AES/GHASH implementations against each other on random inputs
procedure TestCrossPaths;
var i: Integer; k, n, a, p, c1, c2: TBytes;
begin
  if not HwAvail then Exit;
  for i := 1 to 500 do
  begin
    k := Rnd(16 + 8 * Random(3)); n := Rnd(12); a := Rnd(Random(70)); p := Rnd(Random(300));
    if Length(k) = 24 then k := Rnd(16);       // GCM in TLS: 128/256 (192 covered by the ECB test)
    XelSslAsm := True;  c1 := Gcm(k, n, a, p);
    XelSslAsm := False; c2 := Gcm(k, n, a, p);
    Check('hw = portable ' + IntToStr(i), SameBytesCT(c1, c2));
    XelSslAsm := True;  c1 := ChaChaPolySeal(Rnd(32), n, a, p);
    k := Rnd(32);
    c1 := ChaChaPolySeal(k, n, a, p);
    XelSslAsm := False; c2 := ChaChaPolySeal(k, n, a, p);
    Check('chacha asm = pascal ' + IntToStr(i), SameBytesCT(c1, c2));
  end;
  XelSslAsm := True;
end;

// GCM kernels (4-block, 8-block AVX, 16-block VAES) against the Pascal code: all key
// sizes, lengths around the group sizes, in-place open, and a failed open must leave
// the data unchanged
procedure TestGcmLevels;
var i, lvl, len: Integer; k, n, a, p, ref, c, d: TBytes; G: TGcmKey; tag: array[0..15] of Byte; pa: PByte;
begin
  if not HwAvail then Exit;
  for i := 1 to 300 do
  begin
    k := Rnd(16 + 8 * Random(3)); n := Rnd(12); a := Rnd(Random(3) * Random(40));
    case Random(4) of
      0: len := Random(5000);
      1: len := 128 * (1 + Random(20)) + Random(3) - 1;
      2: len := 256 * (1 + Random(10)) + Random(33) - 16;
    else len := Random(300);
    end;
    if len < 0 then len := 0;
    p := Rnd(len);
    GcmSetKey(G, k);
    XelSslAsm := False;
    ref := GcmSeal(G, n, a, p);
    XelSslAsm := True;
    for lvl := 0 to 2 do
    begin
      GcmAsmLevel := lvl;
      c := GcmSeal(G, n, a, p);
      Check(Format('gcm level %d = Pascal (key %d, len %d)', [lvl, Length(k), len]), SameBytesCT(c, ref));
      // in place: open, then a modified tag must fail and leave the plaintext... ciphertext unchanged
      d := Copy(c, 0, len + 1);
      if Length(a) > 0 then pa := @a[0] else pa := nil;
      Move(c[len], tag[0], 16);
      Check(Format('gcm level %d open in place', [lvl]),
        GcmOpenP(G, @n[0], pa, Length(a), @d[0], len, @tag[0]) and (CompareByte(d[0], p[0], len) = 0));
      d := Copy(c, 0, len + 1);
      tag[Random(16)] := tag[Random(16)] xor (1 shl Random(8));
      if CompareByte(tag[0], c[len], 16) <> 0 then
        Check(Format('gcm level %d failed open leaves data unchanged', [lvl]),
          not GcmOpenP(G, @n[0], pa, Length(a), @d[0], len, @tag[0]) and (CompareByte(d[0], c[0], len) = 0));
    end;
  end;
  GcmAsmLevel := 2;
end;

// the 8-block ChaCha20 kernel against the 4-block one and Pascal: lengths around
// 512-byte steps, counters near 2^32 (the 32-bit counter wraps)
procedure TestChaChaWide;
var i, len: Integer; k, n, p, c1, c2, c3: TBytes; ctr: UInt32;
begin
  if not AsmAvailable([cfAvx2]) then Exit;
  for i := 1 to 300 do
  begin
    k := Rnd(32); n := Rnd(12);
    if Random(2) = 0 then len := 512 * (1 + Random(8)) + Random(129) - 64 else len := Random(6000);
    if len < 0 then len := 0;
    p := Rnd(len + 1);
    if Random(4) = 0 then ctr := UInt32($FFFFFFFF) - UInt32(Random(20)) else ctr := 1 + UInt32(Random(1000));
    SetLength(c1, len + 1); SetLength(c2, len + 1); SetLength(c3, len + 1);
    ChaChaWide := True;  ChaCha20Xor(k, n, ctr, @p[0], @c1[0], len);
    ChaChaWide := False; ChaCha20Xor(k, n, ctr, @p[0], @c2[0], len);
    XelSslAsm := False;  ChaCha20Xor(k, n, ctr, @p[0], @c3[0], len);
    XelSslAsm := True;   ChaChaWide := True;
    Check(Format('chacha 8-block = 4-block = Pascal (len %d, ctr %u)', [len, ctr]),
      (CompareByte(c1[0], c2[0], len) = 0) and (CompareByte(c1[0], c3[0], len) = 0));
  end;
end;

// the AVX2 Poly1305 against the one-block code: lengths around 64-byte groups, and
// messages of all-ones bytes (the largest limbs)
procedure TestPolyWide;
var i, len: Integer; k, m, t1, t2: TBytes;
begin
  if not AsmAvailable([cfAvx2]) then Exit;
  for i := 1 to 400 do
  begin
    k := Rnd(32);
    if Random(2) = 0 then len := 64 * (2 + Random(40)) + Random(33) - 16 else len := Random(3000);
    if len < 0 then len := 0;
    m := Rnd(len);
    if Random(5) = 0 then
    begin
      if len > 0 then FillChar(m[0], len, $FF);
      FillChar(k[0], 16, $FF);                  // r gets the largest clamped value
    end;
    PolyWide := True;  t1 := Poly1305Mac(k, m);
    PolyWide := False; t2 := Poly1305Mac(k, m);
    PolyWide := True;
    Check(Format('poly1305 AVX2 = one block (len %d)', [len]), SameBytesCT(t1, t2));
  end;
end;

// X25519 on 4 x 64-bit limbs (BMI2 + ADX) against the Pascal code: random inputs,
// u >= p (non-canonical) and u with the top bit set
// X25519Base through the Edwards table against the ladder (k * 9)
procedure TestX25519Base;
var i: Integer; k, nine, r1, r2: TBytes;
begin
  if not AsmAvailable([cfBmi2, cfAdx]) then Exit;
  SetLength(nine, 32); FillChar(nine[0], 32, 0); nine[0] := 9;
  for i := 1 to 500 do
  begin
    k := Rnd(32);
    if i mod 50 = 0 then FillChar(k[0], 32, $FF);
    if i mod 50 = 1 then FillChar(k[0], 32, 0);
    r1 := X25519Base(k);
    r2 := X25519(k, nine);
    Check('x25519 fixed base = ladder ' + IntToStr(i), SameBytesCT(r1, r2));
  end;
end;

procedure TestX25519Fast;
var i: Integer; k, u, r1, r2: TBytes;
begin
  if not AsmAvailable([cfBmi2, cfAdx]) then Exit;
  for i := 1 to 500 do
  begin
    k := Rnd(32); u := Rnd(32);
    case i mod 5 of
      0: begin FillChar(u[0], 32, $FF); u[0] := $EC + Random(19); end;   // 2^256 - 20 + ..: u >= p after masking
      1: u[31] := u[31] or $80;
      2: begin FillChar(u[0], 32, 0); u[0] := Random(3); end;           // tiny / zero
    end;
    XelSslAsm := True;  r1 := X25519(k, u);
    XelSslAsm := False; r2 := X25519(k, u);
    XelSslAsm := True;
    Check('x25519 fast = Pascal ' + IntToStr(i), SameBytesCT(r1, r2));
    X25519WholeLadder := False; r2 := X25519(k, u); X25519WholeLadder := True;
    Check('x25519 asm ladder = Pascal ladder ' + IntToStr(i), SameBytesCT(r1, r2));
  end;
end;

// SHA-384/512: the two-block kernel against the one-block kernel and Pascal, in one
// call and in uneven pieces
procedure TestSha512Pairs;
var i, len, pos, n: Integer; m, h1, h2, h3: TBytes; alg: THashAlg; c: TXHash;
begin
  if not AsmAvailable([cfAvx2, cfBmi2]) then Exit;
  for i := 1 to 300 do
  begin
    if Odd(i) then alg := haSHA512 else alg := haSHA384;
    len := Random(5000);
    m := Rnd(len);
    HashSha512Pairs := True;  h1 := Hash(alg, m);
    HashSha512Pairs := False; h2 := Hash(alg, m);
    HashSha512Pairs := True;
    XelSslAsm := False; h3 := Hash(alg, m); XelSslAsm := True;
    Check(Format('sha512 pairs = single = Pascal (len %d)', [len]), SameBytesCT(h1, h2) and SameBytesCT(h1, h3));
    HashInit(c, alg);
    pos := 0;
    while pos < len do
    begin
      n := 1 + Random(700);
      if pos + n > len then n := len - pos;
      HashUpdate(c, @m[pos], n);
      Inc(pos, n);
    end;
    Check(Format('sha512 pairs in pieces (len %d)', [len]), SameBytesCT(HashFinal(c), h3));
  end;
end;

procedure Bench;
var G: TGcmKey; p, c: TBytes; t0: QWord; ms: QWord; hw: Boolean;
begin
  p := Rnd(4 * 1024 * 1024);
  for hw in [True, False] do
  begin
    if hw and not HwAvail then Continue;
    AesUseHardware := hw;
    GcmSetKey(G, Rnd(16));
    t0 := GetTickCount64;
    c := GcmSeal(G, Rnd(12), nil, p);
    ms := GetTickCount64 - t0; if ms = 0 then ms := 1;
    if hw then Write('  AES-128-GCM, CPU instructions: ') else Write('  AES-128-GCM, portable code:    ');
    WriteLn(Format('%.0f MB/s', [4 / (ms / 1000)]));
  end;
  t0 := GetTickCount64;
  c := ChaChaPolySeal(Rnd(32), Rnd(12), nil, p);
  ms := GetTickCount64 - t0; if ms = 0 then ms := 1;
  WriteLn(Format('  ChaCha20-Poly1305:              %.0f MB/s', [4 / (ms / 1000)]));
  t0 := GetTickCount64;
  c := Hash(haSHA256, p);
  ms := GetTickCount64 - t0; if ms = 0 then ms := 1;
  WriteLn(Format('  SHA-256:                        %.0f MB/s', [4 / (ms / 1000)]));
  AesUseHardware := HwAvail;
end;

// the P-256 fast path (x86-64) against the generic code: public keys and shared secrets.
// Scalars right below n are checked by symmetry and (n - 1)*G = -G only: the generic
// ladder meets the point at infinity there (probability ~2^-250 for real keys).
procedure TestP256Fast;
var i: Integer; a, pa, b, pb, s1, s2, f1, f2, n: TBytes; edge: Boolean;
begin
  if not AsmAvailable([cfSse2]) then Exit;
  n := EcdhOrder(ecdhP256);
  for i := 1 to 200 do
  begin
    EcdhKeyPair(ecdhP256, a, pa);
    EcdhKeyPair(ecdhP256, b, pb);
    edge := (i mod 20 = 0) or (i mod 20 = 10);
    if i mod 20 = 0 then
    begin
      a := Copy(n);                                   // n - 1 - small
      a[31] := a[31] - 1 - Random(5);
    end
    else if i mod 20 = 10 then
    begin
      a := Copy(n);                                   // n - 65 .. n - 100: signed digits, near the top
      a[31] := a[31] - 65 - Random(36);
    end
    else if i mod 20 = 1 then
    begin
      SetLength(a, 32); FillChar(a[0], 32, 0);        // just above 2^224
      a[3] := 1; a[31] := Random(256);
    end;
    EcdhUseAsm := True;
    f1 := EcdhPublicOf(ecdhP256, a);
    Check('p256 shared fast', EcdhShared(ecdhP256, a, pb, s1));
    if edge then
    begin
      Check('p256 symmetric near n ' + IntToStr(i), EcdhShared(ecdhP256, b, f1, s2) and SameBytesCT(s1, s2));
      Continue;
    end;
    EcdhUseAsm := False;
    f2 := EcdhPublicOf(ecdhP256, a);
    Check('p256 shared generic', EcdhShared(ecdhP256, a, pb, s2));
    EcdhUseAsm := True;
    Check('p256 public fast = generic ' + IntToStr(i), SameBytesCT(f1, f2));
    P256UseGTab := False; P256AsmLoop := False; f2 := EcdhPublicOf(ecdhP256, a); P256AsmLoop := True;
    Check('p256 asm loop = Pascal loop ' + IntToStr(i), SameBytesCT(f1, f2));
    f2 := EcdhPublicOf(ecdhP256, a); P256UseGTab := True;
    Check('p256 G table = asm loop ' + IntToStr(i), SameBytesCT(f1, f2));
    Check('p256 shared fast = generic ' + IntToStr(i), SameBytesCT(s1, s2));
  end;
  // 2^255, 2^240, 2^255 + 2^240 times G: long runs of zero windows (the table path starts at
  // infinity; scalars below 2^256 - n are refused by the API)
  for i := 0 to 2 do
  begin
    SetLength(a, 32); FillChar(a[0], 32, 0);
    if i <> 1 then a[0] := $80;
    if i <> 0 then a[1] := 1;
    f1 := EcdhPublicOf(ecdhP256, a);
    P256UseGTab := False; f2 := EcdhPublicOf(ecdhP256, a); P256UseGTab := True;
    Check('p256 G table sparse scalar ' + IntToStr(i), SameBytesCT(f1, f2));
  end;
  // (n - 1) * G = -G = (Gx, p - Gy)
  a := Copy(n); a[31] := a[31] - 1;
  f1 := EcdhPublicOf(ecdhP256, a);
  CheckHex('p256 (n-1)G = -G', f1, '04' +
    '6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296' +
    'B01CBD1C01E58065711814B583F061E9D431CCA994CEA1313449BF97C840AE0A');
  // invalid peer points are rejected
  pb[40] := pb[40] xor 1;
  Check('p256 fast rejects an invalid point', not EcdhShared(ecdhP256, b, pb, s1));
end;

// P-256 verification u1*G + u2*Q: the table path against the Shamir loop; the expected x
// from ((u1 + u2*q) mod n) * G. Edges: u1 = 0, 1, n - 1; u2 = 1, n - 65 (table path),
// n - 1 (beyond the signed windows: the Shamir loop); a sum at infinity.
procedure TestP256Verify;
var
  i: Integer; q, pq, u1, u2, r, r1, x: TBytes; n, k: TBig; nb: TBytes; atInf: Boolean;
  procedure Run(const Name: string);
  begin
    if atInf then
    begin
      P256UseGTab := True;  Check(Name + ' infinity table', not EcVerifyCombination(ecdhP256, pq, u1, u2, r));
      P256UseGTab := False; Check(Name + ' infinity shamir', not EcVerifyCombination(ecdhP256, pq, u1, u2, r));
      P256UseGTab := True;
      Exit;
    end;
    P256UseGTab := True;  Check(Name + ' table', EcVerifyCombination(ecdhP256, pq, u1, u2, r));
    Check(Name + ' table wrong r', not EcVerifyCombination(ecdhP256, pq, u1, u2, r1));
    P256UseGTab := False; Check(Name + ' shamir', EcVerifyCombination(ecdhP256, pq, u1, u2, r));
    P256UseGTab := True;
  end;
  function Near(const B: TBytes; D: Integer): TBytes;
  begin
    Result := BigToBytes(BigSub(BigFromBytes(B), BigFromInt(D)), 32);
  end;
begin
  if not AsmAvailable([cfSse2]) then Exit;
  nb := EcdhOrder(ecdhP256); n := BigFromBytes(nb);
  for i := 1 to 300 do
  begin
    EcdhKeyPair(ecdhP256, q, pq);
    EcdhKeyPair(ecdhP256, u1, x);
    EcdhKeyPair(ecdhP256, u2, x);
    case i mod 12 of
      1: u1 := BigToBytes(BigFromInt(0), 32);
      2: u1 := BigToBytes(BigFromInt(1), 32);
      3: u1 := Near(nb, 1);
      4: u2 := BigToBytes(BigFromInt(1), 32);
      5: u2 := Near(nb, 65 + Random(30));
      6: u2 := Near(nb, 1 + Random(64));
      7: begin u1 := Near(nb, 1 + Random(16)); u2 := Near(nb, 66); end;
    end;
    k := BigMod(BigAdd(BigFromBytes(u1), BigMul(BigFromBytes(u2), BigFromBytes(q))), n);
    atInf := i mod 12 = 8;
    if atInf then
    begin
      // u1 = -u2*q: the sum is the point at infinity
      u1 := BigToBytes(BigMod(BigSub(n, BigMod(BigMul(BigFromBytes(u2), BigFromBytes(q)), n)), n), 32);
      r := BigToBytes(BigFromInt(1), 32);
    end
    else
    begin
      if BigIsZero(k) then Continue;
      x := Copy(EcdhPublicOf(ecdhP256, BigToBytes(k, 32)), 1, 32);
      r := BigToBytes(BigMod(BigFromBytes(x), n), 32);
      r1 := BigToBytes(BigMod(BigAdd(BigFromBytes(x), BigFromInt(1)), n), 32);
    end;
    Run('p256 verify ' + IntToStr(i));
  end;
end;

procedure TestEcdhVectors;
var L: TStringList; f: TStringArray; i: Integer; cv: TEcdhCurve; sec, a, pa, b, pb, s1, s2: TBytes;
begin
  L := TStringList.Create;
  L.LoadFromFile(ExtractFilePath(ParamStr(0)) + 'ecdh_vectors.txt');
  for i := 0 to L.Count - 1 do
  begin
    if L[i] = '' then Continue;
    f := L[i].Split(['|']);
    if f[0] = 'P-256' then cv := ecdhP256 else if f[0] = 'P-384' then cv := ecdhP384 else cv := ecdhP521;
    CheckHex('ecdh pub ' + f[0], EcdhPublicOf(cv, FromHex(f[1])), f[2]);
    Check('ecdh shared ' + f[0], EcdhShared(cv, FromHex(f[1]), FromHex(f[3]), sec));
    CheckHex('ecdh shared val ' + f[0], sec, f[4]);
  end;
  L.Free;
  for cv := Low(TEcdhCurve) to High(TEcdhCurve) do
  begin
    EcdhKeyPair(cv, a, pa); EcdhKeyPair(cv, b, pb);
    Check('ecdh rnd ab', EcdhShared(cv, a, pb, s1) and EcdhShared(cv, b, pa, s2) and SameBytesCT(s1, s2));
    pb[High(pb)] := pb[High(pb)] xor 1;
    Check('ecdh rejects invalid point', not EcdhShared(cv, a, pb, s1));
  end;
end;

var t0: QWord;
begin
  // XELSSL_TEST_NOMULX=1: the P-256 multiplication without MULX/ADX
  if GetEnvironmentVariable('XELSSL_TEST_NOMULX') = '1' then EcdhUseMulx := False;
  RandSeed := 12345;
  Fails := 0; Checks := 0;
  HwAvail := AesHardwareAvailable;
  WriteLn('AES-NI + PCLMULQDQ: ', HwAvail);
  t0 := GetTickCount64;
  Vec := TStringList.Create;
  Vec.LoadFromFile(ExtractFilePath(ParamStr(0)) + 'prim_vectors.txt');
  BothPaths('fixed AES/GCM vectors', @TestFixedAes);
  BothPaths('AES/GCM vectors from Python', @TestVectorsAes);
  if HwAvail then
  begin
    WriteLn('  AES/GCM vectors from Python: GCM level 1 (8 blocks, AVX)');
    GcmAsmLevel := 1; TestVectorsAes;
    WriteLn('  AES/GCM vectors from Python: GCM level 0 (4 blocks)');
    GcmAsmLevel := 0; TestVectorsAes;
    GcmAsmLevel := 2;
  end;
  TestGcmLevels;
  if AsmAvailable([cfAvx2]) then
  begin
    WriteLn('  ChaCha vectors from Python: 4-block AVX2 only');
    ChaChaWide := False; TestVectorsOther; ChaChaWide := True;
  end;
  TestChaChaWide;
  if AsmAvailable([cfAvx2]) then
  begin
    WriteLn('  ChaCha/Poly1305 vectors from Python: Poly1305 one block at a time');
    PolyWide := False; TestVectorsOther; PolyWide := True;
  end;
  TestPolyWide;
  BothPaths('RFC vectors', @TestFixedOther);
  BothPaths('field + RFC 7748 iterations', @TestField);
  BothPaths('hash/HMAC/HKDF/ChaCha/X25519 vectors from Python', @TestVectorsOther);
  TestCrossPaths;
  BothPaths('ECDH', @TestEcdhVectors);
  TestP256Fast;
  TestP256Verify;
  TestX25519Fast;
  TestX25519Base;
  TestSha512Pairs;
  Vec.Free;
  WriteLn(Format('primitives: %d checks, %d failures (%d ms)', [Checks, Fails, GetTickCount64 - t0]));
  Bench;
  if Fails > 0 then Halt(1);
end.
