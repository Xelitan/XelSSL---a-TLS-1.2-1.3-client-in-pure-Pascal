// Speed of the primitives (MB/s, one core). Each test runs for about 0.5 s.
program t_bench;

{$mode objfpc}{$H+}

uses
  SysUtils, XelSslCpu, XelSslHash, XelSslAes, XelSslChaCha, XelSslX25519, XelSslEcdh;

var
  Buf, Key, Nonce, Outp: TBytes;
  K: TAesKey;
  G: TGcmKey;

type
  TJob = procedure;

// runs Job until 500 ms have passed; Bytes = data processed per call (0 = report ops/s)
procedure Measure(const Name: string; Job: TJob; Bytes: Integer);
var t0, ms: QWord; n: Integer;
begin
  n := 0;
  t0 := GetTickCount64;
  repeat
    Job;
    Inc(n);
    ms := GetTickCount64 - t0;
  until ms >= 500;
  if Bytes > 0 then
    WriteLn(Format('  %-34s %8.0f MB/s', [Name, Int64(n) * Bytes / 1048576 / (ms / 1000)]))
  else
    WriteLn(Format('  %-34s %8.0f ops/s', [Name, n / (ms / 1000)]));
end;

procedure JobAes; begin AesEncryptBlocks(K, @Buf[0], @Outp[0], Length(Buf) div 16); end;
procedure JobGcm; begin Outp := GcmSeal(G, Nonce, nil, Buf); end;
procedure JobGhash; begin Outp := GcmSeal(G, Nonce, Buf, nil); end;
procedure JobChaCha; begin Outp := ChaChaPolySeal(Key, Nonce, nil, Buf); end;
procedure JobChaChaOnly; begin ChaCha20Xor(Key, Nonce, 1, @Buf[0], @Outp[0], Length(Buf)); end;
procedure JobPoly; begin Outp := Poly1305Mac(Key, Buf); end;
procedure JobSha256; begin Outp := Hash(haSHA256, Buf); end;
procedure JobSha384; begin Outp := Hash(haSHA384, Buf); end;
procedure JobSha1; begin Outp := Hash(haSHA1, Buf); end;
procedure JobX25519; begin Outp := X25519Base(Key); end;
procedure JobP256; var a, p: TBytes; begin EcdhKeyPair(ecdhP256, a, p); end;
procedure JobP384; var a, p: TBytes; begin EcdhKeyPair(ecdhP384, a, p); end;

var hw: Boolean;
begin
  // "pascal": no assembler additions at all
  if ParamStr(1) = 'pascal' then XelSslAsm := False;
  WriteLn('assembler additions: ', XelSslAsm and (CpuFeatures <> []));
  SetLength(Buf, 1024 * 1024);
  FillChar(Buf[0], Length(Buf), 7);
  SetLength(Outp, Length(Buf));
  Key := FromHex('000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f');
  Nonce := FromHex('000000000000000000000001');
  for hw in [True, False] do
  begin
    if hw and not AesHardwareAvailable then Continue;
    AesUseHardware := hw;
    if hw then WriteLn('CPU instructions (AES-NI, PCLMULQDQ):') else WriteLn('portable code:');
    AesSetKey(K, Copy(Key, 0, 16));
    GcmSetKey(G, Copy(Key, 0, 16));
    Measure('AES-128 blocks', @JobAes, Length(Buf));
    Measure('GHASH only (AAD)', @JobGhash, Length(Buf));
    Measure('AES-128-GCM seal', @JobGcm, Length(Buf));
  end;
  AesUseHardware := AesHardwareAvailable;
  WriteLn('other:');
  Measure('ChaCha20-Poly1305 seal', @JobChaCha, Length(Buf));
  Measure('ChaCha20 only', @JobChaChaOnly, Length(Buf));
  Measure('Poly1305 only', @JobPoly, Length(Buf));
  Measure('SHA-256', @JobSha256, Length(Buf));
  Measure('SHA-384', @JobSha384, Length(Buf));
  Measure('SHA-1', @JobSha1, Length(Buf));
  Measure('X25519 key pair', @JobX25519, 0);
  Measure('P-256 key pair', @JobP256, 0);
  Measure('P-384 key pair', @JobP384, 0);
end.
