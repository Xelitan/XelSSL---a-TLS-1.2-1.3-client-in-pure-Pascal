// Validation of real chains (xelssl2/test/out/chains/*.pem, from gen_chains.py).
program t_x509;

{$mode objfpc}{$H+}

uses
  SysUtils, Classes, XelSslHash, XelSslX509, XelSslTrust;

const
  RNames: array[TVerifyResult] of string = ('OK', 'BadCert', 'Expired', 'UnknownCA',
    'BadSignature', 'NameMismatch', 'BadUsage', 'Unsupported');

var
  sr: TSearchRec; dir, host, err, err2: string; L: TStringList; s: RawByteString;
  chain: TBytesArray; r, r2: TVerifyResult; t0, t1: QWord; c: TCert;
begin
  dir := ExtractFilePath(ParamStr(0)) + 'chains' + PathDelim;
  t0 := GetTickCount64;
  WriteLn(Format('system store: %d anchors, %d intermediates (%d ms)',
    [Length(SystemTrust.Anchors), Length(SystemTrust.Pool), GetTickCount64 - t0]));
  L := TStringList.Create;
  if FindFirst(dir + '*.pem', faAnyFile, sr) = 0 then
  repeat
    L.LoadFromFile(dir + sr.Name);
    s := L.Text;
    chain := PemCertificates(s);
    host := ChangeFileExt(sr.Name, '');
    t1 := GetTickCount64;
    r := VerifyChain(chain, host, SystemTrust.Anchors, SystemTrust.Pool, NowUtc, err);
    r2 := SystemTrust.Verify(chain, host, err2);
    ParseCert(chain[0], c);
    Write(Format('%-32s %-12s', [host, RNames[r]]));
    if r2 <> r then Write(' -> system: ', RNames[r2]);
    if err <> '' then Write('  (', err, ')');
    WriteLn(Format('  [%d ms]', [GetTickCount64 - t1]));
  until FindNext(sr) <> 0;
  FindClose(sr);
  L.Free;
end.
