// Validation rule tests on the hierarchies from gen_pki.py
program t_pki;

{$mode objfpc}{$H+}

uses
  SysUtils, Classes, XelSslHash, XelSslX509, XelSslTrust;

const
  RNames: array[TVerifyResult] of string = ('OK', 'BadCert', 'Expired', 'UnknownCA',
    'BadSignature', 'NameMismatch', 'BadUsage', 'Unsupported');

function LoadPem(const F: string): TBytesArray;
var L: TStringList;
begin
  L := TStringList.Create;
  try L.LoadFromFile(F); Result := PemCertificates(L.Text); finally L.Free; end;
end;

var
  dir, err: string; L: TStringList; f, files: TStringArray; i, j, fails: Integer;
  chain, a: TBytesArray; anchors: TCertArray; r: TVerifyResult;
begin
  dir := ExtractFilePath(ParamStr(0)) + 'pki' + PathDelim;
  L := TStringList.Create;
  L.LoadFromFile(dir + 'cases.txt');
  fails := 0;
  for i := 0 to L.Count - 1 do
  begin
    if L[i] = '' then Continue;
    f := L[i].Split(['|']);
    a := LoadPem(dir + f[3]);
    SetLength(anchors, 1);
    ParseCert(a[0], anchors[0]);
    chain := nil;
    files := f[4].Split([',']);
    for j := 0 to High(files) do
    begin
      a := LoadPem(dir + files[j]);
      SetLength(chain, Length(chain) + 1);
      chain[High(chain)] := a[0];
    end;
    r := VerifyChain(chain, f[1], anchors, nil, NowUtc, err);
    if RNames[r] <> f[2] then
    begin
      Inc(fails);
      WriteLn(Format('FAIL %-26s expected %-12s got %-12s %s', [f[0], f[2], RNames[r], err]));
    end
    else
      WriteLn(Format('ok   %-26s %-12s %s', [f[0], RNames[r], err]));
  end;
  WriteLn(Format('pki: %d cases, %d failures', [L.Count, fails]));
  L.Free;
  if fails > 0 then Halt(1);
end.
