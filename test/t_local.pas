// XelSSL test matrix against a local "openssl s_server" (versions, suites, groups, HRR,
// resumption, client certificate request, ALPN, fragmentation, various certificates).
program t_local;

{$mode objfpc}{$H+}

uses
  SysUtils, Classes, Process, ssockets, XelSslHash, XelSslClient, XelSslTrust;

type
  TTransport = class
    Sock: TInetSocket;
    function DoSend(const Buf; Len: Integer): Integer;
    function DoRecv(var Buf; Len: Integer): Integer;
  end;

function TTransport.DoSend(const Buf; Len: Integer): Integer;
begin try Result := Sock.Write(Buf, Len); except Result := -1; end; end;

function TTransport.DoRecv(var Buf; Len: Integer): Integer;
begin try Result := Sock.Read(Buf, Len); except Result := -1; end; end;

type
  TCase = record
    Name, Args, Cert, Key, Chain, Anchor, Host: string;
    ExpVer, ExpSuite: Word;
    Resume: Boolean;          // the second connection must be resumed
    MaxVer: Word;
  end;

var
  Dir: string;
  Fails, Total: Integer;
  Port: Integer = 44330;

function Connect(const C: TCase; Trust: TTrustStore; Cache: TXelSslSessionCache;
  out Ver, Suite: Word; out Resumed: Boolean; out Info: string): Boolean;
var t: TTransport; cl: TXelSslClient; req: RawByteString; buf: array[0..65535] of Byte; n, total: Integer;
    first: string;
begin
  Result := False; Info := ''; Ver := 0; Suite := 0; Resumed := False;
  t := TTransport.Create;
  cl := nil;
  try
    try t.Sock := TInetSocket.Create('127.0.0.1', Port);
    except on E: Exception do begin Info := 'TCP: ' + E.Message; Exit; end; end;
    cl := TXelSslClient.Create(@t.DoSend, @t.DoRecv);
    cl.Host := C.Host;
    cl.Trust := Trust;
    cl.Cache := Cache;
    cl.CacheKey := C.Host;
    cl.Alpn := ['http/1.1'];
    if C.MaxVer <> 0 then cl.MaxVersion := C.MaxVer;
    if not cl.Handshake then begin Info := cl.LastError; Exit; end;
    Ver := cl.Version; Suite := cl.CipherSuite; Resumed := cl.Resumed;
    req := 'GET / HTTP/1.0'#13#10#13#10;
    cl.Write(req[1], Length(req));
    total := 0; first := '';
    repeat
      n := cl.Read(buf, SizeOf(buf));
      if (n > 0) and (total = 0) then
      begin
        SetString(first, PAnsiChar(@buf[0]), n);
        first := Copy(first, 1, Pos(#13, first + #13) - 1);
      end;
      if n > 0 then Inc(total, n);
    until n <= 0;
    cl.Close;
    Info := Format('%s %s%s alpn=%s %s (%d B)', [TlsVersionName(Ver), TlsSuiteName(Suite),
      BoolToStr(Resumed, ' RESUMED', ''), cl.NegotiatedAlpn, first, total]);
    Result := (total > 0) and (Pos('200', first) > 0);
    if not Result then Info := Info + ' ' + cl.LastError;
  finally
    cl.Free; t.Sock.Free; t.Free;
  end;
end;

procedure RunCase(const C: TCase);
var p: TProcess; trust: TTrustStore; cache: TXelSslSessionCache; ver, suite: Word; res: Boolean;
    info, info2: string; ok: Boolean; args: TStringArray; i: Integer;
begin
  Inc(Port);
  p := TProcess.Create(nil);
  trust := TTrustStore.Create;
  cache := TXelSslSessionCache.Create;
  try
    p.Executable := 'openssl';
    p.Parameters.Add('s_server');
    p.Parameters.Add('-accept'); p.Parameters.Add(IntToStr(Port));
    p.Parameters.Add('-cert'); p.Parameters.Add(Dir + C.Cert);
    p.Parameters.Add('-key'); p.Parameters.Add(Dir + C.Key);
    if C.Chain <> '' then begin p.Parameters.Add('-cert_chain'); p.Parameters.Add(Dir + C.Chain); end;
    p.Parameters.Add('-www'); p.Parameters.Add('-quiet');
    args := C.Args.Split([' ']);
    for i := 0 to High(args) do if args[i] <> '' then p.Parameters.Add(args[i]);
    p.Options := [poNoConsole];
    p.Execute;
    Sleep(400);
    trust.AddFile(Dir + C.Anchor);
    ok := Connect(C, trust, cache, ver, suite, res, info);
    ok := ok and ((C.ExpVer = 0) or (ver = C.ExpVer)) and ((C.ExpSuite = 0) or (suite = C.ExpSuite));
    info2 := '';
    if ok and C.Resume then
    begin
      Sleep(50);
      ok := Connect(C, trust, cache, ver, suite, res, info2) and res;
      if not res then info2 := info2 + ' [NOT RESUMED]';
    end;
    Inc(Total);
    if ok then WriteLn('ok   ', C.Name:28, '  ', info)
    else begin Inc(Fails); WriteLn('FAIL ', C.Name:28, '  ', info, ' | ', info2); end;
    if C.Resume and ok then WriteLn('     ', '':28, '  ', info2);
  finally
    p.Terminate(0);
    p.Free;
    trust.Free; cache.Free;
  end;
end;

function MkCase(const Name, Args: string; ExpVer, ExpSuite: Word; Resume: Boolean = False;
  const Cert: string = 'leaf.pem'; const Key: string = 'leaf.key'; const Chain: string = 'int.pem';
  const Anchor: string = 'root.pem'; const Host: string = 'ok.test'; MaxVer: Word = 0): TCase;
begin
  Result.Name := Name; Result.Args := Args; Result.ExpVer := ExpVer; Result.ExpSuite := ExpSuite;
  Result.Resume := Resume; Result.Cert := Cert; Result.Key := Key; Result.Chain := Chain;
  Result.Anchor := Anchor; Result.Host := Host; Result.MaxVer := MaxVer;
end;

begin
  Dir := ExtractFilePath(ParamStr(0)) + 'pki' + PathDelim;
  Fails := 0; Total := 0;
  RunCase(MkCase('1.3 AES128', '-tls1_3 -ciphersuites TLS_AES_128_GCM_SHA256', $0304, $1301));
  RunCase(MkCase('1.3 AES256', '-tls1_3 -ciphersuites TLS_AES_256_GCM_SHA384', $0304, $1302));
  RunCase(MkCase('1.3 CHACHA', '-tls1_3 -ciphersuites TLS_CHACHA20_POLY1305_SHA256', $0304, $1303));
  RunCase(MkCase('1.3 tickets (AES128)', '-tls1_3 -ciphersuites TLS_AES_128_GCM_SHA256', $0304, $1301, True));
  RunCase(MkCase('1.3 tickets (AES256/SHA384)', '-tls1_3 -ciphersuites TLS_AES_256_GCM_SHA384', $0304, $1302, True));
  RunCase(MkCase('1.3 HRR -> P-256', '-tls1_3 -groups P-256', $0304, 0, True));
  RunCase(MkCase('1.3 HRR -> P-384', '-tls1_3 -groups P-384', $0304, 0));
  RunCase(MkCase('1.3 HRR -> P-521', '-tls1_3 -groups P-521', $0304, 0));
  RunCase(MkCase('1.3 client cert request', '-tls1_3 -verify 1', $0304, 0));
  RunCase(MkCase('1.3 small fragments', '-tls1_3 -max_send_frag 512', $0304, 0));
  RunCase(MkCase('1.2 ECDHE-ECDSA-AES128', '-tls1_2 -cipher ECDHE-ECDSA-AES128-GCM-SHA256', $0303, $C02B));
  RunCase(MkCase('1.2 ECDHE-ECDSA-AES256', '-tls1_2 -cipher ECDHE-ECDSA-AES256-GCM-SHA384', $0303, $C02C));
  RunCase(MkCase('1.2 ECDHE-ECDSA-CHACHA', '-tls1_2 -cipher ECDHE-ECDSA-CHACHA20-POLY1305', $0303, $CCA9));
  RunCase(MkCase('1.2 ECDHE-RSA-AES128 (PSS)', '-tls1_2 -cipher ECDHE-RSA-AES128-GCM-SHA256', $0303, $C02F, False,
    'leafpss.pem', 'leafpss.key', 'intpss.pem', 'rootrsa.pem', 'pss.test'));
  RunCase(MkCase('1.2 ECDHE-RSA-AES256', '-tls1_2 -cipher ECDHE-RSA-AES256-GCM-SHA384', $0303, $C030, False,
    'leafpss.pem', 'leafpss.key', 'intpss.pem', 'rootrsa.pem', 'pss.test'));
  RunCase(MkCase('1.2 ECDHE-RSA-CHACHA', '-tls1_2 -cipher ECDHE-RSA-CHACHA20-POLY1305', $0303, $CCA8, False,
    'leafpss.pem', 'leafpss.key', 'intpss.pem', 'rootrsa.pem', 'pss.test'));
  RunCase(MkCase('1.2 group P-384', '-tls1_2 -groups P-384', $0303, 0));
  RunCase(MkCase('1.2 group P-521', '-tls1_2 -groups P-521', $0303, 0));
  RunCase(MkCase('1.2 tickets', '-tls1_2', $0303, 0, True));
  RunCase(MkCase('1.2 session ID (no tickets)', '-tls1_2 -no_ticket', $0303, 0, True));
  RunCase(MkCase('1.2 without EMS', '-tls1_2 -no_ticket', $0303, 0, True));
  RunCase(MkCase('1.2 client cert request', '-tls1_2 -verify 1', $0303, 0));
  RunCase(MkCase('1.2 small fragments', '-tls1_2 -max_send_frag 512', $0303, 0));
  RunCase(MkCase('client 1.2 only vs 1.3', '', $0303, 0, True, 'leaf.pem', 'leaf.key', 'int.pem', 'root.pem', 'ok.test', $0303));
  RunCase(MkCase('1.3 RSA-PSS cert', '-tls1_3', $0304, 0, True, 'leafpss.pem', 'leafpss.key', 'intpss.pem', 'rootrsa.pem', 'pss.test'));
  RunCase(MkCase('1.3 ECDSA P-384 cert', '-tls1_3', $0304, 0, False, 'leaf384.pem', 'leaf384.key', '', 'root384.pem', 'e384.test'));
  RunCase(MkCase('1.2 ECDSA P-384 cert', '-tls1_2', $0303, 0, False, 'leaf384.pem', 'leaf384.key', '', 'root384.pem', 'e384.test'));
  WriteLn(Format('local: %d cases, %d failures', [Total, Fails]));
  if Fails > 0 then Halt(1);
end.
