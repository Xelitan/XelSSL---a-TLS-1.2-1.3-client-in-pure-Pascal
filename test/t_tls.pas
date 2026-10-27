// XelSSL client test against real servers.
// t_tls host[:port] [tls12] [noverify] [chacha] [get] [ra] [path]  - no arguments: server list
// ra (or XELSSL_TEST_RA=1): read-ahead thread
program t_tls;

{$mode objfpc}{$H+}

uses
  SysUtils, Classes, {$IFDEF UNIX}cthreads,{$ENDIF} sockets, ssockets, XelSslHash, XelSslClient;

type
  TTransport = class
    Sock: TInetSocket;
    function DoSend(const Buf; Len: Integer): Integer;
    function DoRecv(var Buf; Len: Integer): Integer;
    procedure DoShutdown;
  end;

function TTransport.DoSend(const Buf; Len: Integer): Integer;
begin
  try Result := Sock.Write(Buf, Len); except Result := -1; end;
end;

function TTransport.DoRecv(var Buf; Len: Integer): Integer;
begin
  try Result := Sock.Read(Buf, Len); except Result := -1; end;
end;

procedure TTransport.DoShutdown;
begin
  fpshutdown(Sock.Handle, 2);
end;

var
  Cache: TXelSslSessionCache;

var
  ChaChaOnly: Boolean = False;     // offer only the ChaCha20-Poly1305 suites (parameter "chacha")
  ForceGet: Boolean = False;       // HTTP GET also on ports other than 443 (parameter "get")
  ReadAhead: Boolean = False;      // reader thread (parameter "ra")

{$IFDEF MSWINDOWS}
function GetProcessTimes(P: THandle; out C, E, K, U: Int64): LongBool; stdcall; external 'kernel32';
function GetCurrentProcess: THandle; stdcall; external 'kernel32';
{$ENDIF}

// CPU time of this process in ms (all threads, user + kernel); 0 where unknown
function CpuMs: Int64;
{$IFDEF MSWINDOWS}
var c, e, k, u: Int64;
begin
  if GetProcessTimes(GetCurrentProcess, c, e, k, u) then Result := (k + u) div 10000 else Result := 0;
end;
{$ELSE}
begin
  Result := 0;
end;
{$ENDIF}

function Fetch(const HostPort: string; MaxVer: Word; Verify: Boolean; const Path: string;
  out Info: string): Integer;   // returns the response size in bytes, -1 on error
var
  t: TTransport; c: TXelSslClient; host: string; port, n: Integer; req: RawByteString;
  buf: array[0..16383] of Byte; total: Integer; first: string; t0, t1: QWord; c1: Int64;
begin
  Result := -1; Info := '';
  host := HostPort; port := 443;
  if Pos(':', HostPort) > 0 then
  begin
    host := Copy(HostPort, 1, Pos(':', HostPort) - 1);
    port := StrToInt(Copy(HostPort, Pos(':', HostPort) + 1, 9));
  end;
  t := TTransport.Create;
  c := nil;
  try
    try
      t.Sock := TInetSocket.Create(host, port);
    except
      on E: Exception do begin Info := 'TCP: ' + E.Message; Exit; end;
    end;
    c := TXelSslClient.Create(@t.DoSend, @t.DoRecv);
    c.Host := host;
    c.VerifyPeer := Verify;
    c.MaxVersion := MaxVer;
    if ChaChaOnly then c.CipherSuites := [$1303, $CCA9, $CCA8];
    c.Cache := Cache;
    c.ReadAhead := ReadAhead;
    c.ShutdownFn := @t.DoShutdown;
    c.Alpn := ['http/1.1'];
    t0 := GetTickCount64;
    if not c.Handshake then begin Info := 'ERROR: ' + c.LastError; Exit; end;
    Info := Format('%s %s%s alpn=%s [%d ms]', [TlsVersionName(c.Version), TlsSuiteName(c.CipherSuite),
      BoolToStr(c.Resumed, ' RESUMED', ''), c.NegotiatedAlpn, GetTickCount64 - t0]);
    if (port <> 443) and not ForceGet then begin Result := 0; Exit; end;   // non-HTTP: handshake only
    t1 := GetTickCount64; c1 := CpuMs;
    req := 'GET ' + Path + ' HTTP/1.1'#13#10'Host: ' + host + #13#10'User-Agent: xelssl-test'#13#10'Connection: close'#13#10#13#10;
    c.Write(req[1], Length(req));
    total := 0; first := '';
    repeat
      n := c.Read(buf, SizeOf(buf));
      if n > 0 then
      begin
        if total = 0 then
        begin
          SetString(first, PAnsiChar(@buf[0]), n);
          first := Copy(first, 1, Pos(#13, first) - 1);
        end;
        Inc(total, n);
      end;
    until n <= 0;
    if (n < 0) and (total = 0) then Info := Info + ' read: ' + c.LastError;
    c.Close;
    Info := Info + '  ' + first + Format(' (%d B)', [total]);
    if total > 10000000 then
      Info := Info + Format(' %.0f MB/s, client CPU %d of %d ms', [total / 1048576 / ((GetTickCount64 - t1 + 1) / 1000),
        CpuMs - c1, GetTickCount64 - t1]);
    Result := total;
  finally
    c.Free;
    t.Sock.Free;
    t.Free;
  end;
end;

const
  Hosts: array[0..21] of string = ('example.com', 'www.google.com', 'github.com', 'www.cloudflare.com',
    'letsencrypt.org', 'www.wikipedia.org', 'www.microsoft.com', 'www.amazon.com', 'onet.pl', 'www.gov.pl',
    'ecc256.badssl.com', 'ecc384.badssl.com', 'rsa2048.badssl.com', 'rsa4096.badssl.com',
    'tls-v1-2.badssl.com:1012', 'expired.badssl.com', 'wrong.host.badssl.com', 'self-signed.badssl.com',
    'untrusted-root.badssl.com', 'incomplete-chain.badssl.com', 'smtp.gmail.com:465', 'test.rebex.net:990');

var
  i: Integer; info: string; ver: Word; verify: Boolean; path: string;
begin
  Cache := TXelSslSessionCache.Create;
  if GetEnvironmentVariable('XELSSL_TEST_RA') = '1' then ReadAhead := True;
  ver := $0304; verify := True; path := '/';
  if ParamCount >= 1 then
  begin
    for i := 2 to ParamCount do
      if ParamStr(i) = 'tls12' then ver := $0303
      else if ParamStr(i) = 'chacha' then ChaChaOnly := True
      else if ParamStr(i) = 'get' then ForceGet := True
      else if ParamStr(i) = 'ra' then ReadAhead := True
      else if ParamStr(i) = 'noverify' then verify := False
      else path := ParamStr(i);
    Fetch(ParamStr(1), ver, verify, path, info); WriteLn(ParamStr(1), ': ', info);
    Fetch(ParamStr(1), ver, verify, path, info); WriteLn(ParamStr(1), ' (2): ', info);
  end
  else
    for i := 0 to High(Hosts) do
    begin
      Fetch(Hosts[i], $0304, True, '/', info);
      WriteLn(Format('%-30s %s', [Hosts[i], info]));
    end;
  Cache.Free;
end.
