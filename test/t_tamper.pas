// Robustness tests: a proxy flips 1 bit in the server-to-client stream (flipproxy.py).
// Every change must end in an error - never in accepted data.
program t_tamper;

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

var
  Dir: string; Fails, Port: Integer;

// returns True when the client accepted a complete HTTP response
function Fetch(P: Integer; Trust: TTrustStore; out Info: string): Boolean;
var t: TTransport; c: TXelSslClient; req: RawByteString; buf: array[0..65535] of Byte; n, total: Integer;
begin
  Result := False; Info := '';
  t := TTransport.Create; c := nil;
  try
    try t.Sock := TInetSocket.Create('127.0.0.1', P);
    except on E: Exception do begin Info := 'TCP ' + E.Message; Exit; end; end;
    c := TXelSslClient.Create(@t.DoSend, @t.DoRecv);
    c.Host := 'ok.test'; c.Trust := Trust;
    if not c.Handshake then begin Info := 'handshake: ' + c.LastError; Exit; end;
    req := 'GET / HTTP/1.0'#13#10#13#10;
    c.Write(req[1], Length(req));
    total := 0;
    repeat n := c.Read(buf, SizeOf(buf)); if n > 0 then Inc(total, n); until n <= 0;
    if n < 0 then Info := Format('read after %d B: %s', [total, c.LastError])
    else begin Info := Format('accepted %d B', [total]); Result := total > 0; end;
  finally
    c.Free; t.Sock.Free; t.Free;
  end;
end;

procedure Run(const Name, SrvArgs: string; Offsets: array of Integer);
var srv, px: TProcess; trust: TTrustStore; i, j: Integer; info: string; ok: Boolean; a: TStringArray;
begin
  Inc(Port, 2);
  srv := TProcess.Create(nil);
  srv.Executable := 'openssl';
  srv.Parameters.AddStrings(['s_server', '-accept', IntToStr(Port), '-cert', Dir + 'leaf.pem', '-key',
    Dir + 'leaf.key', '-cert_chain', Dir + 'int.pem', '-www', '-quiet']);
  a := SrvArgs.Split([' ']);
  for j := 0 to High(a) do if a[j] <> '' then srv.Parameters.Add(a[j]);
  srv.Options := [poNoConsole];
  srv.Execute;
  trust := TTrustStore.Create;
  trust.AddFile(Dir + 'root.pem');
  try
    for i := 0 to High(Offsets) do
    begin
      px := TProcess.Create(nil);
      px.Executable := 'python';
      px.Parameters.AddStrings([ExtractFilePath(ParamStr(0)) + '..' + PathDelim + 'flipproxy.py',
        IntToStr(Port + 1), IntToStr(Port), IntToStr(Offsets[i])]);
      px.Options := [poNoConsole];
      px.Execute;
      Sleep(700);
      ok := Fetch(Port + 1, trust, info);
      if Offsets[i] < 0 then
      begin
        if not ok then begin Inc(Fails); WriteLn('FAIL ', Name, ' unmodified: ', info); end
        else WriteLn('ok   ', Name, ' unmodified: ', info);
      end
      else if ok then begin Inc(Fails); WriteLn('FAIL ', Name, ' bit ', Offsets[i], ': MODIFIED DATA ACCEPTED ', info); end
      else WriteLn('ok   ', Name, ' bit ', Offsets[i]:5, ': rejected - ', info);
      px.Terminate(0); px.Free;
      Sleep(100);
    end;
  finally
    srv.Terminate(0); srv.Free; trust.Free;
  end;
end;

begin
  Dir := ExtractFilePath(ParamStr(0)) + 'pki' + PathDelim;
  Fails := 0; Port := 45000;
  // TLS 1.3: ServerHello (random/key), encrypted EE/Cert/CV/Finished, application data, header
  Run('TLS1.3', '-tls1_3', [-1, 3, 20, 70, 140, 400, 900, 1300, 2500, 4000]);
  // TLS 1.2: plaintext certificate, ServerKeyExchange, Finished, data
  Run('TLS1.2', '-tls1_2', [-1, 3, 20, 70, 300, 900, 1200, 1400, 2500, 4000]);
  WriteLn(Format('tampering: %d failures', [Fails]));
  if Fails > 0 then Halt(1);
end.
