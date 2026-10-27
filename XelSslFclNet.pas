// XelSSL - fcl-net integration: a TSSLSocketHandler for TInetSocket / TFPHTTPClient.
// Just using the unit registers TXelSslSocketHandler as the default SSL handler.
// It can also be attached to an ALREADY connected socket (STARTTLS): Attach + Connect.
// License: MIT.
unit XelSslFclNet;

{$mode objfpc}{$H+}

interface

uses
  SysUtils, Classes, ssockets, sslsockets, sslbase, XelSslClient, XelSslTrust;

type
  TXelSslSocketHandler = class(TSSLSocketHandler)
  private
    FTls: TXelSslClient;
    FErr: string;
    FHostName: string;
    FCache: TXelSslSessionCache;
    FTrust: TTrustStore;
    FReadAhead: Boolean;
    function RawSend(const Buf; Len: Integer): Integer;
    procedure RawShutdown;
    function RawRecv(var Buf; Len: Integer): Integer;
  public
    constructor Create; override;
    destructor Destroy; override;
    // the base version raises ("without SSL support"); the client never generates certificates
    function CreateCertGenerator: TX509Certificate; override;
    // attach to an existing, connected socket (e.g. after STARTTLS)
    procedure Attach(AStream: TSocketStream);
    function Connect: Boolean; override;
    function Close: Boolean; override;
    function Shutdown(BiDirectional: Boolean): Boolean; override;
    function Send(const Buffer; Count: Integer): Integer; override;
    function Recv(const Buffer; Count: Integer): Integer; override;
    function BytesAvailable: Integer; override;
    property LastErrorDesc: string read FErr;
    // name for SNI/verification; defaults to TInetSocket.Host
    property HostName: string read FHostName write FHostName;
    // nil = the process-wide cache (used only with VerifyPeerCert and the system store)
    property SessionCache: TXelSslSessionCache read FCache write FCache;
    property TrustStore: TTrustStore read FTrust write FTrust;
    // receive and decrypt in a separate thread (TXelSslClient.ReadAhead); off by default
    property ReadAhead: Boolean read FReadAhead write FReadAhead;
    property Tls: TXelSslClient read FTls;
  end;

// process-wide session cache: new connections to a known server resume the session
// (a shorter handshake) instead of doing a full key exchange and certificate check
function XelSslSharedCache: TXelSslSessionCache;

implementation

uses
  Sockets, {$IFDEF MSWINDOWS}WinSock2{$ELSE}BaseUnix{$ENDIF};

{$IFDEF MSWINDOWS}
const
  SEND_FLAGS = 0;
{$ELSE}
const
  {$IFDEF LINUX}SEND_FLAGS = MSG_NOSIGNAL;{$ELSE}SEND_FLAGS = 0;{$ENDIF}
{$ENDIF}

var
  GSharedCache: TXelSslSessionCache;

function XelSslSharedCache: TXelSslSessionCache;
begin
  Result := GSharedCache;
end;

constructor TXelSslSocketHandler.Create;
begin
  inherited Create;
  VerifyPeerCert := True;
end;

destructor TXelSslSocketHandler.Destroy;
begin
  FreeAndNil(FTls);
  inherited Destroy;
end;

function TXelSslSocketHandler.CreateCertGenerator: TX509Certificate;
begin
  Result := nil;
end;

procedure TXelSslSocketHandler.Attach(AStream: TSocketStream);
begin
  SetSocket(AStream);
end;

function TXelSslSocketHandler.RawSend(const Buf; Len: Integer): Integer;
begin
  {$IFDEF MSWINDOWS}
  Result := WinSock2.send(Socket.Handle, Buf, Len, SEND_FLAGS);
  {$ELSE}
  repeat
    Result := fpSend(Socket.Handle, @Buf, Len, SEND_FLAGS);
  until (Result >= 0) or (SocketError <> ESysEINTR);
  {$ENDIF}
end;

function TXelSslSocketHandler.RawRecv(var Buf; Len: Integer): Integer;
begin
  {$IFDEF MSWINDOWS}
  Result := WinSock2.recv(Socket.Handle, Buf, Len, 0);
  {$ELSE}
  repeat
    Result := fpRecv(Socket.Handle, @Buf, Len, 0);
  until (Result >= 0) or (SocketError <> ESysEINTR);
  {$ENDIF}
end;

procedure TXelSslSocketHandler.RawShutdown;
begin
  if Socket <> nil then fpshutdown(Socket.Handle, 2);
end;

function TXelSslSocketHandler.Connect: Boolean;
var bufSize: LongInt;
begin
  Result := False;
  FErr := '';
  FreeAndNil(FTls);
  // larger socket buffers: fewer system calls and a full TCP window on fast links
  if Socket <> nil then
  begin
    bufSize := 1024 * 1024;
    fpsetsockopt(Socket.Handle, SOL_SOCKET, SO_RCVBUF, @bufSize, SizeOf(bufSize));
    fpsetsockopt(Socket.Handle, SOL_SOCKET, SO_SNDBUF, @bufSize, SizeOf(bufSize));
  end;
  FTls := TXelSslClient.Create(@RawSend, @RawRecv);
  if FHostName <> '' then FTls.Host := FHostName
  else if Socket is TInetSocket then FTls.Host := TInetSocket(Socket).Host;
  FTls.VerifyPeer := VerifyPeerCert;
  FTls.Cache := FCache;
  // the shared cache only for verified connections against the system store, so that a
  // session from a connection without verification never skips the check later
  if (FTls.Cache = nil) and VerifyPeerCert and (FTrust = nil) then
  begin
    FTls.Cache := GSharedCache;
    if Socket is TInetSocket then
      FTls.CacheKey := LowerCase(FTls.Host) + ':' + IntToStr(TInetSocket(Socket).Port);
  end;
  FTls.Trust := FTrust;
  FTls.ReadAhead := FReadAhead;
  FTls.ShutdownFn := @RawShutdown;
  Result := FTls.Handshake;
  if Result then SetSSLActive(True)
  else
  begin
    FErr := FTls.LastError;
    FLastError := 1;
  end;
end;

function TXelSslSocketHandler.Close: Boolean;
begin
  if (FTls <> nil) and FTls.Connected then FTls.Close;
  SetSSLActive(False);
  Result := True;
end;

function TXelSslSocketHandler.Shutdown(BiDirectional: Boolean): Boolean;
begin
  Result := Close;
end;

function TXelSslSocketHandler.Send(const Buffer; Count: Integer): Integer;
begin
  FLastError := 0;
  if FTls = nil then Exit(-1);
  Result := FTls.Write(Buffer, Count);
  if Result < 0 then begin FErr := FTls.LastError; FLastError := 1; end;
end;

function TXelSslSocketHandler.Recv(const Buffer; Count: Integer): Integer;
begin
  FLastError := 0;
  if FTls = nil then Exit(-1);
  Result := FTls.Read(PByte(@Buffer)^, Count);
  if Result < 0 then begin FErr := FTls.LastError; FLastError := 1; end;
end;

function TXelSslSocketHandler.BytesAvailable: Integer;
begin
  if FTls = nil then Result := 0 else Result := FTls.Pending;
end;

initialization
  GSharedCache := TXelSslSessionCache.Create;
  TSSLSocketHandler.SetDefaultHandlerClass(TXelSslSocketHandler);
finalization
  FreeAndNil(GSharedCache);
end.
