// XelSSL - TLS 1.3 (RFC 8446) and TLS 1.2 (RFC 5246) client in pure Pascal.
//
// TLS 1.3: TLS_AES_128_GCM_SHA256, TLS_AES_256_GCM_SHA384, TLS_CHACHA20_POLY1305_SHA256;
//          HelloRetryRequest, session resumption (PSK from tickets, psk_dhe_ke), KeyUpdate.
// TLS 1.2: ECDHE_{ECDSA,RSA}_WITH_AES_{128,256}_GCM, ECDHE_*_CHACHA20_POLY1305;
//          extended master secret (RFC 7627), resumption (session ID, RFC 5077 tickets),
//          renegotiation refused, downgrade protection (RFC 8446 4.1.3).
// Key exchange: X25519, P-256, P-384, P-521. Certificate verification: XelSslX509 + XelSslTrust.
//
// Transport: two functions (send/receive raw bytes) - independent of sockets.
// Read-ahead (optional): after the handshake a reader thread receives and decrypts records
// while the caller handles the previous ones.
// License: MIT.
unit XelSslClient;

{$mode objfpc}{$H+}{$Q-}{$R-}
{$modeswitch advancedrecords}

interface

uses
  SysUtils, Classes, SyncObjs, XelSslHash, XelSslX509, XelSslTrust;

type
  TXelSslSendFn = function(const Buf; Len: Integer): Integer of object;   // bytes sent, <=0 = error
  TXelSslRecvFn = function(var Buf; Len: Integer): Integer of object;     // bytes received, 0 = EOF, <0 = error
  TXelSslShutdownFn = procedure of object;                                // unblocks a pending receive

  ETlsError = class(Exception)
  public
    Alert: Byte;
    constructor CreateAlert(AAlert: Byte; const Msg: string);
  end;

  // Session remembered for resumption
  TXelSslSession = record
    Version, Suite: Word;
    Ticket: TBytes;          // TLS 1.3: PSK identity; TLS 1.2: RFC 5077 ticket (may be empty)
    Secret: TBytes;          // TLS 1.3: PSK; TLS 1.2: master secret
    SessionId: TBytes;       // TLS 1.2
    Ems: Boolean;            // TLS 1.2 extended master secret
    AgeAdd, Lifetime: UInt32;
    ReceivedMs: QWord;
  end;

  // Session cache (shared by connections to the same server, e.g. FTPS)
  TXelSslSessionCache = class
  private
    FLock: TCriticalSection;
    FKeys: TStringList;
    FItems: array of TXelSslSession;
  public
    constructor Create;
    destructor Destroy; override;
    procedure Put(const Key: string; const S: TXelSslSession);
    function Get(const Key: string; out S: TXelSslSession): Boolean;
    procedure Remove(const Key: string);
  end;

  TCipherState = record
    Active, Tls13, ChaCha: Boolean;
    Key, IV: TBytes;
    Gcm: Pointer;            // ^TGcmKey (GCM only)
    Seq: QWord;
  end;

const
  TLS_READ_AHEAD_SLOTS = 32;   // decrypted records queued by the reader thread

type
  TXelSslClient = class
  private
    FSend: TXelSslSendFn;
    FRecv: TXelSslRecvFn;
    FIn: TBytes;             // raw bytes from the transport
    FInPos, FInLen: Integer;
    FRd, FWr: TCipherState;
    FHs: TBytes;             // unprocessed handshake message bytes
    FTranscript: TBytes;
    FAppP: PByte;            // decrypted application data, in place in FIn (valid until the
    FAppLen, FAppPos: Integer; // next record is read)
    FOut: TBytes;            // the record being sent (built and encrypted in place)
    FVersion, FSuite: Word;
    FHash: THashAlg;
    FKeyLen: Integer;
    FChaCha: Boolean;
    FClientRandom, FServerRandom, FSessionId: TBytes;
    FPriv, FPub: TBytes;     // X25519
    FPPriv, FPPub: TBytes;   // NIST P-256/384/521 (after HelloRetryRequest or in TLS 1.2)
    FKsGroup: Word;          // key share group in ClientHello (TLS 1.3)
    FConnected, FClosed, FPeerClosed, FResumed: Boolean;
    FLastError, FAlpnSel: string;
    FPeerChain: TBytesArray;
    FLeaf: TCert;
    // TLS 1.3
    FResMaster, FCAppSecret, FSAppSecret: TBytes;
    // TLS 1.2
    FMaster: TBytes;
    FEms: Boolean;
    FOffered: TXelSslSession;  // session offered for resumption
    FHaveOffered: Boolean;
    // read-ahead: the reader thread owns FIn/FRd while it runs; records go through a ring
    FReader: TThread;
    FRaLock: TCriticalSection;
    FRaNotEmpty, FRaNotFull: PRTLEvent;
    FRaSlots: array[0..TLS_READ_AHEAD_SLOTS - 1] of TBytes;
    FRaLens: array[0..TLS_READ_AHEAD_SLOTS - 1] of Integer;
    FRaTyps: array[0..TLS_READ_AHEAD_SLOTS - 1] of Byte;
    FRaHead, FRaTail: Int64;   // records taken / queued
    FRaHeld: Boolean;          // the main thread is using the slot at FRaHead
    FRaEof, FRaFailed, FRaStop: Boolean;
    FRaConsWaiting, FRaProdWaiting: Boolean;   // a side sleeps on its event (signal only then)
    FRaErr: string;
    FRaAlert: Byte;
    procedure Fail(Alert: Byte; const Msg: string);
    procedure SendAlert(Level, Desc: Byte);
    procedure RawSend(const B: TBytes);
    procedure RawSendP(P: PByte; Len: Integer);
    function FillIn(Need: Integer): Boolean;
    procedure SendRecord(Typ: Byte; const Data: TBytes);
    procedure SendRecordP(Typ: Byte; P: PByte; Len: Integer);
    function ReadRecordDirect(out Typ: Byte; out P: PByte; out Len: Integer): Boolean;
    function ReadRecordView(out Typ: Byte; out P: PByte; out Len: Integer): Boolean;
    procedure StartReader;
    procedure StopReader;
    procedure ReaderLoop;
    function ReadRecord(out Typ: Byte; out Data: TBytes): Boolean;
    function NextHsMessage(out MsgType: Byte; out Body, Raw: TBytes): Boolean;
    procedure SendHandshake(MsgType: Byte; const Body: TBytes; AddToTranscript: Boolean = True);
    function TranscriptHash: TBytes;
    procedure SetCipher(var CS: TCipherState; const Key, IV: TBytes; Tls13: Boolean);
    procedure SetTraffic13(var CS: TCipherState; const Secret: TBytes);
    function BuildClientHello(const Cookie: TBytes; const Prefix: TBytes): TBytes;
    procedure VerifyServerCertificate;
    procedure HandshakeTls13(const SH: TBytes; HrrDone: Boolean; const Psk: TBytes);
    procedure HandshakeTls12(const SHBody: TBytes; const SHExt: TBytes; Resuming: Boolean);
    procedure HandlePostHandshake(MsgType: Byte; const Body: TBytes);
    procedure UpdateTraffic13(Read: Boolean);
    function CacheKeyName: string;
  public
    Host: string;                 // SNI and the name checked in the certificate
    VerifyPeer: Boolean;          // default True
    Trust: TTrustStore;           // nil = system store
    Cache: TXelSslSessionCache;     // nil = no resumption
    CacheKey: string;             // default Host
    Alpn: TStringArray;           // e.g. ['http/1.1']
    MaxVersion: Word;             // $0304 = TLS 1.3, $0303 = TLS 1.2
    CipherSuites: array of Word;  // offered suites in this order (empty = the default list)
    // receive and decrypt in a separate thread after the handshake; needs ShutdownFn, which
    // must make a pending receive return (e.g. shutdown() of the socket); off by default
    ReadAhead: Boolean;
    ShutdownFn: TXelSslShutdownFn;
    constructor Create(ASend: TXelSslSendFn; ARecv: TXelSslRecvFn);
    destructor Destroy; override;
    function Handshake: Boolean;
    function Read(var Buf; Len: Integer): Integer;
    function Write(const Buf; Len: Integer): Integer;
    function Pending: Integer;
    procedure Close;
    property LastError: string read FLastError;
    property Version: Word read FVersion;
    property CipherSuite: Word read FSuite;
    property Resumed: Boolean read FResumed;
    property NegotiatedAlpn: string read FAlpnSel;
    property PeerChain: TBytesArray read FPeerChain;
    property Connected: Boolean read FConnected;
  end;

function TlsVersionName(V: Word): string;
function TlsSuiteName(S: Word): string;

implementation

uses XelSslAes, XelSslChaCha, XelSslX25519, XelSslEcdh, XelSslRandom, XelSslPk;

const
  // record types
  RT_CCS = 20; RT_ALERT = 21; RT_HANDSHAKE = 22; RT_APP = 23;
  // handshake message types
  HT_CLIENT_HELLO = 1; HT_SERVER_HELLO = 2; HT_NEW_SESSION_TICKET = 4; HT_END_OF_EARLY_DATA = 5;
  HT_ENCRYPTED_EXTENSIONS = 8; HT_CERTIFICATE = 11; HT_SERVER_KEY_EXCHANGE = 12;
  HT_CERTIFICATE_REQUEST = 13; HT_SERVER_HELLO_DONE = 14; HT_CERTIFICATE_VERIFY = 15;
  HT_CLIENT_KEY_EXCHANGE = 16; HT_FINISHED = 20; HT_KEY_UPDATE = 24; HT_MESSAGE_HASH = 254;
  HT_HELLO_REQUEST = 0;
  // alerts
  AL_CLOSE_NOTIFY = 0; AL_UNEXPECTED_MESSAGE = 10; AL_BAD_RECORD_MAC = 20; AL_RECORD_OVERFLOW = 22;
  AL_HANDSHAKE_FAILURE = 40; AL_BAD_CERTIFICATE = 42; AL_UNSUPPORTED_CERTIFICATE = 43;
  AL_CERTIFICATE_EXPIRED = 45; AL_CERTIFICATE_UNKNOWN = 46; AL_ILLEGAL_PARAMETER = 47;
  AL_UNKNOWN_CA = 48; AL_DECODE_ERROR = 50; AL_DECRYPT_ERROR = 51; AL_PROTOCOL_VERSION = 70;
  AL_INTERNAL_ERROR = 80; AL_NO_RENEGOTIATION = 100; AL_MISSING_EXTENSION = 109;
  AL_UNSUPPORTED_EXTENSION = 110;
  // extensions
  EXT_SERVER_NAME = 0; EXT_SUPPORTED_GROUPS = 10; EXT_EC_POINT_FORMATS = 11; EXT_SIG_ALGS = 13;
  EXT_ALPN = 16; EXT_EMS = 23; EXT_SESSION_TICKET = 35; EXT_PRE_SHARED_KEY = 41;
  EXT_SUPPORTED_VERSIONS = 43; EXT_COOKIE = 44; EXT_PSK_MODES = 45; EXT_KEY_SHARE = 51;
  EXT_RENEGOTIATION_INFO = $FF01;
  GROUP_X25519 = $001D; GROUP_P256 = $0017; GROUP_P384 = $0018; GROUP_P521 = $0019;
  MAX_PLAIN = 16384;

  SIG_ALGS: array[0..10] of Word = ($0403, $0503, $0603, $0804, $0805, $0806, $0401, $0501, $0601,
    $0809, $080A);
  // preference order: AES-GCM first when the CPU accelerates it, otherwise ChaCha20
  SUITES13: array[Boolean, 0..2] of Word = (($1303, $1301, $1302), ($1301, $1302, $1303));
  SUITES12: array[Boolean, 0..5] of Word = (($CCA9, $CCA8, $C02B, $C02F, $C02C, $C030),
                                            ($C02B, $C02F, $C02C, $C030, $CCA9, $CCA8));

  HRR_RANDOM = 'cf21ad74e59a6111be1d8c021e65b891c2a211167abb8c5e079e09e2c8a8339c';

// ================= helpers =================

type
  TWriter = record
    B: TBytes; N: Integer;
    procedure U8(V: Byte);
    procedure U16(V: Word);
    procedure U24(V: Integer);
    procedure U32(V: UInt32);
    procedure Add(const X: TBytes);
    procedure Vec8(const X: TBytes);
    procedure Vec16(const X: TBytes);
    procedure Vec24(const X: TBytes);
    function Bytes: TBytes;
  end;

  TReader = record
    B: TBytes; P, E: Integer;
    procedure Init(const X: TBytes); overload;
    procedure Init(const X: TBytes; Start, Len: Integer); overload;
    function Left: Integer;
    function U8: Byte;
    function U16: Word;
    function U24: Integer;
    function U32: UInt32;
    function Take(Len: Integer): TBytes;
    function Vec8: TBytes;
    function Vec16: TBytes;
    function Vec24: TBytes;
  end;

procedure TWriter.U8(V: Byte);
begin
  if N + 1 > Length(B) then SetLength(B, 2 * Length(B) + 64);
  B[N] := V; Inc(N);
end;
procedure TWriter.U16(V: Word); begin U8(V shr 8); U8(Byte(V)); end;
procedure TWriter.U24(V: Integer); begin U8(Byte(V shr 16)); U8(Byte(V shr 8)); U8(Byte(V)); end;
procedure TWriter.U32(V: UInt32); begin U16(V shr 16); U16(Word(V)); end;
procedure TWriter.Add(const X: TBytes);
begin
  if Length(X) = 0 then Exit;
  if N + Length(X) > Length(B) then SetLength(B, 2 * Length(B) + Length(X) + 64);
  Move(X[0], B[N], Length(X)); Inc(N, Length(X));
end;
procedure TWriter.Vec8(const X: TBytes); begin U8(Length(X)); Add(X); end;
procedure TWriter.Vec16(const X: TBytes); begin U16(Length(X)); Add(X); end;
procedure TWriter.Vec24(const X: TBytes); begin U24(Length(X)); Add(X); end;
function TWriter.Bytes: TBytes; begin Result := Copy(B, 0, N); end;

procedure DecodeErr;
begin
  raise ETlsError.CreateAlert(AL_DECODE_ERROR, 'malformed message from the server');
end;

procedure TReader.Init(const X: TBytes); begin B := X; P := 0; E := Length(X); end;
procedure TReader.Init(const X: TBytes; Start, Len: Integer); begin B := X; P := Start; E := Start + Len; end;
function TReader.Left: Integer; begin Result := E - P; end;
function TReader.U8: Byte; begin if P + 1 > E then DecodeErr; Result := B[P]; Inc(P); end;
function TReader.U16: Word; begin Result := U8 shl 8; Result := Result or U8; end;
function TReader.U24: Integer; begin Result := U8 shl 16; Result := Result or (U8 shl 8); Result := Result or U8; end;
function TReader.U32: UInt32; begin Result := UInt32(U16) shl 16; Result := Result or U16; end;
function TReader.Take(Len: Integer): TBytes;
begin
  if (Len < 0) or (P + Len > E) then DecodeErr;
  Result := Copy(B, P, Len); Inc(P, Len);
end;
function TReader.Vec8: TBytes; begin Result := Take(U8); end;
function TReader.Vec16: TBytes; begin Result := Take(U16); end;
function TReader.Vec24: TBytes; begin Result := Take(U24); end;

function W16(V: Word): TBytes; begin Result := TBytes.Create(Byte(V shr 8), Byte(V)); end;

function Ext(Typ: Word; const Data: TBytes): TBytes;
var w: TWriter;
begin
  w := Default(TWriter);
  w.U16(Typ); w.Vec16(Data);
  Result := w.Bytes;
end;

constructor ETlsError.CreateAlert(AAlert: Byte; const Msg: string);
begin
  inherited Create(Msg);
  Alert := AAlert;
end;

function TlsVersionName(V: Word): string;
begin
  case V of
    $0304: Result := 'TLSv1.3';
    $0303: Result := 'TLSv1.2';
  else Result := Format('0x%.4x', [V]);
  end;
end;

function TlsSuiteName(S: Word): string;
begin
  case S of
    $1301: Result := 'TLS_AES_128_GCM_SHA256';
    $1302: Result := 'TLS_AES_256_GCM_SHA384';
    $1303: Result := 'TLS_CHACHA20_POLY1305_SHA256';
    $C02B: Result := 'TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256';
    $C02F: Result := 'TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256';
    $C02C: Result := 'TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384';
    $C030: Result := 'TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384';
    $CCA9: Result := 'TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256';
    $CCA8: Result := 'TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256';
  else Result := Format('0x%.4x', [S]);
  end;
end;

function IsOurGroup(G: Word): Boolean;
begin
  Result := (G = GROUP_X25519) or (G = GROUP_P256) or (G = GROUP_P384) or (G = GROUP_P521);
end;

function NistCurve(G: Word): TEcdhCurve;
begin
  case G of
    GROUP_P384: Result := ecdhP384;
    GROUP_P521: Result := ecdhP521;
  else Result := ecdhP256;
  end;
end;

// cipher suite parameters
function SuiteParams(S: Word; out H: THashAlg; out KeyLen: Integer; out ChaCha, Tls13: Boolean): Boolean;
begin
  Result := True; ChaCha := False; Tls13 := False; H := haSHA256; KeyLen := 16;
  case S of
    $1301: Tls13 := True;
    $1302: begin Tls13 := True; H := haSHA384; KeyLen := 32; end;
    $1303: begin Tls13 := True; ChaCha := True; KeyLen := 32; end;
    $C02B, $C02F: ;
    $C02C, $C030: begin H := haSHA384; KeyLen := 32; end;
    $CCA9, $CCA8: begin ChaCha := True; KeyLen := 32; end;
  else Result := False;
  end;
end;

// ================= session cache =================

const
  MAX_CACHED_SESSIONS = 256;

constructor TXelSslSessionCache.Create;
begin
  inherited Create;
  FLock := TCriticalSection.Create;
  FKeys := TStringList.Create;
end;

destructor TXelSslSessionCache.Destroy;
begin
  FKeys.Free; FLock.Free;
  inherited Destroy;
end;

procedure TXelSslSessionCache.Put(const Key: string; const S: TXelSslSession);
var i: Integer;
begin
  FLock.Enter;
  try
    i := FKeys.IndexOf(Key);
    if i < 0 then
    begin
      // bounded size: the oldest entry goes first
      if FKeys.Count >= MAX_CACHED_SESSIONS then
      begin
        for i := 0 to High(FItems) - 1 do FItems[i] := FItems[i + 1];
        SetLength(FItems, Length(FItems) - 1);
        FKeys.Delete(0);
      end;
      i := FKeys.Add(Key);
      SetLength(FItems, FKeys.Count);
    end;
    FItems[i] := S;
  finally FLock.Leave; end;
end;

function TXelSslSessionCache.Get(const Key: string; out S: TXelSslSession): Boolean;
var i: Integer;
begin
  FLock.Enter;
  try
    i := FKeys.IndexOf(Key);
    Result := i >= 0;
    if Result then S := FItems[i] else S := Default(TXelSslSession);
  finally FLock.Leave; end;
end;

procedure TXelSslSessionCache.Remove(const Key: string);
var i, j: Integer;
begin
  FLock.Enter;
  try
    i := FKeys.IndexOf(Key);
    if i < 0 then Exit;
    for j := i to High(FItems) - 1 do FItems[j] := FItems[j + 1];
    SetLength(FItems, Length(FItems) - 1);
    FKeys.Delete(i);
  finally FLock.Leave; end;
end;

// ================= client =================

constructor TXelSslClient.Create(ASend: TXelSslSendFn; ARecv: TXelSslRecvFn);
begin
  inherited Create;
  FSend := ASend; FRecv := ARecv;
  VerifyPeer := True;
  MaxVersion := $0304;
  SetLength(FIn, 64 * 1024);
  FRaLock := TCriticalSection.Create;
  FRaNotEmpty := RTLEventCreate;
  FRaNotFull := RTLEventCreate;
end;

destructor TXelSslClient.Destroy;
begin
  StopReader;
  RTLEventDestroy(FRaNotEmpty);
  RTLEventDestroy(FRaNotFull);
  FRaLock.Free;
  if FRd.Gcm <> nil then FreeMem(FRd.Gcm);
  if FWr.Gcm <> nil then FreeMem(FWr.Gcm);
  Wipe(FMaster); Wipe(FResMaster); Wipe(FPriv);
  inherited Destroy;
end;

procedure TXelSslClient.Fail(Alert: Byte; const Msg: string);
begin
  raise ETlsError.CreateAlert(Alert, Msg);
end;

function TXelSslClient.CacheKeyName: string;
begin
  if CacheKey <> '' then Result := CacheKey else Result := LowerCase(Host);
end;

procedure TXelSslClient.RawSendP(P: PByte; Len: Integer);
var off, n: Integer;
begin
  off := 0;
  while off < Len do
  begin
    n := FSend(P[off], Len - off);
    if n <= 0 then raise ETlsError.CreateAlert(255, 'send failed (connection lost)');
    Inc(off, n);
  end;
end;

procedure TXelSslClient.RawSend(const B: TBytes);
begin
  if Length(B) > 0 then RawSendP(@B[0], Length(B));
end;

procedure TXelSslClient.SendAlert(Level, Desc: Byte);
begin
  try
    SendRecord(RT_ALERT, TBytes.Create(Level, Desc));
  except
    // the connection may already be gone
  end;
end;

// ---- record protection ----

procedure TXelSslClient.SetCipher(var CS: TCipherState; const Key, IV: TBytes; Tls13: Boolean);
begin
  if CS.Gcm <> nil then begin FillChar(CS.Gcm^, SizeOf(TGcmKey), 0); FreeMem(CS.Gcm); CS.Gcm := nil; end;
  CS.Active := True;
  CS.Tls13 := Tls13;
  CS.ChaCha := FChaCha;
  CS.Key := Copy(Key);
  CS.IV := Copy(IV);
  CS.Seq := 0;
  if not FChaCha then
  begin
    CS.Gcm := AllocMem(SizeOf(TGcmKey));
    GcmSetKey(PGcmKey(CS.Gcm)^, Key);
  end;
end;

procedure TXelSslClient.SetTraffic13(var CS: TCipherState; const Secret: TBytes);
begin
  SetCipher(CS, HkdfExpandLabel(FHash, Secret, 'key', nil, FKeyLen),
    HkdfExpandLabel(FHash, Secret, 'iv', nil, 12), True);
end;

function SeqNonce(const IV: TBytes; Seq: QWord): TBytes;
var i: Integer;
begin
  Result := Copy(IV);
  for i := 0 to 7 do
    Result[Length(Result) - 1 - i] := Result[Length(Result) - 1 - i] xor Byte(Seq shr (8 * i));
end;

function SeqBytes(Seq: QWord): TBytes;
var i: Integer;
begin
  SetLength(Result, 8);
  for i := 0 to 7 do Result[7 - i] := Byte(Seq shr (8 * i));
end;

procedure PutSeq(P: PByte; Seq: QWord); inline;
var i: Integer;
begin
  for i := 0 to 7 do P[7 - i] := Byte(Seq shr (8 * i));
end;

// Len bytes at P in records of at most MAX_PLAIN bytes; every record is built in FOut
// and encrypted there (no other copies)
procedure TXelSslClient.SendRecordP(Typ: Byte; P: PByte; Len: Integer);
var
  off, n, size: Integer; o: PByte; nonce: TBytes; aad: array[0..12] of Byte; gn: array[0..11] of Byte;
begin
  off := 0;
  repeat
    n := Len - off;
    if n > MAX_PLAIN then n := MAX_PLAIN;
    size := 5 + 8 + n + 1 + 16;                         // the largest form
    if Length(FOut) < size then SetLength(FOut, size + 1024);
    o := @FOut[0];
    o[1] := 3; o[2] := 3;
    if not FWr.Active then
    begin
      o[0] := Typ;
      o[3] := Byte(n shr 8); o[4] := Byte(n);
      if n > 0 then Move(P[off], o[5], n);
      size := 5 + n;
    end
    else if FWr.Tls13 then
    begin
      // TLSInnerPlaintext = data || type, outer type application_data
      o[0] := RT_APP;
      o[3] := Byte((n + 1 + 16) shr 8); o[4] := Byte(n + 1 + 16);
      if n > 0 then Move(P[off], o[5], n);
      o[5 + n] := Typ;
      nonce := SeqNonce(FWr.IV, FWr.Seq);
      if FWr.ChaCha then ChaChaPolySealP(FWr.Key, nonce, o, 5, o + 5, n + 1, o + 6 + n)
      else GcmSealP(PGcmKey(FWr.Gcm)^, @nonce[0], o, 5, o + 5, n + 1, o + 6 + n);
      size := 5 + n + 1 + 16;
      Inc(FWr.Seq);
    end
    else
    begin
      // TLS 1.2 AEAD: AAD = seq || type || version || plaintext length
      o[0] := Typ;
      PutSeq(@aad[0], FWr.Seq);
      aad[8] := Typ; aad[9] := 3; aad[10] := 3; aad[11] := Byte(n shr 8); aad[12] := Byte(n);
      if FWr.ChaCha then
      begin
        o[3] := Byte((n + 16) shr 8); o[4] := Byte(n + 16);
        if n > 0 then Move(P[off], o[5], n);
        ChaChaPolySealP(FWr.Key, SeqNonce(FWr.IV, FWr.Seq), @aad[0], 13, o + 5, n, o + 5 + n);
        size := 5 + n + 16;
      end
      else
      begin
        // explicit nonce part = sequence number
        o[3] := Byte((8 + n + 16) shr 8); o[4] := Byte(8 + n + 16);
        PutSeq(o + 5, FWr.Seq);
        Move(FWr.IV[0], gn[0], 4);
        PutSeq(@gn[4], FWr.Seq);
        if n > 0 then Move(P[off], o[13], n);
        GcmSealP(PGcmKey(FWr.Gcm)^, @gn[0], @aad[0], 13, o + 13, n, o + 13 + n);
        size := 5 + 8 + n + 16;
      end;
      Inc(FWr.Seq);
    end;
    RawSendP(o, size);
    Inc(off, n);
  until off >= Len;
end;

procedure TXelSslClient.SendRecord(Typ: Byte; const Data: TBytes);
begin
  if Length(Data) > 0 then SendRecordP(Typ, @Data[0], Length(Data))
  else SendRecordP(Typ, nil, 0);
end;

// makes Need unread bytes available at FIn[FInPos] (reads as much as the transport gives)
function TXelSslClient.FillIn(Need: Integer): Boolean;
var n: Integer;
begin
  if FInLen - FInPos >= Need then Exit(True);
  if FInPos = FInLen then begin FInPos := 0; FInLen := 0; end;
  if FInPos + Need > Length(FIn) then
  begin
    if FInLen > FInPos then Move(FIn[FInPos], FIn[0], FInLen - FInPos);
    Dec(FInLen, FInPos); FInPos := 0;
    if Need > Length(FIn) then SetLength(FIn, Need);
  end;
  while FInLen - FInPos < Need do
  begin
    n := FRecv(FIn[FInLen], Length(FIn) - FInLen);
    if n <= 0 then Exit(False);
    Inc(FInLen, n);
  end;
  Result := True;
end;

// Next record, authenticated and decrypted in place in FIn; P/Len = the plaintext,
// valid until the next record is read. Runs in the reader thread when read-ahead is active.
function TXelSslClient.ReadRecordDirect(out Typ: Byte; out P: PByte; out Len: Integer): Boolean;
var len_, i, n: Integer; q: PByte; nonce: TBytes; ok: Boolean; aad: array[0..12] of Byte; gn: array[0..11] of Byte;
begin
  Result := False;
  P := nil; Len := 0;
  if not FillIn(5) then Exit;
  q := @FIn[FInPos];
  Typ := q[0];
  len_ := (q[3] shl 8) or q[4];
  if (q[1] <> 3) or not (Typ in [RT_CCS, RT_ALERT, RT_HANDSHAKE, RT_APP]) then
    Fail(AL_DECODE_ERROR, 'not a TLS stream (bad record header)');
  if len_ > MAX_PLAIN + 2048 then Fail(AL_RECORD_OVERFLOW, 'record too long');
  if not FillIn(5 + len_) then Exit;
  q := @FIn[FInPos];
  Inc(FInPos, 5 + len_);                              // the bytes stay until the next FillIn
  Result := True;
  P := q + 5; Len := len_;
  if (not FRd.Active) or (Typ = RT_CCS) then Exit;    // CCS is never encrypted
  if FRd.Tls13 then
  begin
    if Typ <> RT_APP then Fail(AL_UNEXPECTED_MESSAGE, 'unencrypted record after key change');
    if len_ < 17 then Fail(AL_BAD_RECORD_MAC, 'record too short');
    n := len_ - 16;
    nonce := SeqNonce(FRd.IV, FRd.Seq);
    if FRd.ChaCha then ok := ChaChaPolyOpenP(FRd.Key, nonce, q, 5, q + 5, n, q + 5 + n)
    else ok := GcmOpenP(PGcmKey(FRd.Gcm)^, @nonce[0], q, 5, q + 5, n, q + 5 + n);
    if not ok then Fail(AL_BAD_RECORD_MAC, 'record authentication failed (bad_record_mac)');
    Inc(FRd.Seq);
    i := n - 1;
    while (i >= 0) and (q[5 + i] = 0) do Dec(i);      // strip padding
    if i < 0 then Fail(AL_UNEXPECTED_MESSAGE, 'record without a content type');
    Typ := q[5 + i];
    Len := i;
  end
  else
  begin
    if FRd.ChaCha then
    begin
      if len_ < 16 then Fail(AL_BAD_RECORD_MAC, 'record too short');
      n := len_ - 16;
      PutSeq(@aad[0], FRd.Seq);
      aad[8] := Typ; aad[9] := 3; aad[10] := 3; aad[11] := Byte(n shr 8); aad[12] := Byte(n);
      ok := ChaChaPolyOpenP(FRd.Key, SeqNonce(FRd.IV, FRd.Seq), @aad[0], 13, q + 5, n, q + 5 + n);
    end
    else
    begin
      if len_ < 24 then Fail(AL_BAD_RECORD_MAC, 'record too short');
      n := len_ - 24;
      PutSeq(@aad[0], FRd.Seq);
      aad[8] := Typ; aad[9] := 3; aad[10] := 3; aad[11] := Byte(n shr 8); aad[12] := Byte(n);
      Move(FRd.IV[0], gn[0], 4);
      Move(q[5], gn[4], 8);                           // explicit nonce
      ok := GcmOpenP(PGcmKey(FRd.Gcm)^, @gn[0], @aad[0], 13, q + 13, n, q + 13 + n);
      P := q + 13;
    end;
    if not ok then Fail(AL_BAD_RECORD_MAC, 'record authentication failed (bad_record_mac)');
    Inc(FRd.Seq);
    Len := n;
  end;
  if Len > MAX_PLAIN then Fail(AL_RECORD_OVERFLOW, 'record too long after decryption');
end;

// ---- read-ahead ----

type
  TTlsReader = class(TThread)
  private
    FOwner: TXelSslClient;
  protected
    procedure Execute; override;
  end;

procedure TTlsReader.Execute;
begin
  FOwner.ReaderLoop;
end;

// reader thread: records are decrypted and copied to free slots of the ring; after a
// handshake record (KeyUpdate may change the read keys) it waits until the main thread
// has handled it
procedure TXelSslClient.ReaderLoop;
var typ: Byte; p: PByte; n, slot: Integer; wait, stop, eof, wake: Boolean;
begin
  try
    repeat
      eof := not ReadRecordDirect(typ, p, n);
      if eof then
      begin
        FRaLock.Enter;
        FRaEof := True;
        FRaLock.Leave;
        RTLEventSetEvent(FRaNotEmpty);
        Exit;
      end;
      // a free slot
      repeat
        FRaLock.Enter;
        wait := FRaTail - FRaHead >= TLS_READ_AHEAD_SLOTS;
        stop := FRaStop;
        FRaProdWaiting := wait;
        FRaLock.Leave;
        if stop then Exit;
        if not wait then Break;
        RTLEventWaitFor(FRaNotFull, 200);
      until False;
      slot := FRaTail mod TLS_READ_AHEAD_SLOTS;
      if Length(FRaSlots[slot]) < n then SetLength(FRaSlots[slot], n + 1024);
      if n > 0 then Move(p^, FRaSlots[slot][0], n);
      FRaLens[slot] := n;
      FRaTyps[slot] := typ;
      FRaLock.Enter;
      Inc(FRaTail);
      wake := FRaConsWaiting;
      FRaLock.Leave;
      if wake then RTLEventSetEvent(FRaNotEmpty);
      // after a handshake record: wait until the main thread asks for the next record,
      // i.e. it has handled this one
      if typ = RT_HANDSHAKE then
        repeat
          FRaLock.Enter;
          wait := FRaTail > FRaHead;
          stop := FRaStop;
          FRaProdWaiting := wait;
          FRaLock.Leave;
          if stop then Exit;
          if not wait then Break;
          RTLEventWaitFor(FRaNotFull, 200);
        until False;
    until False;
  except
    on E: Exception do
    begin
      FRaLock.Enter;
      FRaFailed := True;
      FRaErr := E.Message;
      if E is ETlsError then FRaAlert := ETlsError(E).Alert else FRaAlert := AL_INTERNAL_ERROR;
      FRaLock.Leave;
      RTLEventSetEvent(FRaNotEmpty);
    end;
  end;
end;

procedure TXelSslClient.StartReader;
var t: TTlsReader;
begin
  if (FReader <> nil) or not ReadAhead or not Assigned(ShutdownFn) or (TThread.ProcessorCount < 2) then Exit;
  FRaHead := 0; FRaTail := 0; FRaHeld := False;
  FRaEof := False; FRaFailed := False; FRaStop := False; FRaErr := ''; FRaAlert := 255;
  FRaConsWaiting := False; FRaProdWaiting := False;
  RTLEventResetEvent(FRaNotEmpty); RTLEventResetEvent(FRaNotFull);
  // without thread support (e.g. a Unix program without cthreads) records are read directly
  try
    t := TTlsReader.Create(True);
  except
    Exit;
  end;
  t.FOwner := Self;
  t.FreeOnTerminate := False;
  FReader := t;
  t.Start;
end;

// stops the reader thread; ShutdownFn ends the connection's receive side
procedure TXelSslClient.StopReader;
var i: Integer;
begin
  if FReader = nil then Exit;
  FRaLock.Enter;
  FRaStop := True;
  FRaLock.Leave;
  RTLEventSetEvent(FRaNotFull);
  if Assigned(ShutdownFn) then ShutdownFn;
  FReader.WaitFor;
  FreeAndNil(FReader);
  for i := 0 to High(FRaSlots) do FRaSlots[i] := nil;
end;

// next record: from the reader thread's queue, or read directly
function TXelSslClient.ReadRecordView(out Typ: Byte; out P: PByte; out Len: Integer): Boolean;
var avail, failed, eof, wake: Boolean; slot, spin: Integer; err: string; alert: Byte;
begin
  if FReader = nil then Exit(ReadRecordDirect(Typ, P, Len));
  // the previous record's slot is free again
  if FRaHeld then
  begin
    FRaLock.Enter;
    Inc(FRaHead);
    wake := FRaProdWaiting;
    FRaLock.Leave;
    FRaHeld := False;
    if wake then RTLEventSetEvent(FRaNotFull);
  end;
  spin := 0;
  repeat
    FRaLock.Enter;
    avail := FRaTail > FRaHead;
    failed := FRaFailed;
    eof := FRaEof;
    err := FRaErr;
    alert := FRaAlert;
    // sleep only after a short spin: the next record is usually close
    FRaConsWaiting := not avail and not failed and not eof and (spin >= 64);
    FRaLock.Leave;
    if avail then Break;
    if failed then raise ETlsError.CreateAlert(alert, err);
    if eof then begin P := nil; Len := 0; Typ := 0; Exit(False); end;
    if spin < 64 then begin Inc(spin); ThreadSwitch; end
    else RTLEventWaitFor(FRaNotEmpty, 1000);
  until False;
  slot := FRaHead mod TLS_READ_AHEAD_SLOTS;
  FRaHeld := True;
  Typ := FRaTyps[slot];
  P := @FRaSlots[slot][0];
  Len := FRaLens[slot];
  Result := True;
end;

function TXelSslClient.ReadRecord(out Typ: Byte; out Data: TBytes): Boolean;
var p: PByte; n: Integer;
begin
  Data := nil;
  Result := ReadRecordView(Typ, p, n);
  if Result and (n > 0) then
  begin
    SetLength(Data, n);
    Move(p^, Data[0], n);
  end;
end;

function AlertName(D: Byte): string;
begin
  case D of
    0: Result := 'close_notify'; 10: Result := 'unexpected_message'; 20: Result := 'bad_record_mac';
    40: Result := 'handshake_failure'; 42: Result := 'bad_certificate'; 43: Result := 'unsupported_certificate';
    45: Result := 'certificate_expired'; 46: Result := 'certificate_unknown'; 47: Result := 'illegal_parameter';
    48: Result := 'unknown_ca'; 50: Result := 'decode_error'; 51: Result := 'decrypt_error';
    70: Result := 'protocol_version'; 71: Result := 'insufficient_security'; 80: Result := 'internal_error';
    86: Result := 'inappropriate_fallback'; 90: Result := 'user_canceled'; 109: Result := 'missing_extension';
    110: Result := 'unsupported_extension'; 112: Result := 'unrecognized_name'; 116: Result := 'certificate_required';
    120: Result := 'no_application_protocol';
  else Result := IntToStr(D);
  end;
end;

// Returns the next handshake message (joins fragments from several records).
function TXelSslClient.NextHsMessage(out MsgType: Byte; out Body, Raw: TBytes): Boolean;
var typ: Byte; data: TBytes; len: Integer;
begin
  Result := False;
  while True do
  begin
    if Length(FHs) >= 4 then
    begin
      len := (FHs[1] shl 16) or (FHs[2] shl 8) or FHs[3];
      if len > 256 * 1024 then Fail(AL_DECODE_ERROR, 'handshake message too large');
      if Length(FHs) >= 4 + len then
      begin
        MsgType := FHs[0];
        Raw := Copy(FHs, 0, 4 + len);
        Body := Copy(FHs, 4, len);
        FHs := Copy(FHs, 4 + len, Length(FHs) - 4 - len);
        Exit(True);
      end;
    end;
    if not ReadRecord(typ, data) then Fail(255, 'the server closed the connection during the TLS handshake');
    case typ of
      RT_HANDSHAKE: FHs := Concat(FHs, data);
      RT_CCS:
        if (Length(data) <> 1) or (data[0] <> 1) then Fail(AL_UNEXPECTED_MESSAGE, 'malformed ChangeCipherSpec');
      RT_ALERT:
        begin
          if Length(data) >= 2 then
            Fail(255, 'the server rejected the connection: alert ' + AlertName(data[1]))
          else Fail(AL_DECODE_ERROR, 'malformed alert');
        end;
    else Fail(AL_UNEXPECTED_MESSAGE, 'unexpected data during the TLS handshake');
    end;
  end;
end;

procedure TXelSslClient.SendHandshake(MsgType: Byte; const Body: TBytes; AddToTranscript: Boolean);
var w: TWriter; m: TBytes;
begin
  w := Default(TWriter);
  w.U8(MsgType); w.Vec24(Body);
  m := w.Bytes;
  if AddToTranscript then FTranscript := Concat(FTranscript, m);
  SendRecord(RT_HANDSHAKE, m);
end;

function TXelSslClient.TranscriptHash: TBytes;
begin
  Result := Hash(FHash, FTranscript);
end;

// ---- ClientHello ----

function TXelSslClient.BuildClientHello(const Cookie: TBytes; const Prefix: TBytes): TBytes;
var
  w, e, x: TWriter; i: Integer; offer13, psk: Boolean; body, trunc, binder, early, bkey, fkey: TBytes;
  pskHash: THashAlg; kl: Integer; cc, t13: Boolean; age: UInt32; pskExt, binders: TBytes; bl: Integer;
begin
  offer13 := MaxVersion >= $0304;
  psk := FHaveOffered and (FOffered.Version = $0304) and offer13;
  e := Default(TWriter);
  // server_name
  if (Host <> '') and not ParseIp(Host, body) then
  begin
    x := Default(TWriter);
    x.U8(0); x.Vec16(BytesOf(Host));
    e.Add(Ext(EXT_SERVER_NAME, Concat(W16(x.N), x.Bytes)));
  end;
  // supported_versions
  x := Default(TWriter);
  if offer13 then begin x.U8(4); x.U16($0304); x.U16($0303); end
  else begin x.U8(2); x.U16($0303); end;
  e.Add(Ext(EXT_SUPPORTED_VERSIONS, x.Bytes));
  // supported_groups / ec_point_formats
  e.Add(Ext(EXT_SUPPORTED_GROUPS, TBytes.Create(0, 8, 0, GROUP_X25519, 0, GROUP_P256, 0, GROUP_P384, 0, GROUP_P521)));
  e.Add(Ext(EXT_EC_POINT_FORMATS, TBytes.Create(1, 0)));
  // signature_algorithms
  x := Default(TWriter);
  x.U16((Length(SIG_ALGS) + 1) * 2);
  for i := 0 to High(SIG_ALGS) do x.U16(SIG_ALGS[i]);
  x.U16($0201);                                   // rsa_pkcs1_sha1 - only for old TLS 1.2 servers
  e.Add(Ext(EXT_SIG_ALGS, x.Bytes));
  // TLS 1.2: extended master secret, renegotiation_info, session_ticket
  e.Add(Ext(EXT_EMS, nil));
  e.Add(Ext(EXT_RENEGOTIATION_INFO, TBytes.Create(0)));
  if FHaveOffered and (FOffered.Version = $0303) then e.Add(Ext(EXT_SESSION_TICKET, FOffered.Ticket))
  else e.Add(Ext(EXT_SESSION_TICKET, nil));
  // ALPN
  if Length(Alpn) > 0 then
  begin
    x := Default(TWriter);
    for i := 0 to High(Alpn) do x.Vec8(BytesOf(Alpn[i]));
    e.Add(Ext(EXT_ALPN, Concat(W16(x.N), x.Bytes)));
  end;
  if offer13 then
  begin
    // key_share: X25519 (or a NIST curve after HelloRetryRequest)
    x := Default(TWriter);
    if FKsGroup <> GROUP_X25519 then begin x.U16(4 + Length(FPPub)); x.U16(FKsGroup); x.Vec16(FPPub); end
    else begin x.U16(4 + 32); x.U16(GROUP_X25519); x.Vec16(FPub); end;
    e.Add(Ext(EXT_KEY_SHARE, x.Bytes));
    e.Add(Ext(EXT_PSK_MODES, TBytes.Create(1, 1)));           // psk_dhe_ke
    if Length(Cookie) > 0 then e.Add(Ext(EXT_COOKIE, Cookie));
  end;
  // pre_shared_key (always last) - binder computed at the end
  pskExt := nil; bl := 0;
  if psk then
  begin
    SuiteParams(FOffered.Suite, pskHash, kl, cc, t13);
    bl := HashSize(pskHash);
    age := UInt32((GetTickCount64 - FOffered.ReceivedMs) and $FFFFFFFF) + FOffered.AgeAdd;
    x := Default(TWriter);
    x.U16(Length(FOffered.Ticket) + 6);
    x.Vec16(FOffered.Ticket); x.U32(age);
    SetLength(binders, 3 + bl);                                // list length(2) + length(1) + binder
    FillChar(binders[0], Length(binders), 0);
    binders[0] := Byte((1 + bl) shr 8); binders[1] := Byte(1 + bl); binders[2] := bl;
    pskExt := Concat(x.Bytes, binders);
    e.Add(Ext(EXT_PRE_SHARED_KEY, pskExt));
  end;
  // ClientHello
  w := Default(TWriter);
  w.U16($0303);
  w.Add(FClientRandom);
  w.Vec8(FSessionId);
  x := Default(TWriter);
  if Length(CipherSuites) > 0 then
  begin
    for i := 0 to High(CipherSuites) do
      if offer13 or (CipherSuites[i] and $FF00 <> $1300) then x.U16(CipherSuites[i]);
  end
  else
  begin
    if offer13 then for i := 0 to 2 do x.U16(SUITES13[AesHardwareAvailable, i]);
    for i := 0 to 5 do x.U16(SUITES12[AesHardwareAvailable, i]);
  end;
  w.Vec16(x.Bytes);
  w.U8(1); w.U8(0);                                            // compression: null
  w.Vec16(e.Bytes);
  body := w.Bytes;
  // full message (type + length) - the binder covers it without the binder list
  x := Default(TWriter);
  x.U8(HT_CLIENT_HELLO); x.Vec24(body);
  Result := x.Bytes;
  if psk then
  begin
    trunc := Copy(Result, 0, Length(Result) - (3 + bl));
    early := HkdfExtract(pskHash, nil, FOffered.Secret);
    bkey := HkdfExpandLabel(pskHash, early, 'res binder', Hash(pskHash, nil), HashSize(pskHash));
    fkey := HkdfExpandLabel(pskHash, bkey, 'finished', nil, HashSize(pskHash));
    binder := Hmac(pskHash, fkey, Hash(pskHash, Concat(Prefix, trunc)));
    Move(binder[0], Result[Length(Result) - bl], bl);
  end;
end;

// ---- server certificate ----

procedure TXelSslClient.VerifyServerCertificate;
var r: TVerifyResult; err: string; ts: TTrustStore;
begin
  if Length(FPeerChain) = 0 then Fail(AL_BAD_CERTIFICATE, 'the server sent no certificate');
  if not ParseCert(FPeerChain[0], FLeaf) then Fail(AL_BAD_CERTIFICATE, 'cannot parse the server certificate');
  if not VerifyPeer then Exit;
  ts := Trust;
  if ts = nil then ts := SystemTrust;
  r := ts.Verify(FPeerChain, Host, err);
  case r of
    vrOk: ;
    vrExpired: Fail(AL_CERTIFICATE_EXPIRED, 'certificate: ' + err);
    vrUnknownCA: Fail(AL_UNKNOWN_CA, 'certificate: ' + err);
    vrNameMismatch: Fail(AL_BAD_CERTIFICATE, 'certificate: ' + err);
  else Fail(AL_BAD_CERTIFICATE, 'certificate: ' + err);
  end;
end;

function ParseCertificateList(var R: TReader; Tls13: Boolean): TBytesArray;
var lst: TBytes; L: TReader; c: TBytes;
begin
  Result := nil;
  if Tls13 then R.Vec8;                                        // certificate_request_context
  lst := R.Vec24;
  L.Init(lst);
  while L.Left > 0 do
  begin
    c := L.Vec24;
    if Length(c) = 0 then DecodeErr;
    SetLength(Result, Length(Result) + 1);
    Result[High(Result)] := c;
    if Tls13 then L.Vec16;                                     // entry extensions
  end;
end;

// ---- TLS 1.3 ----

procedure TXelSslClient.HandshakeTls13(const SH: TBytes; HrrDone: Boolean; const Psk: TBytes);
var
  R: TReader; mt: Byte; body, raw, shared, early, hs, master, derived, cHs, sHs, th, fk,
  sig, content, vd, ee, exts, alpnB, ctx, zeros: TBytes;
  certReq, pskUsed: Boolean; scheme: Word; i: Integer; L: TReader; et: Word;
begin
  // ServerHello already in the transcript; extract key_share and optionally pre_shared_key
  R.Init(SH);
  R.U16; R.Take(32); R.Vec8; R.U16; R.U8;
  exts := R.Vec16;
  L.Init(exts);
  shared := nil; pskUsed := False;
  while L.Left > 0 do
  begin
    et := L.U16;
    body := L.Vec16;
    case et of
      EXT_KEY_SHARE:
        begin
          if (Length(body) < 4) or (((body[0] shl 8) or body[1]) <> FKsGroup) then
            Fail(AL_ILLEGAL_PARAMETER, 'the server selected a key exchange group that was not offered');
          if FKsGroup <> GROUP_X25519 then
          begin
            if not EcdhShared(NistCurve(FKsGroup), FPPriv, Copy(body, 4, Length(body) - 4), shared) then
              Fail(AL_ILLEGAL_PARAMETER, 'invalid server ECDHE key');
          end
          else
          begin
            if Length(body) <> 4 + 32 then Fail(AL_ILLEGAL_PARAMETER, 'invalid server X25519 key');
            shared := X25519(FPriv, Copy(body, 4, 32));
            i := 0;
            for mt := 0 to 31 do i := i or shared[mt];
            if i = 0 then Fail(AL_ILLEGAL_PARAMETER, 'degenerate X25519 shared secret');
          end;
        end;
      EXT_PRE_SHARED_KEY:
        begin
          if (Length(Psk) = 0) or (Length(body) <> 2) or (body[0] <> 0) or (body[1] <> 0) then
            Fail(AL_ILLEGAL_PARAMETER, 'the server selected a PSK that was not offered');
          pskUsed := True;
        end;
    end;
  end;
  if shared = nil then Fail(AL_MISSING_EXTENSION, 'missing key_share in ServerHello');
  // key schedule
  SetLength(zeros, HashSize(FHash));
  FillChar(zeros[0], Length(zeros), 0);
  if pskUsed then early := HkdfExtract(FHash, nil, Psk)
  else early := HkdfExtract(FHash, nil, zeros);        // no PSK = HashLen zero bytes (RFC 8446 7.1)
  derived := HkdfExpandLabel(FHash, early, 'derived', Hash(FHash, nil), HashSize(FHash));
  hs := HkdfExtract(FHash, derived, shared);
  th := TranscriptHash;
  cHs := HkdfExpandLabel(FHash, hs, 'c hs traffic', th, HashSize(FHash));
  sHs := HkdfExpandLabel(FHash, hs, 's hs traffic', th, HashSize(FHash));
  SetTraffic13(FRd, sHs);
  FResumed := pskUsed;
  // EncryptedExtensions
  if not NextHsMessage(mt, body, raw) or (mt <> HT_ENCRYPTED_EXTENSIONS) then
    Fail(AL_UNEXPECTED_MESSAGE, 'expected EncryptedExtensions');
  FTranscript := Concat(FTranscript, raw);
  R.Init(body);
  ee := R.Vec16;
  L.Init(ee);
  while L.Left > 0 do
  begin
    et := L.U16; body := L.Vec16;
    if (et = EXT_ALPN) and (Length(body) >= 3) then
    begin
      alpnB := Copy(body, 3, body[2]);
      SetString(FAlpnSel, PAnsiChar(@alpnB[0]), Length(alpnB));
    end;
  end;
  certReq := False;
  if not pskUsed then
  begin
    if not NextHsMessage(mt, body, raw) then Fail(AL_UNEXPECTED_MESSAGE, 'missing certificate');
    if mt = HT_CERTIFICATE_REQUEST then
    begin
      certReq := True;
      FTranscript := Concat(FTranscript, raw);
      R.Init(body);
      ctx := R.Vec8;
      if not NextHsMessage(mt, body, raw) then Fail(AL_UNEXPECTED_MESSAGE, 'missing certificate');
    end;
    if mt <> HT_CERTIFICATE then Fail(AL_UNEXPECTED_MESSAGE, 'expected Certificate');
    FTranscript := Concat(FTranscript, raw);
    R.Init(body);
    FPeerChain := ParseCertificateList(R, True);
    VerifyServerCertificate;
    // CertificateVerify
    th := TranscriptHash;
    if not NextHsMessage(mt, body, raw) or (mt <> HT_CERTIFICATE_VERIFY) then
      Fail(AL_UNEXPECTED_MESSAGE, 'expected CertificateVerify');
    R.Init(body);
    scheme := R.U16;
    sig := R.Vec16;
    if scheme = $0201 then Fail(AL_ILLEGAL_PARAMETER, 'rsa_pkcs1_sha1 is not allowed in TLS 1.3');
    if ((scheme = $0401) or (scheme = $0501) or (scheme = $0601)) then
      Fail(AL_ILLEGAL_PARAMETER, 'PKCS#1 signatures are not allowed in TLS 1.3 CertificateVerify');
    // in TLS 1.3 the ECDSA scheme binds the curve
    if ((scheme = $0403) and (FLeaf.Curve <> ecP256)) or ((scheme = $0503) and (FLeaf.Curve <> ecP384)) or
       ((scheme = $0603) and (FLeaf.Curve <> ecP521)) then
      Fail(AL_ILLEGAL_PARAMETER, 'ECDSA scheme does not match the key curve');
    SetLength(content, 64); FillChar(content[0], 64, $20);
    content := Concat(content, BytesOf('TLS 1.3, server CertificateVerify'), Concat(TBytes.Create(0), th));
    if not TlsVerifySignature(FLeaf, scheme, content, sig) then
      Fail(AL_DECRYPT_ERROR, 'invalid server signature (CertificateVerify)');
    FTranscript := Concat(FTranscript, raw);
  end;
  // server Finished
  th := TranscriptHash;
  if not NextHsMessage(mt, body, raw) or (mt <> HT_FINISHED) then Fail(AL_UNEXPECTED_MESSAGE, 'expected Finished');
  fk := HkdfExpandLabel(FHash, sHs, 'finished', nil, HashSize(FHash));
  if not SameBytesCT(body, Hmac(FHash, fk, th)) then Fail(AL_DECRYPT_ERROR, 'invalid server Finished');
  FTranscript := Concat(FTranscript, raw);
  // application secrets
  derived := HkdfExpandLabel(FHash, hs, 'derived', Hash(FHash, nil), HashSize(FHash));
  master := HkdfExtract(FHash, derived, zeros);
  th := TranscriptHash;
  FCAppSecret := HkdfExpandLabel(FHash, master, 'c ap traffic', th, HashSize(FHash));
  FSAppSecret := HkdfExpandLabel(FHash, master, 's ap traffic', th, HashSize(FHash));
  // client response: CCS (compatibility), [Certificate], Finished
  RawSend(TBytes.Create(RT_CCS, 3, 3, 0, 1, 1));
  SetTraffic13(FWr, cHs);
  if certReq then
  begin
    // no client certificate: empty list
    SendHandshake(HT_CERTIFICATE, Concat(TBytes.Create(Length(ctx)), ctx, TBytes.Create(0, 0, 0)));
  end;
  fk := HkdfExpandLabel(FHash, cHs, 'finished', nil, HashSize(FHash));
  vd := Hmac(FHash, fk, TranscriptHash);
  SendHandshake(HT_FINISHED, vd);
  FResMaster := HkdfExpandLabel(FHash, master, 'res master', TranscriptHash, HashSize(FHash));
  SetTraffic13(FWr, FCAppSecret);
  SetTraffic13(FRd, FSAppSecret);
  Wipe(hs); Wipe(master); Wipe(cHs); Wipe(sHs); Wipe(shared);
end;

procedure TXelSslClient.UpdateTraffic13(Read: Boolean);
begin
  if Read then
  begin
    FSAppSecret := HkdfExpandLabel(FHash, FSAppSecret, 'traffic upd', nil, HashSize(FHash));
    SetTraffic13(FRd, FSAppSecret);
  end
  else
  begin
    FCAppSecret := HkdfExpandLabel(FHash, FCAppSecret, 'traffic upd', nil, HashSize(FHash));
    SetTraffic13(FWr, FCAppSecret);
  end;
end;

procedure TXelSslClient.HandlePostHandshake(MsgType: Byte; const Body: TBytes);
var R: TReader; s: TXelSslSession; nonce: TBytes; req: Byte;
begin
  if FVersion = $0304 then
  begin
    case MsgType of
      HT_NEW_SESSION_TICKET:
        begin
          R.Init(Body);
          s := Default(TXelSslSession);
          s.Version := $0304; s.Suite := FSuite;
          s.Lifetime := R.U32; s.AgeAdd := R.U32;
          nonce := R.Vec8;
          s.Ticket := R.Vec16;
          R.Vec16;                                            // extensions (early_data) - ignored
          s.ReceivedMs := GetTickCount64;
          if (Cache <> nil) and (Length(s.Ticket) > 0) and (s.Lifetime > 0) then
          begin
            s.Secret := HkdfExpandLabel(FHash, FResMaster, 'resumption', nonce, HashSize(FHash));
            Cache.Put(CacheKeyName, s);
          end;
        end;
      HT_KEY_UPDATE:
        begin
          if Length(Body) <> 1 then Fail(AL_DECODE_ERROR, 'malformed KeyUpdate');
          req := Body[0];
          UpdateTraffic13(True);
          if req = 1 then
          begin
            SendHandshake(HT_KEY_UPDATE, TBytes.Create(0), False);
            UpdateTraffic13(False);
          end;
        end;
    else
      Fail(AL_UNEXPECTED_MESSAGE, 'unexpected post-handshake message');
    end;
  end
  else
  begin
    // TLS 1.2: HelloRequest = renegotiation request - refused with a warning
    if MsgType = HT_HELLO_REQUEST then SendAlert(1, AL_NO_RENEGOTIATION)
    else Fail(AL_UNEXPECTED_MESSAGE, 'renegotiation is not supported');
  end;
end;

// ---- TLS 1.2 ----

procedure TXelSslClient.HandshakeTls12(const SHBody: TBytes; const SHExt: TBytes; Resuming: Boolean);
var
  mt: Byte; body, raw, keyBlock, pms, params, sig, signed, srvPub, vd, ticket, keyC, keyS, ivC, ivS: TBytes;
  R: TReader; certReq, gotTicket: Boolean; scheme, grp: Word; ivLen: Integer; s: TXelSslSession;

  procedure DeriveKeys;
  begin
    if FChaCha then ivLen := 12 else ivLen := 4;
    keyBlock := Tls12Prf(FHash, FMaster, 'key expansion', Concat(FServerRandom, FClientRandom),
      2 * FKeyLen + 2 * ivLen);
    keyC := Copy(keyBlock, 0, FKeyLen);
    keyS := Copy(keyBlock, FKeyLen, FKeyLen);
    ivC := Copy(keyBlock, 2 * FKeyLen, ivLen);
    ivS := Copy(keyBlock, 2 * FKeyLen + ivLen, ivLen);
  end;

  procedure ReadServerFinished;
  var expected: TBytes; typ: Byte; data: TBytes;
  begin
    // optional NewSessionTicket before CCS
    gotTicket := False;
    // server CCS: switches the read keys
    while True do
    begin
      if Length(FHs) > 0 then
      begin
        if not NextHsMessage(mt, body, raw) then Fail(AL_UNEXPECTED_MESSAGE, 'missing Finished');
        if mt <> HT_NEW_SESSION_TICKET then Fail(AL_UNEXPECTED_MESSAGE, 'expected ChangeCipherSpec');
        FTranscript := Concat(FTranscript, raw);
        R.Init(body); R.U32; ticket := R.Vec16; gotTicket := True;
        Continue;
      end;
      if not ReadRecord(typ, data) then Fail(255, 'the server closed the connection');
      if typ = RT_HANDSHAKE then begin FHs := Concat(FHs, data); Continue; end;
      if typ = RT_ALERT then
      begin
        if Length(data) >= 2 then Fail(255, 'the server rejected the connection: alert ' + AlertName(data[1]));
        Fail(AL_DECODE_ERROR, 'malformed alert');
      end;
      if (typ <> RT_CCS) or (Length(data) <> 1) or (data[0] <> 1) then
        Fail(AL_UNEXPECTED_MESSAGE, 'expected ChangeCipherSpec');
      Break;
    end;
    SetCipher(FRd, keyS, ivS, False);
    expected := Tls12Prf(FHash, FMaster, 'server finished', TranscriptHash, 12);
    if not NextHsMessage(mt, body, raw) or (mt <> HT_FINISHED) then Fail(AL_UNEXPECTED_MESSAGE, 'expected Finished');
    if not SameBytesCT(body, expected) then Fail(AL_DECRYPT_ERROR, 'invalid server Finished');
    FTranscript := Concat(FTranscript, raw);
  end;

  procedure SendClientFinished;
  begin
    RawSend(TBytes.Create(RT_CCS, 3, 3, 0, 1, 1));
    SetCipher(FWr, keyC, ivC, False);
    vd := Tls12Prf(FHash, FMaster, 'client finished', TranscriptHash, 12);
    SendHandshake(HT_FINISHED, vd);
  end;

  procedure SaveSession;
  begin
    if Cache = nil then Exit;
    s := Default(TXelSslSession);
    s.Version := $0303; s.Suite := FSuite; s.Secret := Copy(FMaster); s.Ems := FEms;
    s.SessionId := Copy(FSessionId);
    if gotTicket then s.Ticket := ticket else if Resuming then s.Ticket := FOffered.Ticket;
    s.ReceivedMs := GetTickCount64;
    if (Length(s.SessionId) > 0) or (Length(s.Ticket) > 0) then Cache.Put(CacheKeyName, s);
  end;

begin
  if Resuming then
  begin
    // abbreviated handshake: server -> [NewSessionTicket] CCS Finished; client -> CCS Finished
    FMaster := Copy(FOffered.Secret);
    FEms := FOffered.Ems;
    DeriveKeys;
    ReadServerFinished;
    SendClientFinished;
    FResumed := True;
    SaveSession;
    Exit;
  end;
  // Certificate
  if not NextHsMessage(mt, body, raw) or (mt <> HT_CERTIFICATE) then Fail(AL_UNEXPECTED_MESSAGE, 'expected Certificate');
  FTranscript := Concat(FTranscript, raw);
  R.Init(body);
  FPeerChain := ParseCertificateList(R, False);
  VerifyServerCertificate;
  // ServerKeyExchange (ECDHE)
  if not NextHsMessage(mt, body, raw) or (mt <> HT_SERVER_KEY_EXCHANGE) then
    Fail(AL_HANDSHAKE_FAILURE, 'the server does not use ECDHE (no ServerKeyExchange)');
  FTranscript := Concat(FTranscript, raw);
  R.Init(body);
  if R.U8 <> 3 then Fail(AL_ILLEGAL_PARAMETER, 'unsupported curve type');
  grp := R.U16;
  if not IsOurGroup(grp) then
    Fail(AL_ILLEGAL_PARAMETER, Format('the server selected an unsupported curve 0x%.4x', [grp]));
  srvPub := R.Vec8;
  if (grp = GROUP_X25519) and (Length(srvPub) <> 32) then Fail(AL_ILLEGAL_PARAMETER, 'invalid server X25519 key');
  params := Copy(body, 0, R.P);
  scheme := R.U16;
  sig := R.Vec16;
  if not TlsSchemeSupported(scheme) then Fail(AL_ILLEGAL_PARAMETER, 'unsupported server signature scheme');
  if ((FSuite = $C02B) or (FSuite = $C02C) or (FSuite = $CCA9)) <> (FLeaf.KeyKind = kkEc) then
    Fail(AL_ILLEGAL_PARAMETER, 'certificate key type does not match the cipher suite');
  signed := Concat(FClientRandom, FServerRandom, params);
  if not TlsVerifySignature(FLeaf, scheme, signed, sig) then
    Fail(AL_DECRYPT_ERROR, 'invalid ServerKeyExchange signature');
  // [CertificateRequest] ServerHelloDone
  certReq := False;
  if not NextHsMessage(mt, body, raw) then Fail(AL_UNEXPECTED_MESSAGE, 'missing ServerHelloDone');
  if mt = HT_CERTIFICATE_REQUEST then
  begin
    certReq := True;
    FTranscript := Concat(FTranscript, raw);
    if not NextHsMessage(mt, body, raw) then Fail(AL_UNEXPECTED_MESSAGE, 'missing ServerHelloDone');
  end;
  if mt <> HT_SERVER_HELLO_DONE then Fail(AL_UNEXPECTED_MESSAGE, 'expected ServerHelloDone');
  FTranscript := Concat(FTranscript, raw);
  if certReq then SendHandshake(HT_CERTIFICATE, TBytes.Create(0, 0, 0));
  // ClientKeyExchange
  if grp <> GROUP_X25519 then
  begin
    EcdhKeyPair(NistCurve(grp), FPPriv, FPPub);
    if not EcdhShared(NistCurve(grp), FPPriv, srvPub, pms) then Fail(AL_ILLEGAL_PARAMETER, 'invalid server ECDHE key');
    SendHandshake(HT_CLIENT_KEY_EXCHANGE, Concat(TBytes.Create(Length(FPPub)), FPPub));
  end
  else
  begin
    pms := X25519(FPriv, srvPub);
    SendHandshake(HT_CLIENT_KEY_EXCHANGE, Concat(TBytes.Create(32), FPub));
  end;
  if FEms then
    FMaster := Tls12Prf(FHash, pms, 'extended master secret', TranscriptHash, 48)
  else
    FMaster := Tls12Prf(FHash, pms, 'master secret', Concat(FClientRandom, FServerRandom), 48);
  Wipe(pms);
  DeriveKeys;
  SendClientFinished;
  ReadServerFinished;
  SaveSession;
end;

// ---- handshake ----

function TXelSslClient.Handshake: Boolean;
var
  ch, body, raw, srvRand, sid, exts, ext, cookie, prefix, psk: TBytes;
  mt: Byte; R, L: TReader; suite, ver, et, grp: Word; hrr, ems, offered13, resuming12: Boolean;
  kl: Integer; cc, t13: Boolean; pskH: THashAlg;
begin
  Result := False;
  FLastError := '';
  try
    FClientRandom := RandomBytes(32);
    FSessionId := RandomBytes(32);              // middlebox compatibility (TLS 1.3)
    FPriv := RandomBytes(32);
    FPub := X25519Base(FPriv);
    FKsGroup := GROUP_X25519;
    offered13 := MaxVersion >= $0304;
    FHaveOffered := (Cache <> nil) and Cache.Get(CacheKeyName, FOffered);
    if FHaveOffered and (FOffered.Version = $0304) then
    begin
      // ticket expired or requiring an unavailable version
      if (not offered13) or (GetTickCount64 - FOffered.ReceivedMs > QWord(FOffered.Lifetime) * 1000) then
        FHaveOffered := False;
      Cache.Remove(CacheKeyName);               // TLS 1.3 tickets are single-use
    end;
    if FHaveOffered and (FOffered.Version = $0303) and (Length(FOffered.SessionId) > 0) then
      FSessionId := Copy(FOffered.SessionId);
    psk := nil;
    if FHaveOffered and (FOffered.Version = $0304) then psk := FOffered.Secret;
    hrr := False;
    cookie := nil; prefix := nil;
    ch := BuildClientHello(nil, nil);
    FTranscript := ch;
    SendRecord(RT_HANDSHAKE, ch);
    while True do
    begin
      if not NextHsMessage(mt, body, raw) or (mt <> HT_SERVER_HELLO) then
        Fail(AL_UNEXPECTED_MESSAGE, 'expected ServerHello');
      R.Init(body);
      ver := R.U16;
      srvRand := R.Take(32);
      sid := R.Vec8;
      suite := R.U16;
      if R.U8 <> 0 then Fail(AL_ILLEGAL_PARAMETER, 'the server selected compression');
      exts := nil;
      if R.Left > 0 then exts := R.Vec16;
      // supported_versions
      L.Init(exts);
      while L.Left > 0 do
      begin
        et := L.U16; ext := L.Vec16;
        if et = EXT_SUPPORTED_VERSIONS then
        begin
          if Length(ext) <> 2 then DecodeErr;
          ver := (ext[0] shl 8) or ext[1];
        end;
      end;
      if (ver <> $0304) and (ver <> $0303) then
        Fail(AL_PROTOCOL_VERSION, 'the server requires the obsolete version ' + TlsVersionName(ver) + ' (supported: TLS 1.2 and 1.3)');
      if (ver = $0304) and not offered13 then Fail(AL_PROTOCOL_VERSION, 'the server selected TLS 1.3, which was not offered');
      if not SuiteParams(suite, FHash, FKeyLen, FChaCha, t13) or (t13 <> (ver = $0304)) then
        Fail(AL_ILLEGAL_PARAMETER, 'the server selected a cipher suite that was not offered');
      FVersion := ver; FSuite := suite;
      if (ver = $0304) and SameBytesCT(srvRand, FromHex(HRR_RANDOM)) then
      begin
        // HelloRetryRequest
        if hrr then Fail(AL_UNEXPECTED_MESSAGE, 'second HelloRetryRequest');
        hrr := True;
        L.Init(exts);
        while L.Left > 0 do
        begin
          et := L.U16; ext := L.Vec16;
          if et = EXT_KEY_SHARE then
          begin
            if Length(ext) <> 2 then DecodeErr;
            grp := (ext[0] shl 8) or ext[1];
            if not IsOurGroup(grp) then
              Fail(AL_HANDSHAKE_FAILURE, Format('the server requires an unsupported group 0x%.4x', [grp]));
            if grp = FKsGroup then Fail(AL_ILLEGAL_PARAMETER, 'HelloRetryRequest for a group already sent');
            FKsGroup := grp;
            if grp <> GROUP_X25519 then EcdhKeyPair(NistCurve(grp), FPPriv, FPPub);
          end
          else if et = EXT_COOKIE then cookie := ext;
        end;
        // transcript: message_hash(CH1) + HRR
        prefix := Concat(TBytes.Create(HT_MESSAGE_HASH, 0, 0, HashSize(FHash)), Hash(FHash, FTranscript), raw);
        // a PSK with a different hash than the selected suite must be dropped (RFC 8446 4.1.4)
        if Length(psk) > 0 then
        begin
          SuiteParams(FOffered.Suite, pskH, kl, cc, t13);
          if pskH <> FHash then begin psk := nil; FHaveOffered := False; end;
        end;
        ch := BuildClientHello(cookie, prefix);
        FTranscript := Concat(prefix, ch);
        SendRecord(RT_HANDSHAKE, ch);
        Continue;
      end;
      Break;
    end;
    FServerRandom := srvRand;
    FTranscript := Concat(FTranscript, raw);
    if ver = $0304 then
    begin
      if not SameBytesCT(sid, FSessionId) then Fail(AL_ILLEGAL_PARAMETER, 'the server changed legacy_session_id');
      if Length(psk) > 0 then
      begin
        SuiteParams(FOffered.Suite, pskH, kl, cc, t13);
        if pskH <> FHash then psk := nil;              // PSK unusable with this hash
      end;
      HandshakeTls13(body, hrr, psk);
    end
    else
    begin
      // downgrade protection (RFC 8446 4.1.3)
      if offered13 and (SameBytesCT(Copy(srvRand, 24, 8), FromHex('444f574e47524401')) or
         SameBytesCT(Copy(srvRand, 24, 8), FromHex('444f574e47524400'))) then
        Fail(AL_ILLEGAL_PARAMETER, 'protocol downgrade attempt detected');
      ems := False;
      L.Init(exts);
      while L.Left > 0 do
      begin
        et := L.U16; ext := L.Vec16;
        if et = EXT_EMS then ems := True
        else if (et = EXT_ALPN) and (Length(ext) >= 3) then
          SetString(FAlpnSel, PAnsiChar(@ext[3]), ext[2])
        else if (et = EXT_RENEGOTIATION_INFO) and ((Length(ext) <> 1) or (ext[0] <> 0)) then
          Fail(AL_HANDSHAKE_FAILURE, 'invalid renegotiation_info');
      end;
      FEms := ems;
      // TLS 1.2 resumption: the server echoed our session ID (or accepted the ticket)
      resuming12 := FHaveOffered and (FOffered.Version = $0303) and (FOffered.Suite = suite) and
        (Length(sid) > 0) and SameBytesCT(sid, FSessionId) and (FOffered.Ems = ems);
      if not resuming12 and FHaveOffered and (FOffered.Version = $0303) and (Length(FOffered.Ticket) > 0) and
         (Length(sid) > 0) and SameBytesCT(sid, FSessionId) then
        resuming12 := (FOffered.Suite = suite) and (FOffered.Ems = ems);
      FSessionId := sid;
      HandshakeTls12(body, exts, resuming12);
    end;
    FConnected := True;
    Result := True;
    StartReader;
  except
    on E: ETlsError do
    begin
      FLastError := E.Message;
      if E.Alert <> 255 then SendAlert(2, E.Alert);
      FClosed := True;
    end;
    on E: Exception do
    begin
      FLastError := E.Message;
      SendAlert(2, AL_INTERNAL_ERROR);
      FClosed := True;
    end;
  end;
end;

// ---- application data ----

function TXelSslClient.Pending: Integer;
begin
  Result := FAppLen - FAppPos;
end;

function TXelSslClient.Read(var Buf; Len: Integer): Integer;
var typ, mt: Byte; data, body, raw: TBytes; n: Integer; rp: PByte;
begin
  Result := -1;
  if not FConnected then Exit;
  try
    while Pending = 0 do
    begin
      if FPeerClosed then Exit(0);
      // pending handshake messages (post-handshake)
      if Length(FHs) >= 4 then
      begin
        n := (FHs[1] shl 16) or (FHs[2] shl 8) or FHs[3];
        if Length(FHs) >= 4 + n then
        begin
          mt := FHs[0];
          body := Copy(FHs, 4, n);
          FHs := Copy(FHs, 4 + n, Length(FHs) - 4 - n);
          HandlePostHandshake(mt, body);
          Continue;
        end;
      end;
      FAppLen := 0; FAppPos := 0;
      if not ReadRecordView(typ, rp, n) then
      begin
        FPeerClosed := True;                 // EOF without close_notify
        Exit(0);
      end;
      if typ = RT_APP then
      begin
        // application data is read straight from the receive buffer
        FAppP := rp; FAppLen := n; FAppPos := 0;
        Continue;
      end;
      SetLength(data, n);
      if n > 0 then Move(rp^, data[0], n);
      case typ of
        RT_HANDSHAKE: FHs := Concat(FHs, data);
        RT_ALERT:
          begin
            if (Length(data) >= 2) and (data[1] = AL_CLOSE_NOTIFY) then
            begin
              FPeerClosed := True;
              Exit(0);
            end;
            if (Length(data) >= 2) and (data[0] = 1) then Continue;   // warning
            if Length(data) >= 2 then FLastError := 'the server terminated the connection: alert ' + AlertName(data[1]);
            FPeerClosed := True;
            Exit(-1);
          end;
        RT_CCS: Fail(AL_UNEXPECTED_MESSAGE, 'unexpected ChangeCipherSpec');
      end;
    end;
    n := Pending;
    if n > Len then n := Len;
    Move(FAppP[FAppPos], Buf, n);
    Inc(FAppPos, n);
    Result := n;
  except
    on E: ETlsError do
    begin
      FLastError := E.Message;
      if E.Alert <> 255 then SendAlert(2, E.Alert);
      FConnected := False;
      Result := -1;
    end;
  end;
end;

function TXelSslClient.Write(const Buf; Len: Integer): Integer;
begin
  Result := -1;
  if not FConnected or FClosed then Exit;
  if Len <= 0 then Exit(0);
  try
    SendRecordP(RT_APP, @Buf, Len);
    Result := Len;
  except
    on E: Exception do begin FLastError := E.Message; FConnected := False; end;
  end;
end;

procedure TXelSslClient.Close;
begin
  if FConnected and not FClosed then SendAlert(1, AL_CLOSE_NOTIFY);
  FClosed := True;
  StopReader;
end;

end.
