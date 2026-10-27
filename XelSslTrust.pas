// XelSSL - trusted certificate store.
// Windows: system stores ROOT (anchors) and CA (intermediates for path building),
//          excluding certificates in "Disallowed"; plus a fallback verification via the
//          system chain engine (CertGetCertificateChain + SSL policy) - it fetches
//          missing roots through Windows automatic root update.
// Unix/macOS/BSD/Android: SSL_CERT_FILE / SSL_CERT_DIR or well-known CA bundle paths.
// CryptoAPI declarations written from the Windows SDK documentation (wincrypt.h).
// License: MIT.
unit XelSslTrust;

{$mode objfpc}{$H+}

interface

uses
  SysUtils, Classes, StrUtils, SyncObjs, XelSslHash, XelSslX509;

type
  TTrustStore = class
  private
    FAnchors, FPool: TCertArray;
    FLock: SyncObjs.TCriticalSection;
  public
    constructor Create;
    destructor Destroy; override;
    procedure AddDer(const Der: TBytes; AsAnchor: Boolean = True);
    function AddPem(const Pem: RawByteString; AsAnchor: Boolean = True): Integer;   // number added
    function AddFile(const FileName: string; AsAnchor: Boolean = True): Integer;
    procedure LoadSystem;
    function Verify(const Chain: array of TBytes; const Host: string; out Err: string): TVerifyResult;
    property Anchors: TCertArray read FAnchors;
    property Pool: TCertArray read FPool;
  end;

// Shared system store (loaded on first use).
function SystemTrust: TTrustStore;

// Extracts DER certificates from PEM text.
function PemCertificates(const Pem: RawByteString): TBytesArray;

implementation

{$IFDEF MSWINDOWS}
uses Windows;

// ---- crypt32.dll (Windows SDK: wincrypt.h) ----

const
  Crypt32Dll = 'crypt32.dll';
  EncodingX509Pkcs7 = $00000001 or $00010000;     // X509_ASN_ENCODING | PKCS_7_ASN_ENCODING
  StoreProvMemory = PAnsiChar(2);                // CERT_STORE_PROV_MEMORY
  StoreAddAlways = 4;                            // CERT_STORE_ADD_ALWAYS
  UsageMatchAnd = 0;                             // USAGE_MATCH_TYPE_AND
  AuthTypeServer = 2;                            // AUTHTYPE_SERVER
  ChainPolicySsl = PAnsiChar(4);                 // CERT_CHAIN_POLICY_SSL
  OidServerAuth: PAnsiChar = '1.3.6.1.5.5.7.3.1';

type
  TStoreHandle = Pointer;
  // CERT_CONTEXT
  PCertCtx = ^TCertCtx;
  TCertCtx = record
    EncodingType: DWORD;
    Encoded: PByte;
    EncodedLen: DWORD;
    Info: Pointer;
    Store: TStoreHandle;
  end;
  // CERT_ENHKEY_USAGE
  TEnhKeyUsage = record
    Count: DWORD;
    Oids: PPAnsiChar;
  end;
  // CERT_USAGE_MATCH
  TUsageMatch = record
    MatchType: DWORD;
    Usage: TEnhKeyUsage;
  end;
  // CERT_CHAIN_PARA (the nested records keep the C alignment: 32 bytes on x64)
  TChainPara = record
    Size: DWORD;
    RequestedUsage: TUsageMatch;
  end;
  // SSL_EXTRA_CERT_CHAIN_POLICY_PARA
  TSslPolicyExtra = record
    Size: DWORD;
    AuthType: DWORD;
    Checks: DWORD;
    ServerName: PWideChar;
  end;
  // CERT_CHAIN_POLICY_PARA
  TPolicyPara = record
    Size: DWORD;
    Flags: DWORD;
    Extra: Pointer;
  end;
  // CERT_CHAIN_POLICY_STATUS
  TPolicyStatus = record
    Size: DWORD;
    Error: DWORD;
    ChainIndex: LongInt;
    ElementIndex: LongInt;
    Extra: Pointer;
  end;

function CertOpenSystemStoreW(Prov: Pointer; Name: PWideChar): TStoreHandle;
  stdcall; external Crypt32Dll;
function CertOpenStore(Provider: PAnsiChar; Encoding: DWORD; Prov: Pointer; Flags: DWORD;
  Para: Pointer): TStoreHandle; stdcall; external Crypt32Dll;
function CertCloseStore(Store: TStoreHandle; Flags: DWORD): BOOL; stdcall; external Crypt32Dll;
function CertEnumCertificatesInStore(Store: TStoreHandle; Prev: PCertCtx): PCertCtx;
  stdcall; external Crypt32Dll;
function CertCreateCertificateContext(Encoding: DWORD; Data: PByte; Len: DWORD): PCertCtx;
  stdcall; external Crypt32Dll;
function CertFreeCertificateContext(Ctx: PCertCtx): BOOL; stdcall; external Crypt32Dll;
function CertAddEncodedCertificateToStore(Store: TStoreHandle; Encoding: DWORD; Data: PByte;
  Len: DWORD; Disposition: DWORD; OutCtx: Pointer): BOOL; stdcall; external Crypt32Dll;
function CertGetCertificateChain(Engine: Pointer; Ctx: PCertCtx; Time: Pointer; Extra: TStoreHandle;
  const Para: TChainPara; Flags: DWORD; Reserved: Pointer; out Chain: Pointer): BOOL;
  stdcall; external Crypt32Dll;
procedure CertFreeCertificateChain(Chain: Pointer); stdcall; external Crypt32Dll;
function CertVerifyCertificateChainPolicy(Policy: PAnsiChar; Chain: Pointer; const Para: TPolicyPara;
  var Status: TPolicyStatus): BOOL; stdcall; external Crypt32Dll;

// DER copies of all certificates in a system store ('ROOT', 'CA', 'Disallowed')
function StoreCertificates(const Name: UnicodeString): TBytesArray;
var st: TStoreHandle; ctx: PCertCtx; n: Integer;
begin
  Result := nil;
  st := CertOpenSystemStoreW(nil, PWideChar(Name));
  if st = nil then Exit;
  n := 0;
  ctx := CertEnumCertificatesInStore(st, nil);
  while ctx <> nil do
  begin
    if (ctx^.Encoded <> nil) and (ctx^.EncodedLen > 0) then
    begin
      if n = Length(Result) then SetLength(Result, n * 2 + 32);
      SetLength(Result[n], ctx^.EncodedLen);
      Move(ctx^.Encoded^, Result[n][0], ctx^.EncodedLen);
      Inc(n);
    end;
    ctx := CertEnumCertificatesInStore(st, ctx);    // frees the previous context
  end;
  CertCloseStore(st, 0);
  SetLength(Result, n);
end;

// Asks the Windows chain engine: path to a trusted root (it may download missing
// roots) + SSL server policy (serverAuth usage, host name, validity).
function OsVerify(const Chain: array of TBytes; const Host: string): Boolean;
var
  leaf: PCertCtx; extra: TStoreHandle; chainCtx: Pointer; i: Integer; oid: PAnsiChar;
  para: TChainPara; sslExtra: TSslPolicyExtra; policy: TPolicyPara; status: TPolicyStatus;
  name: UnicodeString;
begin
  Result := False;
  if (Length(Chain) = 0) or (Length(Chain[0]) = 0) then Exit;
  leaf := CertCreateCertificateContext(EncodingX509Pkcs7, @Chain[0][0], Length(Chain[0]));
  if leaf = nil then Exit;
  chainCtx := nil;
  extra := CertOpenStore(StoreProvMemory, EncodingX509Pkcs7, nil, 0, nil);
  try
    // the intermediates sent by the server
    if extra <> nil then
      for i := 1 to High(Chain) do
        if Length(Chain[i]) > 0 then
          CertAddEncodedCertificateToStore(extra, EncodingX509Pkcs7, @Chain[i][0], Length(Chain[i]),
            StoreAddAlways, nil);
    oid := OidServerAuth;
    para := Default(TChainPara);
    para.Size := SizeOf(para);
    para.RequestedUsage.MatchType := UsageMatchAnd;
    para.RequestedUsage.Usage.Count := 1;
    para.RequestedUsage.Usage.Oids := @oid;
    if not CertGetCertificateChain(nil, leaf, nil, extra, para, 0, nil, chainCtx) then Exit;
    name := UnicodeString(Host);
    sslExtra := Default(TSslPolicyExtra);
    sslExtra.Size := SizeOf(sslExtra);
    sslExtra.AuthType := AuthTypeServer;
    if name <> '' then sslExtra.ServerName := PWideChar(name);
    policy := Default(TPolicyPara);
    policy.Size := SizeOf(policy);
    policy.Extra := @sslExtra;
    status := Default(TPolicyStatus);
    status.Size := SizeOf(status);
    Result := CertVerifyCertificateChainPolicy(ChainPolicySsl, chainCtx, policy, status) and (status.Error = 0);
  finally
    if chainCtx <> nil then CertFreeCertificateChain(chainCtx);
    if extra <> nil then CertCloseStore(extra, 0);
    CertFreeCertificateContext(leaf);
  end;
end;
{$ENDIF}

// ---- PEM ----

function PemCertificates(const Pem: RawByteString): TBytesArray;
const
  BeginTag = '-----BEGIN CERTIFICATE-----';
  EndTag = '-----END CERTIFICATE-----';
  B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';
var
  p, e, i, v, bits, n, idx: Integer; acc: UInt32; der: TBytes; c: AnsiChar;
begin
  Result := nil;
  p := Pos(BeginTag, Pem);
  while p > 0 do
  begin
    e := PosEx(EndTag, Pem, p);
    if e = 0 then Break;
    SetLength(der, (e - p) * 3 div 4 + 3);
    n := 0; acc := 0; bits := 0;
    for i := p + Length(BeginTag) to e - 1 do
    begin
      c := Pem[i];
      idx := Pos(c, B64);
      if idx = 0 then Continue;                   // skip whitespace and '='
      v := idx - 1;
      acc := (acc shl 6) or UInt32(v);
      Inc(bits, 6);
      if bits >= 8 then
      begin
        Dec(bits, 8);
        der[n] := Byte(acc shr bits);
        Inc(n);
      end;
    end;
    SetLength(der, n);
    SetLength(Result, Length(Result) + 1);
    Result[High(Result)] := der;
    p := PosEx(BeginTag, Pem, e);
  end;
end;

// ---- TTrustStore ----

constructor TTrustStore.Create;
begin
  inherited Create;
  FLock := SyncObjs.TCriticalSection.Create;
end;

destructor TTrustStore.Destroy;
begin
  FLock.Free;
  inherited Destroy;
end;

procedure TTrustStore.AddDer(const Der: TBytes; AsAnchor: Boolean);
var c: TCert;
begin
  if not ParseCert(Der, c) then Exit;
  FLock.Enter;
  try
    if AsAnchor then
    begin
      SetLength(FAnchors, Length(FAnchors) + 1);
      FAnchors[High(FAnchors)] := c;
    end
    else
    begin
      SetLength(FPool, Length(FPool) + 1);
      FPool[High(FPool)] := c;
    end;
  finally
    FLock.Leave;
  end;
end;

function TTrustStore.AddPem(const Pem: RawByteString; AsAnchor: Boolean): Integer;
var certs: TBytesArray; i: Integer;
begin
  certs := PemCertificates(Pem);
  for i := 0 to High(certs) do AddDer(certs[i], AsAnchor);
  Result := Length(certs);
end;

function TTrustStore.AddFile(const FileName: string; AsAnchor: Boolean): Integer;
var fs: TFileStream; s: RawByteString; b: TBytes;
begin
  Result := 0;
  if not FileExists(FileName) then Exit;
  fs := TFileStream.Create(FileName, fmOpenRead or fmShareDenyNone);
  try
    SetLength(s, fs.Size);
    if fs.Size > 0 then fs.ReadBuffer(s[1], fs.Size);
  finally
    fs.Free;
  end;
  if Pos('-----BEGIN', s) > 0 then Result := AddPem(s, AsAnchor)
  else if Length(s) > 0 then
  begin
    SetLength(b, Length(s));
    Move(s[1], b[0], Length(s));
    AddDer(b, AsAnchor);
    Result := 1;
  end;
end;

procedure TTrustStore.LoadSystem;
{$IFDEF MSWINDOWS}
var bad: TBytesArray;

  function Distrusted(const Der: TBytes): Boolean;
  var k: Integer;
  begin
    for k := 0 to High(bad) do
      if SameBytesCT(Der, bad[k]) then Exit(True);
    Result := False;
  end;

  procedure AddStore(const Name: UnicodeString; AsAnchor: Boolean);
  var certs: TBytesArray; k: Integer;
  begin
    certs := StoreCertificates(Name);
    for k := 0 to High(certs) do
      if not Distrusted(certs[k]) then AddDer(certs[k], AsAnchor);
  end;

begin
  bad := StoreCertificates('Disallowed');
  AddStore('ROOT', True);
  AddStore('CA', False);                         // intermediates - only for path building
end;
{$ELSE}
const
  // CA bundles (one PEM file), in the order they are tried
  Bundles: array[0..9] of string = (
    '/etc/ssl/certs/ca-certificates.crt',                  // Debian, Ubuntu, Arch, Gentoo
    '/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem',   // Fedora, RHEL 7+
    '/etc/pki/tls/certs/ca-bundle.crt',                    // older Red Hat / CentOS
    '/var/lib/ca-certificates/ca-bundle.pem',              // openSUSE, SLES
    '/etc/ssl/ca-bundle.pem',                              // older openSUSE
    '/etc/ssl/cert.pem',                                   // macOS, Alpine, OpenBSD, NetBSD
    '/usr/local/etc/ssl/cert.pem',                         // FreeBSD
    '/usr/local/share/certs/ca-root-nss.crt',              // FreeBSD (ca_root_nss)
    '/etc/certs/ca-certificates.crt',                      // Solaris
    '/usr/share/ca-certificates/cacert.pem');              // misc.
  // directories with one certificate per file
  CertDirs: array[0..3] of string = (
    '/etc/ssl/certs', '/system/etc/security/cacerts', '/etc/pki/tls/certs', '/etc/openssl/certs');

  function LoadDir(const Dir: string): Integer;
  var sr: TSearchRec; base: string;
  begin
    Result := 0;
    base := IncludeTrailingPathDelimiter(Dir);
    if FindFirst(base + '*', faAnyFile, sr) <> 0 then Exit;
    repeat
      if (sr.Attr and faDirectory) = 0 then Inc(Result, AddFile(base + sr.Name));
    until FindNext(sr) <> 0;
    FindClose(sr);
  end;

var i: Integer; env: string;
begin
  // OpenSSL conventions first
  env := GetEnvironmentVariable('SSL_CERT_FILE');
  if (env <> '') and (AddFile(env) > 0) then Exit;
  env := GetEnvironmentVariable('SSL_CERT_DIR');
  if (env <> '') and (LoadDir(env) > 0) then Exit;
  for i := 0 to High(Bundles) do
    if AddFile(Bundles[i]) > 0 then Exit;
  for i := 0 to High(CertDirs) do
    if DirectoryExists(CertDirs[i]) and (LoadDir(CertDirs[i]) > 0) then Exit;
end;
{$ENDIF}

function TTrustStore.Verify(const Chain: array of TBytes; const Host: string; out Err: string): TVerifyResult;
var a, p: TCertArray;
begin
  FLock.Enter;
  try a := FAnchors; p := FPool; finally FLock.Leave; end;
  Result := VerifyChain(Chain, Host, a, p, NowUtc, Err);
  {$IFDEF MSWINDOWS}
  // no known root: Windows may not have it in the store yet (it fetches roots
  // while building chains) - ask the system engine, which also checks the host name
  if (Result = vrUnknownCA) and (Self = SystemTrust) and OsVerify(Chain, Host) then
  begin
    Result := vrOk; Err := '';
  end;
  {$ENDIF}
end;

var
  GSystem: TTrustStore = nil;
  GSysLock: SyncObjs.TCriticalSection;

function SystemTrust: TTrustStore;
begin
  if GSystem = nil then
  begin
    GSysLock.Enter;
    try
      if GSystem = nil then
      begin
        Result := TTrustStore.Create;
        Result.LoadSystem;
        GSystem := Result;
      end;
    finally
      GSysLock.Leave;
    end;
  end;
  Result := GSystem;
end;

initialization
  GSysLock := SyncObjs.TCriticalSection.Create;
finalization
  FreeAndNil(GSystem);
  FreeAndNil(GSysLock);
end.
