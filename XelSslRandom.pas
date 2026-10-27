// XelSSL - cryptographically secure random numbers from the OS.
// Windows: BCryptGenRandom (system CSPRNG). Unix/macOS/BSD: /dev/urandom.
// License: MIT.
unit XelSslRandom;

{$mode objfpc}{$H+}

interface

uses
  SysUtils;

function RandomBytes(N: Integer): TBytes;

implementation

{$IFDEF MSWINDOWS}
const
  BCRYPT_USE_SYSTEM_PREFERRED_RNG = 2;

function BCryptGenRandom(hAlgorithm: Pointer; pbBuffer: PByte; cbBuffer: Cardinal;
  dwFlags: Cardinal): LongInt; stdcall; external 'bcrypt.dll';

function RandomBytes(N: Integer): TBytes;
begin
  SetLength(Result, N);
  if N = 0 then Exit;
  if BCryptGenRandom(nil, @Result[0], N, BCRYPT_USE_SYSTEM_PREFERRED_RNG) <> 0 then
    raise Exception.Create('XelSSL: BCryptGenRandom failed');
end;
{$ELSE}
uses BaseUnix;

function RandomBytes(N: Integer): TBytes;
var fd: cint; got, r: Integer;
begin
  SetLength(Result, N);
  if N = 0 then Exit;
  fd := FpOpen('/dev/urandom', O_RDONLY);
  if fd < 0 then raise Exception.Create('XelSSL: /dev/urandom not available');
  try
    got := 0;
    while got < N do
    begin
      r := FpRead(fd, Result[got], N - got);
      if r <= 0 then raise Exception.Create('XelSSL: error reading /dev/urandom');
      Inc(got, r);
    end;
  finally
    FpClose(fd);
  end;
end;
{$ENDIF}

end.
