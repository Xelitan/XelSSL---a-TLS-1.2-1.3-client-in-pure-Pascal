// XelSSL - CPU feature detection for the optional assembler code paths.
//
// The assembler routines are an addition: they exist only on x86-64 and are used only
// when CPUID reports the instructions they need. Every algorithm also has a Pascal
// implementation, which is used on all other platforms (and when XelSslAsm = False).
// License: MIT.
unit XelSslCpu;

{$mode objfpc}{$H+}
{$IFDEF CPUX86_64}
  {$asmmode intel}
  {$DEFINE XELSSL_X64}
{$ENDIF}

interface

type
  TCpuFeature = (cfSse2, cfSsse3, cfSse41, cfAesNi, cfPclmul, cfShaNi, cfBmi2, cfAdx, cfAvx,
    cfAvx2, cfVaes, cfVpclmul);
  TCpuFeatures = set of TCpuFeature;

var
  // what the processor supports (empty on non-x86-64 platforms)
  CpuFeatures: TCpuFeatures = [];
  // master switch: False = Pascal code everywhere (tests compare both)
  XelSslAsm: Boolean = True;

// True if the assembler path needing Need may run now.
function AsmAvailable(Need: TCpuFeatures): Boolean; inline;

implementation

function AsmAvailable(Need: TCpuFeatures): Boolean;
begin
  {$IFDEF XELSSL_X64}
  Result := XelSslAsm and (Need <= CpuFeatures);
  {$ELSE}
  Result := False;
  {$ENDIF}
end;

{$IFDEF XELSSL_X64}
procedure Cpuid(Leaf, Sub: UInt32; out A, B, C, D: UInt32);
var ra, rb, rc, rd: UInt32;
begin
  asm
    push rbx
    mov eax, Leaf
    mov ecx, Sub
    cpuid
    mov ra, eax
    mov rb, ebx
    mov rc, ecx
    mov rd, edx
    pop rbx
  end ['rax', 'rcx', 'rdx'];
  A := ra; B := rb; C := rc; D := rd;
end;

// XCR0 (which register states the operating system saves)
function XGetBv0: UInt32;
var r: UInt32;
begin
  asm
    xor ecx, ecx
    xgetbv
    mov r, eax
  end ['rax', 'rcx', 'rdx'];
  Result := r;
end;

procedure Detect;
var a, b, c, d, maxLeaf: UInt32; osYmm: Boolean;
begin
  Cpuid(0, 0, maxLeaf, b, c, d);
  if maxLeaf < 1 then Exit;
  Cpuid(1, 0, a, b, c, d);
  CpuFeatures := [cfSse2];                       // part of x86-64
  if c and (1 shl 9) <> 0 then Include(CpuFeatures, cfSsse3);
  if c and (1 shl 19) <> 0 then Include(CpuFeatures, cfSse41);
  if c and (1 shl 25) <> 0 then Include(CpuFeatures, cfAesNi);
  if c and (1 shl 1) <> 0 then Include(CpuFeatures, cfPclmul);
  // AVX registers usable: OSXSAVE set and the OS saves the xmm and ymm state
  osYmm := (c and (1 shl 27) <> 0) and (XGetBv0 and 6 = 6);
  if osYmm and (c and (1 shl 28) <> 0) then Include(CpuFeatures, cfAvx);
  if maxLeaf >= 7 then
  begin
    Cpuid(7, 0, a, b, c, d);
    if b and (1 shl 29) <> 0 then Include(CpuFeatures, cfShaNi);
    if b and (1 shl 8) <> 0 then Include(CpuFeatures, cfBmi2);
    if b and (1 shl 19) <> 0 then Include(CpuFeatures, cfAdx);
    if osYmm and (b and (1 shl 5) <> 0) then Include(CpuFeatures, cfAvx2);
    // AES and carry-less multiplication on whole ymm registers (2 blocks per instruction)
    if osYmm and (c and (1 shl 9) <> 0) then Include(CpuFeatures, cfVaes);
    if osYmm and (c and (1 shl 10) <> 0) then Include(CpuFeatures, cfVpclmul);
  end;
end;
{$ENDIF}

initialization
  {$IFDEF XELSSL_X64}
  Detect;
  {$ENDIF}
end.
