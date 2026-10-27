// XelSSL - ECDH on the NIST curves P-256 / P-384 / P-521 (TLS key exchange) and the
// point computation for ECDSA verification (EcVerifyCombination).
// Constant-time arithmetic: 32-bit limbs (8/12/17), Montgomery multiplication
// (CIOS; for all three p = -1 mod 2^32, so -p^-1 mod 2^32 = 1), conditional
// subtraction via masks, Montgomery ladder with branch-free swaps.
// Jacobian coordinates, a = -3. Curve parameters: XelSslCurves.
// x86-64 assembler addition: Montgomery multiplication on 64-bit limbs (MUL 64 x 64 ->
// 128); the limb counts (8 / 12 / 18 x 32 bits) are even, so both implementations use
// the same Montgomery radix R = 2^(32 * limbs). P-256 on x86-64 has its own path:
// 4 x 64-bit field elements with a dedicated multiplication (XelSslP256Mul.inc), scalar
// multiplication in fixed 4-bit windows with constant-time table selection (the scalar
// is k + n with its top bit set, so the additions never meet equal points), and the
// verification with wNAF-5 Straus on the same arithmetic. License: MIT.
unit XelSslEcdh;

{$mode objfpc}{$H+}{$Q-}{$R-}
{$IFDEF CPUX86_64}
  {$asmmode intel}
  {$DEFINE XELSSL_X64}
{$ENDIF}

interface

uses
  SysUtils;

type
  TEcdhCurve = (ecdhP256, ecdhP384, ecdhP521);

// New key pair: Priv = scalar (Len bytes), Pub = 04||X||Y.
procedure EcdhKeyPair(Curve: TEcdhCurve; out Priv, Pub: TBytes);
// Shared secret = X coordinate. False if the peer's point is invalid.
function EcdhShared(Curve: TEcdhCurve; const Priv, PeerPub: TBytes; out Secret: TBytes): Boolean;
// Public key for a given scalar (tests).
function EcdhPublicOf(Curve: TEcdhCurve; const Priv: TBytes): TBytes;
function EcdhCoordLen(Curve: TEcdhCurve): Integer;
// ECDSA verification core: True if x(U1*G + U2*Q) mod n = R (all big-endian; Pub =
// 04||X||Y, checked to lie on the curve). Public data only - not constant time.
function EcVerifyCombination(Curve: TEcdhCurve; const Pub, U1, U2, R: TBytes): Boolean;

var
  // use the assembler addition when the CPU allows it (tests switch it off)
  EcdhUseAsm: Boolean = True;
  // P-256 multiplication with MULX/ADCX/ADOX when the CPU has BMI2 + ADX (tests switch it off)
  EcdhUseMulx: Boolean = True;
  // with MULX: the whole P-256 window loop in assembler (False: the Pascal loop over the
  // assembler point operations; tests compare both)
  P256AsmLoop: Boolean = True;
  // P-256 with MULX: k * G (key pairs) and u1 * G (verification) from a fixed table of
  // affine multiples of G (built on first use, ~0.3 ms); verification takes u2 * Q in the
  // assembler window loop. False: the general loops (tests compare both)
  P256UseGTab: Boolean = True;

// Order n of the base point (big-endian, minimal length) - for ECDSA signing.
function EcdhOrder(Curve: TEcdhCurve): TBytes;

implementation

uses XelSslRandom, XelSslBigNum, XelSslCurves, XelSslCpu;

const
  MAXL = 18;

type
  TFe = array[0..MAXL - 1] of UInt32;      // little-endian; NL limbs used
  TPt = record X, Y, Z: TFe; end;
  TCtx = record
    NL, Len, NBits: Integer;               // limbs, coordinate bytes, bits of the order n
    M64: UInt64;                           // -p^-1 mod 2^64 (64-bit Montgomery)
    P, R2, OneM, BM, GX, GY: TFe;
    N: TBig;
    Ready: Boolean;
  end;

var
  Ctxs: array[TEcdhCurve] of TCtx;

const
  // index into XelSslCurves.CurveParams
  CurveIdx: array[TEcdhCurve] of Integer = (CURVE_P256, CURVE_P384, CURVE_P521);

// ---- conversions ----

procedure FeFromBig(const C: TCtx; out R: TFe; const B: TBig);
var i: Integer;
begin
  FillChar(R, SizeOf(R), 0);
  for i := 0 to C.NL - 1 do
    if i < Length(B) then R[i] := B[i];
end;

function FeToBig(const C: TCtx; const A: TFe): TBig;
var i, n: Integer;
begin
  SetLength(Result, C.NL);
  for i := 0 to C.NL - 1 do Result[i] := A[i];
  n := C.NL;
  while (n > 0) and (Result[n - 1] = 0) do Dec(n);
  SetLength(Result, n);
end;

// ---- arithmetic mod p (constant time; loops depend only on NL) ----

procedure FeReduceOnce(const C: TCtx; var A: TFe; Hi: UInt32);
var t: TFe; i: Integer; d: Int64; borrow, mask: UInt32;
begin
  borrow := 0;
  for i := 0 to C.NL - 1 do
  begin
    d := Int64(A[i]) - C.P[i] - borrow;
    t[i] := UInt32(d);
    borrow := UInt32(QWord(d) shr 63);
  end;
  mask := UInt32(0) - ((Hi or (borrow xor 1)) and 1);
  for i := 0 to C.NL - 1 do A[i] := (t[i] and mask) or (A[i] and not mask);
end;

{$IFDEF XELSSL_X64}
// P-384 field kernels (test/gen_p384_asm.py), 6 x 64-bit limbs = the 12 x 32-bit limbs
// of the generic code (the same Montgomery radix R = 2^384); results fully reduced.
// Called without a stack frame: rax = R, rcx = A, rdx = B.
procedure P384MulxAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP384Mulx.inc}
end;

procedure P384AddAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP384Add.inc}
end;

procedure P384SubAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP384Sub.inc}
end;

var
  HaveP384x: Boolean;              // BMI2 + ADX (set at start-up)

function P384Fast(const C: TCtx): Boolean; inline;
begin
  Result := (C.NL = 12) and HaveP384x and EcdhUseAsm and EcdhUseMulx;
end;
{$ENDIF}

procedure FeAdd(const C: TCtx; out R: TFe; const A, B: TFe);
var i: Integer; cy: UInt64;
begin
  {$IFDEF XELSSL_X64}
  if P384Fast(C) then begin P384AddAsm(@R[0], @A[0], @B[0]); Exit; end;
  {$ENDIF}
  cy := 0;
  for i := 0 to C.NL - 1 do
  begin
    cy := cy + A[i] + B[i];
    R[i] := UInt32(cy);
    cy := cy shr 32;
  end;
  FeReduceOnce(C, R, UInt32(cy));
end;

procedure FeSub(const C: TCtx; out R: TFe; const A, B: TFe);
var i: Integer; d: Int64; borrow, mask: UInt32; cy: UInt64;
begin
  {$IFDEF XELSSL_X64}
  if P384Fast(C) then begin P384SubAsm(@R[0], @A[0], @B[0]); Exit; end;
  {$ENDIF}
  borrow := 0;
  for i := 0 to C.NL - 1 do
  begin
    d := Int64(A[i]) - B[i] - borrow;
    R[i] := UInt32(d);
    borrow := UInt32(QWord(d) shr 63);
  end;
  mask := UInt32(0) - borrow;
  cy := 0;
  for i := 0 to C.NL - 1 do
  begin
    cy := cy + R[i] + (C.P[i] and mask);
    R[i] := UInt32(cy);
    cy := cy shr 32;
  end;
end;

{$IFDEF XELSSL_X64}
// Montgomery multiplication on N 64-bit limbs (CIOS): T := A*B*2^(-64*N), T < 2p,
// T[N] = the carry out (0 or 1). M = -p^-1 mod 2^64.
procedure HwMontMul(T, A, B, P: PUInt64; N: Integer; M: UInt64);
var pt, pa, pb, pp: Pointer; cnt: PtrInt; mm: UInt64;
begin
  pt := T; pa := A; pb := B; pp := P; cnt := N; mm := M;
  asm
    mov rax, pt
    mov rcx, pa
    mov rdx, pb
    mov r8, pp
    mov r9, cnt
    mov r10, mm
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    mov rbx, rax                             // t
    mov rsi, rcx                             // a
    mov rdi, rdx                             // b
    // t[0..n+1] := 0
    xor rax, rax
    lea rcx, [r9 + 2]
    mov rdx, rbx
  @zero:
    mov [rdx], rax
    add rdx, 8
    dec rcx
    jnz @zero
    xor r11, r11                             // i
  @outer:
    cmp r11, r9
    jae @finish
    mov r14, [rdi + r11 * 8]                 // b[i]
    xor r13, r13                             // carry
    xor r12, r12                             // j
  @mulloop:
    mov rax, [rsi + r12 * 8]
    mul r14
    add rax, [rbx + r12 * 8]
    adc rdx, 0
    add rax, r13
    adc rdx, 0
    mov [rbx + r12 * 8], rax
    mov r13, rdx
    inc r12
    cmp r12, r9
    jb @mulloop
    // t[n] += carry, t[n+1] = carry out
    xor rdx, rdx
    add r13, [rbx + r9 * 8]
    adc rdx, 0
    mov [rbx + r9 * 8], r13
    mov [rbx + r9 * 8 + 8], rdx
    // m = t[0] * M; t := (t + m*p) / 2^64
    mov r15, [rbx]
    imul r15, r10
    mov rax, r15
    mul qword ptr [r8]
    add rax, [rbx]
    adc rdx, 0
    mov r13, rdx                             // carry
    mov r12, 1
  @redloop:
    cmp r12, r9
    jae @redend
    mov rax, r15
    mul qword ptr [r8 + r12 * 8]
    add rax, [rbx + r12 * 8]
    adc rdx, 0
    add rax, r13
    adc rdx, 0
    mov [rbx + r12 * 8 - 8], rax
    mov r13, rdx
    inc r12
    jmp @redloop
  @redend:
    xor rdx, rdx
    add r13, [rbx + r9 * 8]
    adc rdx, 0
    mov [rbx + r9 * 8 - 8], r13
    add rdx, [rbx + r9 * 8 + 8]
    mov [rbx + r9 * 8], rdx
    inc r11
    jmp @outer
  @finish:
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11'];
end;
{$ENDIF}

{$IFDEF XELSSL_X64}
// P-256 field kernels (test/gen_p256_asm.py), called without a stack frame: the
// arguments are moved from the ABI registers to rax = R, rcx = A, rdx = B. R may be A or
// B (all inputs are read before the result is written). Results are fully reduced.
procedure P256MulAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP256Mul.inc}
end;

// the same with MULX/ADCX/ADOX (BMI2 + ADX)
procedure P256MulxAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP256Mulx.inc}
end;

procedure P256AddAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP256Add.inc}
end;

procedure P256SubAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP256Sub.inc}
end;

// R := A^2 (MULX/ADCX/ADOX)
procedure P256SqrxAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP256Sqrx.inc}
end;

// R := Table[Idx] for Idx 1..15 (Table = entry 1), zeros for 0; constant time
procedure P256SelectAsm(R, Table: Pointer; Idx: PtrUInt); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslP256Select.inc}
end;

var
  HaveMulx: Boolean;                 // BMI2 + ADX (set at start-up)

procedure HwP256Mul(R, A, B: Pointer); inline;
begin
  if HaveMulx and EcdhUseMulx then P256MulxAsm(R, A, B) else P256MulAsm(R, A, B);
end;
{$ENDIF}

// Montgomery: R := A*B*2^(-32*NL) mod p
procedure FeMul(const C: TCtx; out R: TFe; const A, B: TFe);
var t: array[0..MAXL + 1] of UInt32; i, j, nl: Integer; cy: UInt64; m: UInt32;
  {$IFDEF XELSSL_X64}t64: array[0..MAXL div 2 + 2] of UInt64;{$ENDIF}
begin
  {$IFDEF XELSSL_X64}
  // P-384 (12 limbs): the dedicated MULX multiplication, fully reduced
  if P384Fast(C) then
  begin
    P384MulxAsm(@R[0], @A[0], @B[0]);
    Exit;
  end;
  // P-256 (8 limbs): the same radix R = 2^256 with the dedicated multiplication
  if (C.NL = 8) and EcdhUseAsm and AsmAvailable([cfSse2]) then
  begin
    HwP256Mul(@R[0], @A[0], @B[0]);
    Exit;
  end;
  if EcdhUseAsm and AsmAvailable([cfSse2]) then
  begin
    HwMontMul(@t64[0], @A[0], @B[0], @C.P[0], C.NL div 2, C.M64);
    FillChar(R, SizeOf(R), 0);
    Move(t64[0], R[0], C.NL * 4);
    FeReduceOnce(C, R, UInt32(t64[C.NL div 2]));
    Exit;
  end;
  {$ENDIF}
  nl := C.NL;
  for i := 0 to nl + 1 do t[i] := 0;
  for i := 0 to nl - 1 do
  begin
    cy := 0;
    for j := 0 to nl - 1 do
    begin
      cy := cy + t[j] + UInt64(A[j]) * B[i];
      t[j] := UInt32(cy);
      cy := cy shr 32;
    end;
    cy := cy + t[nl];
    t[nl] := UInt32(cy);
    t[nl + 1] := UInt32(cy shr 32);
    m := t[0];                                   // -p^-1 mod 2^32 = 1
    cy := (UInt64(t[0]) + UInt64(m) * C.P[0]) shr 32;
    for j := 1 to nl - 1 do
    begin
      cy := cy + t[j] + UInt64(m) * C.P[j];
      t[j - 1] := UInt32(cy);
      cy := cy shr 32;
    end;
    cy := cy + t[nl];
    t[nl - 1] := UInt32(cy);
    t[nl] := t[nl + 1] + UInt32(cy shr 32);
  end;
  FillChar(R, SizeOf(R), 0);
  for i := 0 to nl - 1 do R[i] := t[i];
  FeReduceOnce(C, R, t[nl]);
end;

procedure FeInv(const C: TCtx; out R: TFe; const A: TFe);
var e: TBig; i: Integer; acc: TFe;
begin
  e := BigSub(FeToBig(C, C.P), BigFromInt(2));    // public exponent
  acc := C.OneM;
  for i := 32 * C.NL - 1 downto 0 do
  begin
    FeMul(C, acc, acc, acc);
    if BigBit(e, i) = 1 then FeMul(C, acc, acc, A);
  end;
  R := acc;
end;

procedure FeCSwap(const C: TCtx; var A, B: TFe; Bit: UInt32);
var i: Integer; mask, t: UInt32;
begin
  mask := UInt32(0) - (Bit and 1);
  for i := 0 to C.NL - 1 do
  begin
    t := mask and (A[i] xor B[i]);
    A[i] := A[i] xor t; B[i] := B[i] xor t;
  end;
end;

function FeEq(const C: TCtx; const A, B: TFe): Boolean;
var i: Integer; d: UInt32;
begin
  d := 0;
  for i := 0 to C.NL - 1 do d := d or (A[i] xor B[i]);
  Result := d = 0;
end;

procedure InitCurve(Curve: TEcdhCurve);
var c: TCtx; one, t: TFe; p0: UInt64; k: Integer;
begin
  begin
    c := Default(TCtx);
    case Curve of
      ecdhP256: begin c.NL := 8; c.Len := 32; end;
      ecdhP384: begin c.NL := 12; c.Len := 48; end;
      ecdhP521: begin c.NL := 18; c.Len := 66; end;        // even, see the header
    end;
    FeFromBig(c, c.P, BigFromHex(CurveParams[CurveIdx[Curve]].P));
    c.N := BigFromHex(CurveParams[CurveIdx[Curve]].N);
    c.NBits := BigBits(c.N);
    // -p^-1 mod 2^64 by Newton's iteration (x := x * (2 - p*x) doubles the correct bits)
    c.M64 := UInt64(c.P[0]) or (UInt64(c.P[1]) shl 32);
    p0 := c.M64;
    for k := 1 to 6 do c.M64 := c.M64 * (2 - p0 * c.M64);
    c.M64 := UInt64(0) - c.M64;
    // R^2 mod p, R = 2^(32*NL)
    FeFromBig(c, c.R2, BigMod(BigFromHex('1' + StringOfChar('0', 16 * c.NL)), BigFromHex(CurveParams[CurveIdx[Curve]].P)));
    FillChar(one, SizeOf(one), 0); one[0] := 1;
    FeMul(c, c.OneM, one, c.R2);
    FeFromBig(c, t, BigFromHex(CurveParams[CurveIdx[Curve]].B)); FeMul(c, c.BM, t, c.R2);
    FeFromBig(c, t, BigFromHex(CurveParams[CurveIdx[Curve]].Gx)); FeMul(c, c.GX, t, c.R2);
    FeFromBig(c, t, BigFromHex(CurveParams[CurveIdx[Curve]].Gy)); FeMul(c, c.GY, t, c.R2);
    c.Ready := True;
    Ctxs[Curve] := c;
  end;
end;

// contexts computed once in the initialization section - thread-safe
function Ctx(Curve: TEcdhCurve): TCtx;
begin
  Result := Ctxs[Curve];
end;

function EcdhCoordLen(Curve: TEcdhCurve): Integer;
begin
  case Curve of
    ecdhP256: Result := 32;
    ecdhP384: Result := 48;
  else Result := 66;
  end;
end;

// ---- points (Jacobian, a = -3) ----

{$IFDEF XELSSL_X64}
type
  // the P-384 point routines (test/gen_p384_points.py) on the generic TPt records
  TP384PointsCtx = record
    Op: Int64;                           // 1 PR := 2 PA, 2 PR := PA + PB
    PR, PA, PB, Dst: Pointer;
    P: array[0..5] of UInt64;            // the prime
    Pad: UInt64;
    Tmp: array[0..17, 0..5] of UInt64;
  end;

procedure HwP384Points(Ctx: Pointer);
var p: Pointer;
begin
  p := Ctx;
  asm
    mov rax, p
    {$I XelSslP384Points.inc}
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11'];
end;
{$ENDIF}

procedure PtDouble(const C: TCtx; out R: TPt; const A: TPt);
var delta, gamma, beta, alpha, t, t2: TFe; {$IFDEF XELSSL_X64}pc: TP384PointsCtx;{$ENDIF}
begin
  {$IFDEF XELSSL_X64}
  if P384Fast(C) then
  begin
    pc.Op := 1; pc.PR := @R; pc.PA := @A;
    Move(C.P[0], pc.P[0], 48);
    HwP384Points(@pc);
    Exit;
  end;
  {$ENDIF}
  FeMul(C, delta, A.Z, A.Z);
  FeMul(C, gamma, A.Y, A.Y);
  FeMul(C, beta, A.X, gamma);
  FeSub(C, t, A.X, delta); FeAdd(C, t2, A.X, delta); FeMul(C, alpha, t, t2);
  FeAdd(C, t, alpha, alpha); FeAdd(C, alpha, t, alpha);
  FeAdd(C, t, beta, beta); FeAdd(C, t, t, t); FeAdd(C, t2, t, t);
  FeMul(C, R.X, alpha, alpha); FeSub(C, R.X, R.X, t2);
  FeAdd(C, R.Z, A.Y, A.Z); FeMul(C, R.Z, R.Z, R.Z); FeSub(C, R.Z, R.Z, gamma); FeSub(C, R.Z, R.Z, delta);
  FeMul(C, gamma, gamma, gamma); FeAdd(C, gamma, gamma, gamma); FeAdd(C, gamma, gamma, gamma); FeAdd(C, gamma, gamma, gamma);
  FeSub(C, t, t, R.X); FeMul(C, R.Y, alpha, t); FeSub(C, R.Y, R.Y, gamma);
end;

procedure PtAdd(const C: TCtx; out R: TPt; const A, B: TPt);
var z1z1, z2z2, u1, u2, s1, s2, h, i, j, rr, v, t: TFe; {$IFDEF XELSSL_X64}pc: TP384PointsCtx;{$ENDIF}
begin
  {$IFDEF XELSSL_X64}
  if P384Fast(C) then
  begin
    pc.Op := 2; pc.PR := @R; pc.PA := @A; pc.PB := @B;
    Move(C.P[0], pc.P[0], 48);
    HwP384Points(@pc);
    Exit;
  end;
  {$ENDIF}
  FeMul(C, z1z1, A.Z, A.Z); FeMul(C, z2z2, B.Z, B.Z);
  FeMul(C, u1, A.X, z2z2); FeMul(C, u2, B.X, z1z1);
  FeMul(C, s1, A.Y, B.Z); FeMul(C, s1, s1, z2z2);
  FeMul(C, s2, B.Y, A.Z); FeMul(C, s2, s2, z1z1);
  FeSub(C, h, u2, u1);
  FeSub(C, rr, s2, s1); FeAdd(C, rr, rr, rr);
  FeAdd(C, t, h, h); FeMul(C, i, t, t);
  FeMul(C, j, h, i);
  FeMul(C, v, u1, i);
  FeMul(C, R.X, rr, rr); FeSub(C, R.X, R.X, j); FeAdd(C, t, v, v); FeSub(C, R.X, R.X, t);
  FeSub(C, t, v, R.X); FeMul(C, R.Y, rr, t); FeMul(C, t, s1, j); FeAdd(C, t, t, t); FeSub(C, R.Y, R.Y, t);
  FeAdd(C, t, A.Z, B.Z); FeMul(C, t, t, t); FeSub(C, t, t, z1z1); FeSub(C, t, t, z2z2); FeMul(C, R.Z, t, h);
end;

// K' = k + n (bit NBits is always 1) - ladder from the next bit down
procedure ScalarMul(const C: TCtx; const K: TBig; const X, Y: TFe; out AX, AY: TFe);
var r0, r1, t: TPt; i: Integer; bit: UInt32; zi, zi2: TFe;
begin
  r0.X := X; r0.Y := Y; r0.Z := C.OneM;
  PtDouble(C, r1, r0);
  for i := C.NBits - 1 downto 0 do
  begin
    bit := BigBit(K, i);
    FeCSwap(C, r0.X, r1.X, bit); FeCSwap(C, r0.Y, r1.Y, bit); FeCSwap(C, r0.Z, r1.Z, bit);
    PtAdd(C, t, r0, r1);
    PtDouble(C, r0, r0);
    r1 := t;
    FeCSwap(C, r0.X, r1.X, bit); FeCSwap(C, r0.Y, r1.Y, bit); FeCSwap(C, r0.Z, r1.Z, bit);
  end;
  FeInv(C, zi, r0.Z);
  FeMul(C, zi2, zi, zi);
  FeMul(C, AX, r0.X, zi2);
  FeMul(C, zi2, zi2, zi);
  FeMul(C, AY, r0.Y, zi2);
end;

function Extend(const C: TCtx; const Priv: TBytes): TBig;
begin
  Result := BigAdd(BigFromBytes(Priv), C.N);
  if BigBit(Result, C.NBits) <> 1 then
    raise Exception.Create('XelSSL ECDH: scalar out of range');
end;

function FromMont(const C: TCtx; const A: TFe): TFe;
var one: TFe;
begin
  FillChar(one, SizeOf(one), 0); one[0] := 1;
  FeMul(C, Result, A, one);
end;

function EcdhOrder(Curve: TEcdhCurve): TBytes;
begin
  Result := BigToBytes(Ctx(Curve).N);
end;

// ================= P-256 fast path (x86-64) =================

{$IFDEF XELSSL_X64}
type
  TF = array[0..3] of UInt64;              // Montgomery form, R = 2^256, fully reduced
  TJ = record X, Y, Z: TF; end;            // Jacobian

var
  P256P, P256R2, P256One, P256B, P256GX, P256GY: TF;
  P256NearN: TBig;                         // 2n - 64: k + n at or above it is k > n - 64

const
  P256Limbs: TF = (UInt64($FFFFFFFFFFFFFFFF), UInt64($00000000FFFFFFFF), 0, UInt64($FFFFFFFF00000001));

function P256Fast: Boolean; inline;
begin
  Result := EcdhUseAsm and AsmAvailable([cfSse2]);
end;

procedure FMul(out R: TF; const A, B: TF); inline;
begin
  HwP256Mul(@R[0], @A[0], @B[0]);
end;

procedure FSqr(out R: TF; const A: TF); inline;
begin
  if HaveMulx and EcdhUseMulx then P256SqrxAsm(@R[0], @A[0], nil) else HwP256Mul(@R[0], @A[0], @A[0]);
end;

procedure FAdd(out R: TF; const A, B: TF); inline;
begin
  P256AddAsm(@R[0], @A[0], @B[0]);
end;

procedure FSub(out R: TF; const A, B: TF); inline;
begin
  P256SubAsm(@R[0], @A[0], @B[0]);
end;

function FIsZero(const A: TF): Boolean; inline;
begin
  Result := (A[0] or A[1] or A[2] or A[3]) = 0;
end;

function FEqual(const A, B: TF): Boolean; inline;
begin
  Result := ((A[0] xor B[0]) or (A[1] xor B[1]) or (A[2] xor B[2]) or (A[3] xor B[3])) = 0;
end;

// A^(p-2) (fixed public exponent)
procedure FSqrN(var A: TF; N: Integer);
var i: Integer;
begin
  for i := 1 to N do FSqr(A, A);
end;

// A^(p-2), p - 2 = ffffffff 00000001 00000000 00000000 00000000 ffffffff ffffffff fffffffd:
// an addition chain of 255 squarings and 12 multiplications (as in BoringSSL)
procedure FInv(out R: TF; const A: TF);
var x2, x3, x6, x12, x15, x30, x32, t: TF;
begin
  FSqr(x2, A); FMul(x2, x2, A);                          // 2^2 - 1
  FSqr(x3, x2); FMul(x3, x3, A);                         // 2^3 - 1
  x6 := x3; FSqrN(x6, 3); FMul(x6, x6, x3);              // 2^6 - 1
  x12 := x6; FSqrN(x12, 6); FMul(x12, x12, x6);          // 2^12 - 1
  x15 := x12; FSqrN(x15, 3); FMul(x15, x15, x3);         // 2^15 - 1
  x30 := x15; FSqrN(x30, 15); FMul(x30, x30, x15);       // 2^30 - 1
  x32 := x30; FSqrN(x32, 2); FMul(x32, x32, x2);         // 2^32 - 1
  t := x32; FSqrN(t, 32); FMul(t, t, A);                 // ffffffff 00000001
  FSqrN(t, 128); FMul(t, t, x32);                        // ... 0 (96 bits) ffffffff
  FSqrN(t, 32); FMul(t, t, x32);                         // ... ffffffff
  FSqrN(t, 30); FMul(t, t, x30);                         // ... 30 ones
  FSqrN(t, 2); FMul(R, t, A);                            // ... 01
end;

type
  // the assembler block of point arithmetic and the window loop (test/gen_p256_ladder.py)
  TP256LadderCtx = record
    Op: Int64;                       // 0 window loop, 1 PR := 2 PA, 2 PR := PA + PB
    PR, PA, PB, Dst: Pointer;
    W: Int64;
    Pad: array[0..1] of UInt64;
    Dig: array[0..63] of Byte;       // signed window digits: |d| (0..16) or 128 for d < 0
    Acc, TSum, Sel: TJ;
    Tmp: array[0..19] of TF;         // 18 = zero, 19 = -Y
    Tab: array[1..16] of TJ;
  end;

procedure HwP256Ladder(Ctx: Pointer);
var p: Pointer;
begin
  p := Ctx;
  asm
    mov rax, p
    {$I XelSslP256Ladder.inc}
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11', 'xmm0', 'xmm1', 'xmm2', 'xmm3', 'xmm4', 'xmm5'];
end;

function P256AsmPoints: Boolean; inline;
begin
  Result := HaveMulx and EcdhUseMulx;
end;

procedure JDouble(out R: TJ; const A: TJ);
var delta, gamma, beta, alpha, t, t2: TF; ctx: TP256LadderCtx;
begin
  if P256AsmPoints then
  begin
    ctx.Op := 1; ctx.PR := @R; ctx.PA := @A;
    HwP256Ladder(@ctx);
    Exit;
  end;
  FSqr(delta, A.Z);
  FSqr(gamma, A.Y);
  FMul(beta, A.X, gamma);
  FSub(t, A.X, delta); FAdd(t2, A.X, delta); FMul(alpha, t, t2);
  FAdd(t, alpha, alpha); FAdd(alpha, t, alpha);
  FAdd(t, beta, beta); FAdd(t, t, t); FAdd(t2, t, t);            // t = 4 beta, t2 = 8 beta
  FAdd(R.Z, A.Y, A.Z); FSqr(R.Z, R.Z); FSub(R.Z, R.Z, gamma); FSub(R.Z, R.Z, delta);
  FSqr(R.X, alpha); FSub(R.X, R.X, t2);
  FSqr(gamma, gamma); FAdd(gamma, gamma, gamma); FAdd(gamma, gamma, gamma); FAdd(gamma, gamma, gamma);
  FSub(t, t, R.X); FMul(R.Y, alpha, t); FSub(R.Y, R.Y, gamma);
end;

// R := A + B for A <> +-B, neither infinity (add-2007-bl)
procedure JAdd(out R: TJ; const A, B: TJ);
var z1z1, z2z2, u1, u2, s1, s2, h, i, j, rr, v, t: TF; ctx: TP256LadderCtx;
begin
  if P256AsmPoints then
  begin
    ctx.Op := 2; ctx.PR := @R; ctx.PA := @A; ctx.PB := @B;
    HwP256Ladder(@ctx);
    Exit;
  end;
  FSqr(z1z1, A.Z); FSqr(z2z2, B.Z);
  FMul(u1, A.X, z2z2); FMul(u2, B.X, z1z1);
  FMul(s1, A.Y, B.Z); FMul(s1, s1, z2z2);
  FMul(s2, B.Y, A.Z); FMul(s2, s2, z1z1);
  FSub(h, u2, u1);
  FSub(rr, s2, s1); FAdd(rr, rr, rr);
  FAdd(t, h, h); FSqr(i, t);
  FMul(j, h, i);
  FMul(v, u1, i);
  FSqr(R.X, rr); FSub(R.X, R.X, j); FAdd(t, v, v); FSub(R.X, R.X, t);
  FSub(t, v, R.X); FMul(R.Y, rr, t); FMul(t, s1, j); FAdd(t, t, t); FSub(R.Y, R.Y, t);
  FAdd(t, A.Z, B.Z); FSqr(t, t); FSub(t, t, z1z1); FSub(t, t, z2z2); FMul(R.Z, t, h);
end;

// R := (Bit = 1) ? B : A, constant time
procedure JSelect(var R: TJ; const B: TJ; Bit: UInt64);
var mask: UInt64; i: Integer;
begin
  mask := UInt64(0) - (Bit and 1);
  for i := 0 to 3 do
  begin
    R.X[i] := R.X[i] xor (mask and (R.X[i] xor B.X[i]));
    R.Y[i] := R.Y[i] xor (mask and (R.Y[i] xor B.Y[i]));
    R.Z[i] := R.Z[i] xor (mask and (R.Z[i] xor B.Z[i]));
  end;
end;

function FFromBytes(const B: TBytes; Off: Integer): TF;
var i, k: Integer;
begin
  for i := 0 to 3 do
  begin
    Result[i] := 0;
    for k := 0 to 7 do Result[i] := (Result[i] shl 8) or B[Off + (3 - i) * 8 + k];
  end;
end;

function FToBytes(const A: TF): TBytes;
var i, k: Integer;
begin
  SetLength(Result, 32);
  for i := 0 to 3 do
    for k := 0 to 7 do Result[(3 - i) * 8 + k] := Byte(A[i] shr (8 * (7 - k)));
end;

// a value < p from big-endian bytes; False if >= p
function FFromBytesChecked(const B: TBytes; Off: Integer; out R: TF): Boolean;
var i: Integer;
begin
  R := FFromBytes(B, Off);
  for i := 3 downto 0 do
    if R[i] <> P256Limbs[i] then Exit(R[i] < P256Limbs[i]);
  Result := False;
end;

function FToMont(const A: TF): TF;
begin
  FMul(Result, A, P256R2);
end;

function FFromMont(const A: TF): TF;
var one: TF;
begin
  one[0] := 1; one[1] := 0; one[2] := 0; one[3] := 0;
  FMul(Result, A, one);
end;

// x, y (Montgomery) on y^2 = x^3 - 3x + b
function OnCurve(const X, Y: TF): Boolean;
var l, r, t: TF;
begin
  FMul(l, Y, Y);
  FMul(r, X, X); FMul(r, r, X);
  FAdd(t, X, X); FAdd(t, t, X);
  FSub(r, r, t); FAdd(r, r, P256B);
  Result := FEqual(l, r);
end;

// K = k + n (257 bits, bit 256 set, K < 2n - 64) times (QX, QY), Jacobian result: the whole
// window loop in the assembler block, signed 5-bit digits (Booth recoding as in OpenSSL),
// table 1..16 * Q, constant time
procedure P256BoothMul(const K: TBig; const QX, QY: TF; out Acc: TJ);
var i, j, w: Integer; d, sgn: UInt32; m: UInt64; ctx: TP256LadderCtx;
begin
  ctx.Tab[1].X := QX; ctx.Tab[1].Y := QY; ctx.Tab[1].Z := P256One;
  JDouble(ctx.Tab[2], ctx.Tab[1]);
  for j := 3 to 16 do JAdd(ctx.Tab[j], ctx.Tab[j - 1], ctx.Tab[1]);
  FillChar(ctx.Tmp[18], SizeOf(TF), 0);
  for w := 0 to 51 do
  begin
    // bits 5w-1 .. 5w+4 (bit -1 = 0)
    d := 0;
    for i := 0 to 5 do
      if 5 * w - 1 + i >= 0 then d := d or (UInt32(BigBit(K, 5 * w - 1 + i)) shl i);
    m := UInt64(0) - UInt64(d shr 5);                       // all ones for a negative digit
    sgn := d shr 5;
    d := UInt32(((63 - d) and UInt32(m)) or (d and not UInt32(m)));
    d := (d shr 1) + (d and 1);                             // |digit| 0..16
    ctx.Dig[w] := Byte(d or (sgn shl 7));
  end;
  // the top window (bit 256 of k + n is set): a positive digit, picked in constant time
  FillChar(ctx.Acc, SizeOf(ctx.Acc), 0);
  for j := 1 to 16 do
  begin
    m := UInt64(UInt32(j) xor ctx.Dig[51]);
    m := UInt64(0) - ((m - 1) shr 63);
    for i := 0 to 3 do
    begin
      ctx.Acc.X[i] := ctx.Acc.X[i] or (ctx.Tab[j].X[i] and m);
      ctx.Acc.Y[i] := ctx.Acc.Y[i] or (ctx.Tab[j].Y[i] and m);
      ctx.Acc.Z[i] := ctx.Acc.Z[i] or (ctx.Tab[j].Z[i] and m);
    end;
  end;
  ctx.Op := 0;
  HwP256Ladder(@ctx);
  Acc := ctx.Acc;
  FillChar(ctx, SizeOf(ctx), 0);
end;

// K = k + n (257 bits, bit 256 set) times (QX, QY); fixed 4-bit windows, every step does
// 4 doublings and one addition with an entry selected in constant time (digit 0: the
// sum is computed with entry 1 and discarded by a masked select). Affine result.
procedure P256ScalarMul(const K: TBig; const QX, QY: TF; out AX, AY: TF);
var tab: array[1..15] of TJ; acc, t, sel: TJ; i, j, w: Integer; d: UInt32; zi, zi2: TF; m: UInt64;
begin
  // signed digits meet equal points in the last step for k = n - 2d (d = 1..16); those
  // few scalars right below n (probability ~2^-250) take the unsigned windows below
  if P256AsmPoints and P256AsmLoop and (BigCmp(K, P256NearN) < 0) then
  begin
    P256BoothMul(K, QX, QY, acc);
    FInv(zi, acc.Z);
    FSqr(zi2, zi);
    FMul(AX, acc.X, zi2);
    FMul(zi2, zi2, zi);
    FMul(AY, acc.Y, zi2);
    FillChar(acc, SizeOf(acc), 0);
    Exit;
  end;
  tab[1].X := QX; tab[1].Y := QY; tab[1].Z := P256One;
  JDouble(tab[2], tab[1]);
  for j := 3 to 15 do JAdd(tab[j], tab[j - 1], tab[1]);
  acc := tab[1];                                   // window 64: the single top bit (1)
  for w := 63 downto 0 do
  begin
    for i := 1 to 4 do begin JDouble(t, acc); acc := t; end;
    d := (UInt32(BigBit(K, 4 * w + 3)) shl 3) or (UInt32(BigBit(K, 4 * w + 2)) shl 2) or
         (UInt32(BigBit(K, 4 * w + 1)) shl 1) or UInt32(BigBit(K, 4 * w));
    P256SelectAsm(@sel, @tab[1], d);                 // zeros for d = 0 (that sum is discarded)
    JAdd(t, acc, sel);
    m := UInt64(d);
    m := 1 - ((m or (UInt64(0) - m)) shr 63);       // 1 when d = 0
    JSelect(t, acc, m);
    acc := t;
  end;
  FInv(zi, acc.Z);
  FMul(zi2, zi, zi);
  FMul(AX, acc.X, zi2);
  FMul(zi2, zi2, zi);
  FMul(AY, acc.Y, zi2);
  FillChar(tab, SizeOf(tab), 0); FillChar(acc, SizeOf(acc), 0); FillChar(t, SizeOf(t), 0);
  FillChar(sel, SizeOf(sel), 0);
end;

// k * G: with the fixed table of G (below, next to the verification)
function P256PublicOf(const K: TBig): TBytes; forward;

function P256Shared(const K: TBig; const PeerPub: TBytes; out Secret: TBytes): Boolean;
var qx, qy, ax, ay: TF;
begin
  Result := False; Secret := nil;
  if (Length(PeerPub) <> 65) or (PeerPub[0] <> 4) then Exit;
  if not FFromBytesChecked(PeerPub, 1, qx) or not FFromBytesChecked(PeerPub, 33, qy) then Exit;
  qx := FToMont(qx); qy := FToMont(qy);
  if not OnCurve(qx, qy) then Exit;
  P256ScalarMul(K, qx, qy, ax, ay);
  ax := FFromMont(ax);
  if FIsZero(ax) then Exit;
  Secret := FToBytes(ax);
  Result := True;
end;

// R := R + B with the special cases - variable time (verification)
procedure JAddV(var R: TJ; var RInf: Boolean; const B: TJ);
var z1z1, z2z2, u1, u2, s1, s2, h, rr: TF; t: TJ;
begin
  if RInf then begin R := B; RInf := False; Exit; end;
  // the general addition first: its Z = 2*Z1*Z2*h is 0 only for R = +-B (rare, public
  // data), and only then the case is told apart below
  JAdd(t, R, B);
  if not FIsZero(t.Z) then
  begin
    R := t;
    Exit;
  end;
  FMul(z1z1, R.Z, R.Z); FMul(z2z2, B.Z, B.Z);
  FMul(u1, R.X, z2z2); FMul(u2, B.X, z1z1);
  FMul(s1, R.Y, B.Z); FMul(s1, s1, z2z2);
  FMul(s2, B.Y, R.Z); FMul(s2, s2, z1z1);
  FSub(h, u2, u1);
  FSub(rr, s2, s1);
  if FIsZero(h) then
  begin
    if FIsZero(rr) then begin JDouble(t, R); R := t; end
    else RInf := True;
    Exit;
  end;
  JAdd(t, R, B);
  R := t;
end;
{$ENDIF}

function EcdhPublicOf(Curve: TEcdhCurve; const Priv: TBytes): TBytes;
var C: TCtx; ax, ay: TFe;
begin
  C := Ctx(Curve);
  {$IFDEF XELSSL_X64}
  if (Curve = ecdhP256) and P256Fast then Exit(P256PublicOf(Extend(C, Priv)));
  {$ENDIF}
  ScalarMul(C, Extend(C, Priv), C.GX, C.GY, ax, ay);
  Result := Concat(TBytes.Create(4), BigToBytes(FeToBig(C, FromMont(C, ax)), C.Len));
  Result := Concat(Result, BigToBytes(FeToBig(C, FromMont(C, ay)), C.Len));
end;

procedure EcdhKeyPair(Curve: TEcdhCurve; out Priv, Pub: TBytes);
var C: TCtx; k: TBig;
begin
  C := Ctx(Curve);
  repeat
    Priv := RandomBytes(C.Len);
    if Curve = ecdhP521 then Priv[0] := Priv[0] and 1;        // 521 bits
    k := BigFromBytes(Priv);
  until (BigCmp(k, C.N) < 0) and (BigBits(k) > C.NBits - 32);   // then k + n has bit NBits set
  Pub := EcdhPublicOf(Curve, Priv);
end;

function EcdhShared(Curve: TEcdhCurve; const Priv, PeerPub: TBytes; out Secret: TBytes): Boolean;
var C: TCtx; qx, qy: TBig; mx, my, l, r, t, ax, ay, fx: TFe;
begin
  Result := False; Secret := nil;
  C := Ctx(Curve);
  {$IFDEF XELSSL_X64}
  if (Curve = ecdhP256) and P256Fast then Exit(P256Shared(Extend(C, Priv), PeerPub, Secret));
  {$ENDIF}
  if (Length(PeerPub) <> 1 + 2 * C.Len) or (PeerPub[0] <> 4) then Exit;
  qx := BigFromBytes(Copy(PeerPub, 1, C.Len));
  qy := BigFromBytes(Copy(PeerPub, 1 + C.Len, C.Len));
  if (BigCmp(qx, FeToBig(C, C.P)) >= 0) or (BigCmp(qy, FeToBig(C, C.P)) >= 0) then Exit;
  FeFromBig(C, t, qx); FeMul(C, mx, t, C.R2);
  FeFromBig(C, t, qy); FeMul(C, my, t, C.R2);
  // y^2 = x^3 - 3x + b (public point - the check need not be constant time)
  FeMul(C, l, my, my);
  FeMul(C, r, mx, mx); FeMul(C, r, r, mx);
  FeAdd(C, t, mx, mx); FeAdd(C, t, t, mx);
  FeSub(C, r, r, t); FeAdd(C, r, r, C.BM);
  if not FeEq(C, l, r) then Exit;
  ScalarMul(C, Extend(C, Priv), mx, my, ax, ay);
  fx := FromMont(C, ax);
  if Length(FeToBig(C, fx)) = 0 then Exit;
  Secret := BigToBytes(FeToBig(C, fx), C.Len);
  Result := True;
end;

// ---- ECDSA verification (public data, variable time) ----

type
  TWnaf = array[0..575] of ShortInt;

// width-5 NAF of K (big-endian): digits odd in -15..15, at most one non-zero in 5
// positions. A 6-bit window slides over the scalar (as bn_compute_wNAF in OpenSSL)
// instead of shifting the whole number for every bit.
function Wnaf(const K: TBytes; out D: TWnaf): Integer;
const
  BITV = 16; NEXTV = 32; MASKV = 31;
var len, j, window, digit, i: Integer;
  function BitAt(P: Integer): Integer; inline;
  begin
    if P >= 8 * Length(K) then Result := 0
    else Result := (K[High(K) - (P shr 3)] shr (P and 7)) and 1;
  end;
begin
  FillChar(D, SizeOf(D), 0);
  // bit length
  len := 0;
  for i := 0 to High(K) do
    if K[i] <> 0 then
    begin
      len := 8 * (Length(K) - i);
      while (len > 0) and (BitAt(len - 1) = 0) do Dec(len);
      Break;
    end;
  window := 0;
  for i := 0 to 5 do window := window or (BitAt(i) shl i);
  window := window and MASKV;
  j := 0;
  while (window <> 0) or (j + 5 < len) do
  begin
    digit := 0;
    if window and 1 <> 0 then
    begin
      if window and BITV <> 0 then
      begin
        digit := window - NEXTV;
        if j + 5 >= len then digit := window and (MASKV shr 1);
      end
      else
        digit := window;
      window := window - digit;
    end;
    D[j] := digit;
    Inc(j);
    window := (window shr 1) + BITV * BitAt(j + 4);
  end;
  Result := j;
end;

function FeIsZeroV(const C: TCtx; const A: TFe): Boolean;
var i: Integer;
begin
  for i := 0 to C.NL - 1 do if A[i] <> 0 then Exit(False);
  Result := True;
end;

// R := R + B with the special cases (infinity, R = B, R = -B) - variable time
procedure PtAddV(const C: TCtx; var R: TPt; var RInf: Boolean; const B: TPt);
var z1z1, z2z2, u1, u2, s1, s2, h, rr: TFe; t: TPt;
begin
  if RInf then begin R := B; RInf := False; Exit; end;
  // the general addition first: its Z = 2*Z1*Z2*h is 0 only for R = +-B (rare, public
  // data), and only then the case is told apart below
  PtAdd(C, t, R, B);
  if not FeIsZeroV(C, t.Z) then
  begin
    R := t;
    Exit;
  end;
  FeMul(C, z1z1, R.Z, R.Z); FeMul(C, z2z2, B.Z, B.Z);
  FeMul(C, u1, R.X, z2z2); FeMul(C, u2, B.X, z1z1);
  FeMul(C, s1, R.Y, B.Z); FeMul(C, s1, s1, z2z2);
  FeMul(C, s2, B.Y, R.Z); FeMul(C, s2, s2, z1z1);
  FeSub(C, h, u2, u1);
  FeSub(C, rr, s2, s1);
  if FeIsZeroV(C, h) then
  begin
    if FeIsZeroV(C, rr) then begin PtDouble(C, t, R); R := t; end
    else RInf := True;
    Exit;
  end;
  PtAdd(C, t, R, B);
  R := t;
end;

procedure PtNegV(const C: TCtx; var P: TPt);
var z: TFe;
begin
  FillChar(z, SizeOf(z), 0);
  FeSub(C, P.Y, z, P.Y);
end;

{$IFDEF XELSSL_X64}
type
  // j * 2^(5w) * G, affine (Montgomery), for the 52 signed 5-bit windows of a scalar
  TP256Aff = record X, Y: TF; end;
  TP256GTab = array[0..51, 1..16] of TP256Aff;
  PP256GTab = ^TP256GTab;

var
  P256GTab: PP256GTab = nil;

// built on first use (52 * 16 points, ~0.3 ms); a thread that loses the race frees its copy
function P256GTable: PP256GTab;
var
  t: PP256GTab; pts: array of TJ; pre: array of TF; p, d: TJ; w, j, i, n: Integer;
  inv, zi, zi2: TF;
begin
  Result := P256GTab;
  if Result <> nil then Exit;
  n := 52 * 16;
  SetLength(pts, n); SetLength(pre, n);
  p.X := P256GX; p.Y := P256GY; p.Z := P256One;
  for w := 0 to 51 do
  begin
    // p = 2^(5w) G; no entry equals +-p, so the plain additions are exact
    pts[16 * w] := p;
    JDouble(pts[16 * w + 1], p);
    for j := 2 to 15 do JAdd(pts[16 * w + j], pts[16 * w + j - 1], p);
    JDouble(d, pts[16 * w + 15]);
    p := d;
  end;
  // one inversion for all: prefix products of Z
  pre[0] := pts[0].Z;
  for i := 1 to n - 1 do FMul(pre[i], pre[i - 1], pts[i].Z);
  FInv(inv, pre[n - 1]);
  New(t);
  for i := n - 1 downto 0 do
  begin
    if i > 0 then
    begin
      FMul(zi, inv, pre[i - 1]);
      FMul(inv, inv, pts[i].Z);
    end
    else zi := inv;
    FSqr(zi2, zi);
    FMul(t^[i div 16, i mod 16 + 1].X, pts[i].X, zi2);
    FMul(zi2, zi2, zi);
    FMul(t^[i div 16, i mod 16 + 1].Y, pts[i].Y, zi2);
  end;
  if InterlockedCompareExchange(Pointer(P256GTab), Pointer(t), nil) <> nil then Dispose(t);
  Result := P256GTab;
end;

// R := A + (B.X, B.Y, 1): the mixed addition (op 3 of the assembler block); A <> +-B, A not
// infinity (else R.Z = 0); R = A allowed
procedure JMAdd(out R: TJ; const A: TJ; const B: TP256Aff);
var ctx: TP256LadderCtx;
begin
  ctx.Op := 3; ctx.PR := @R; ctx.PA := @A; ctx.PB := @B;
  HwP256Ladder(@ctx);
end;

// k * G from the fixed table, constant time: 52 signed 5-bit windows, each a selection of
// one of 16 affine entries (all read), Y negated under a mask, one mixed addition; masks
// keep acc for digit 0 and take the entry itself while acc is still the point at infinity.
// For 0 < k < n no addition meets +-acc: the partial sum s of the windows below w has
// |s| < 2^(5w) <= |entry| (and the top window cannot close to 0 or 2 * entry below n).
procedure P256BaseMul(const K: TBig; out AX, AY: TF);
var
  tab: PP256GTab; acc, tsum: TJ; sel: TP256Aff; ny, zero, zi, zi2: TF;
  w, i, j: Integer; d, sgn: UInt32; m, mz, inf, ms: UInt64;
begin
  tab := P256GTable;
  FillChar(acc, SizeOf(acc), 0); FillChar(zero, SizeOf(zero), 0);
  inf := UInt64(0) - 1;
  for w := 0 to 51 do
  begin
    d := 0;
    for i := 0 to 5 do
      if 5 * w - 1 + i >= 0 then d := d or (UInt32(BigBit(K, 5 * w - 1 + i)) shl i);
    m := UInt64(0) - UInt64(d shr 5);
    sgn := d shr 5;
    d := UInt32(((63 - d) and UInt32(m)) or (d and not UInt32(m)));
    d := (d shr 1) + (d and 1);                             // |digit| 0..16
    FillChar(sel, SizeOf(sel), 0);
    for j := 1 to 16 do
    begin
      m := UInt64(UInt32(j) xor d);
      m := UInt64(0) - ((m - 1) shr 63);                    // all ones for j = |digit|
      for i := 0 to 3 do
      begin
        sel.X[i] := sel.X[i] or (tab^[w, j].X[i] and m);
        sel.Y[i] := sel.Y[i] or (tab^[w, j].Y[i] and m);
      end;
    end;
    FSub(ny, zero, sel.Y);
    ms := UInt64(0) - UInt64(sgn);
    for i := 0 to 3 do sel.Y[i] := sel.Y[i] xor ((sel.Y[i] xor ny[i]) and ms);
    JMAdd(tsum, acc, sel);
    // tsum := inf ? (sel, 1) : tsum; acc := (digit = 0) ? acc : tsum
    for i := 0 to 3 do
    begin
      tsum.X[i] := tsum.X[i] xor ((tsum.X[i] xor sel.X[i]) and inf);
      tsum.Y[i] := tsum.Y[i] xor ((tsum.Y[i] xor sel.Y[i]) and inf);
      tsum.Z[i] := tsum.Z[i] xor ((tsum.Z[i] xor P256One[i]) and inf);
    end;
    mz := UInt64(0) - ((UInt64(d) - 1) shr 63);              // all ones for digit 0
    for i := 0 to 3 do
    begin
      acc.X[i] := tsum.X[i] xor ((tsum.X[i] xor acc.X[i]) and mz);
      acc.Y[i] := tsum.Y[i] xor ((tsum.Y[i] xor acc.Y[i]) and mz);
      acc.Z[i] := tsum.Z[i] xor ((tsum.Z[i] xor acc.Z[i]) and mz);
    end;
    inf := inf and mz;
  end;
  FInv(zi, acc.Z);
  FSqr(zi2, zi);
  FMul(AX, acc.X, zi2);
  FMul(zi2, zi2, zi);
  FMul(AY, acc.Y, zi2);
  FillChar(acc, SizeOf(acc), 0); FillChar(tsum, SizeOf(tsum), 0); FillChar(sel, SizeOf(sel), 0);
  FillChar(ny, SizeOf(ny), 0);
end;

// K = k + n: k * G from the table (with MULX), else the general window loop
function P256PublicOf(const K: TBig): TBytes;
var ax, ay: TF;
begin
  if P256AsmPoints and P256UseGTab then
    P256BaseMul(BigSub(K, Ctx(ecdhP256).N), ax, ay)
  else
    P256ScalarMul(K, P256GX, P256GY, ax, ay);
  Result := Concat(TBytes.Create(4), FToBytes(FFromMont(ax)), FToBytes(FFromMont(ay)));
end;

// U1 * G + U2 * Q (Jacobian; public scalars): U2 * Q in the assembler window loop, U1 * G
// from the fixed table (52 mixed additions, no doublings). False if not applicable (U2 = 0 or
// U2 >= n - 64, kept from the signed windows of the loop).
function P256VerifyFast(const U1, U2: TBytes; const QX, QY: TF; out Acc: TJ; out Inf: Boolean): Boolean;
var u1b, k: TBig; tab: PP256GTab; pt, t: TJ; a: TP256Aff; w, i: Integer; d: UInt32; zero: TF;
begin
  Result := False;
  if not (P256AsmPoints and P256AsmLoop and P256UseGTab) then Exit;
  k := BigFromBytes(U2);
  if BigIsZero(k) then Exit;
  k := BigAdd(k, Ctx(ecdhP256).N);
  if BigCmp(k, P256NearN) >= 0 then Exit;
  u1b := BigFromBytes(U1);
  if BigBits(u1b) > 256 then Exit;
  tab := P256GTable;
  P256BoothMul(k, QX, QY, Acc);
  Inf := False;
  FillChar(zero, SizeOf(zero), 0);
  pt.Z := P256One;
  for w := 0 to 51 do
  begin
    d := 0;
    for i := 0 to 5 do
      if 5 * w - 1 + i >= 0 then d := d or (UInt32(BigBit(u1b, 5 * w - 1 + i)) shl i);
    if (d = 0) or (d = 63) then Continue;
    if d >= 32 then
    begin
      d := 63 - d; d := (d shr 1) + (d and 1);
      a.X := tab^[w, d].X; FSub(a.Y, zero, tab^[w, d].Y);
    end
    else
    begin
      d := (d shr 1) + (d and 1);
      a := tab^[w, d];
    end;
    // the mixed addition; its Z = 2 * Z1 * h is 0 only for acc = +-entry (then the
    // general addition with the special cases)
    JMAdd(t, Acc, a);
    if not FIsZero(t.Z) then Acc := t
    else
    begin
      pt.X := a.X; pt.Y := a.Y;
      JAddV(Acc, Inf, pt);
    end;
  end;
  Result := True;
end;

function P256Verify(const Pub, U1, U2, R: TBytes): Boolean;
var
  C: TCtx; qx, qy, t, z2, xr: TF; tg, tq: array[0..7] of TJ; g, q, g2, q2, acc, neg: TJ;
  dg, dq: TWnaf; i, ng, nq, top: Integer; inf: Boolean; rb, rn: TBig; rbytes: TBytes;
  zero: TF;
begin
  Result := False;
  if (Length(Pub) <> 65) or (Pub[0] <> 4) then Exit;
  if not FFromBytesChecked(Pub, 1, qx) or not FFromBytesChecked(Pub, 33, qy) then Exit;
  qx := FToMont(qx); qy := FToMont(qy);
  if not OnCurve(qx, qy) then Exit;
  if P256VerifyFast(U1, U2, qx, qy, acc, inf) then
  begin
    if inf or FIsZero(acc.Z) then Exit;
  end
  else
  begin
    // the general way: both scalars together (Shamir), wNAF digits
    FillChar(zero, SizeOf(zero), 0);
    g.X := P256GX; g.Y := P256GY; g.Z := P256One;
    q.X := qx; q.Y := qy; q.Z := P256One;
    JDouble(g2, g); JDouble(q2, q);
    tg[0] := g; tq[0] := q;
    for i := 1 to 7 do
    begin
      JAdd(tg[i], tg[i - 1], g2);
      JAdd(tq[i], tq[i - 1], q2);
    end;
    ng := Wnaf(U1, dg);
    nq := Wnaf(U2, dq);
    top := ng; if nq > top then top := nq;
    inf := True;
    acc := g;
    for i := top - 1 downto 0 do
    begin
      if not inf then begin JDouble(neg, acc); acc := neg; end;
      if dg[i] > 0 then JAddV(acc, inf, tg[dg[i] div 2])
      else if dg[i] < 0 then begin neg := tg[(-dg[i]) div 2]; FSub(neg.Y, zero, neg.Y); JAddV(acc, inf, neg); end;
      if dq[i] > 0 then JAddV(acc, inf, tq[dq[i] div 2])
      else if dq[i] < 0 then begin neg := tq[(-dq[i]) div 2]; FSub(neg.Y, zero, neg.Y); JAddV(acc, inf, neg); end;
    end;
    if inf or FIsZero(acc.Z) then Exit;
  end;
  // x(acc) = X / Z^2: compare X with r * Z^2 (and (r + n) * Z^2 if r + n < p)
  FMul(z2, acc.Z, acc.Z);
  C := Ctx(ecdhP256);
  rb := BigFromBytes(R);
  if BigBits(rb) > 256 then Exit;
  rbytes := BigToBytes(rb, 32);
  if not FFromBytesChecked(rbytes, 0, t) then Exit;
  FMul(xr, FToMont(t), z2);
  if FEqual(xr, acc.X) then Exit(True);
  rn := BigAdd(rb, C.N);
  if BigBits(rn) > 256 then Exit;
  rbytes := BigToBytes(rn, 32);
  if FFromBytesChecked(rbytes, 0, t) then
  begin
    FMul(xr, FToMont(t), z2);
    Result := FEqual(xr, acc.X);
  end;
end;
{$ENDIF}

function EcVerifyCombination(Curve: TEcdhCurve; const Pub, U1, U2, R: TBytes): Boolean;
var
  C: TCtx; qx, qy, rb, pb, rn: TBig; t, l, rr, mx, my, z2, xr: TFe;
  tg, tq: array[0..7] of TPt; g, q, g2, q2, acc, neg: TPt; dg, dq: TWnaf;
  i, ng, nq, top: Integer; inf: Boolean;
begin
  Result := False;
  {$IFDEF XELSSL_X64}
  if (Curve = ecdhP256) and P256Fast then Exit(P256Verify(Pub, U1, U2, R));
  {$ENDIF}
  C := Ctx(Curve);
  if (Length(Pub) <> 1 + 2 * C.Len) or (Pub[0] <> 4) then Exit;
  pb := FeToBig(C, C.P);
  qx := BigFromBytes(Copy(Pub, 1, C.Len));
  qy := BigFromBytes(Copy(Pub, 1 + C.Len, C.Len));
  if (BigCmp(qx, pb) >= 0) or (BigCmp(qy, pb) >= 0) then Exit;
  FeFromBig(C, t, qx); FeMul(C, mx, t, C.R2);
  FeFromBig(C, t, qy); FeMul(C, my, t, C.R2);
  // Q on the curve: y^2 = x^3 - 3x + b
  FeMul(C, l, my, my);
  FeMul(C, rr, mx, mx); FeMul(C, rr, rr, mx);
  FeAdd(C, t, mx, mx); FeAdd(C, t, t, mx);
  FeSub(C, rr, rr, t); FeAdd(C, rr, rr, C.BM);
  if not FeEq(C, l, rr) then Exit;
  // odd multiples 1, 3, ..., 15 of G and Q
  g.X := C.GX; g.Y := C.GY; g.Z := C.OneM;
  q.X := mx; q.Y := my; q.Z := C.OneM;
  PtDouble(C, g2, g); PtDouble(C, q2, q);
  tg[0] := g; tq[0] := q;
  for i := 1 to 7 do
  begin
    PtAdd(C, tg[i], tg[i - 1], g2);
    PtAdd(C, tq[i], tq[i - 1], q2);
  end;
  ng := Wnaf(U1, dg);
  nq := Wnaf(U2, dq);
  top := ng; if nq > top then top := nq;
  inf := True;
  acc := g;
  for i := top - 1 downto 0 do
  begin
    if not inf then begin PtDouble(C, neg, acc); acc := neg; end;
    if dg[i] > 0 then PtAddV(C, acc, inf, tg[dg[i] div 2])
    else if dg[i] < 0 then begin neg := tg[(-dg[i]) div 2]; PtNegV(C, neg); PtAddV(C, acc, inf, neg); end;
    if dq[i] > 0 then PtAddV(C, acc, inf, tq[dq[i] div 2])
    else if dq[i] < 0 then begin neg := tq[(-dq[i]) div 2]; PtNegV(C, neg); PtAddV(C, acc, inf, neg); end;
  end;
  if inf or FeIsZeroV(C, acc.Z) then Exit;
  // x(acc) = X / Z^2: compare X with r * Z^2 (and with (r + n) * Z^2 if r + n < p)
  FeMul(C, z2, acc.Z, acc.Z);
  rb := BigFromBytes(R);
  FeFromBig(C, t, rb); FeMul(C, xr, t, C.R2);
  FeMul(C, xr, xr, z2);
  if FeEq(C, xr, acc.X) then Exit(True);
  rn := BigAdd(rb, C.N);
  if BigCmp(rn, pb) < 0 then
  begin
    FeFromBig(C, t, rn); FeMul(C, xr, t, C.R2);
    FeMul(C, xr, xr, z2);
    Result := FeEq(C, xr, acc.X);
  end;
end;

{$IFDEF XELSSL_X64}
procedure InitP256;
var c: TCtx;
begin
  c := Ctxs[ecdhP256];
  Move(c.P[0], P256P[0], 32);
  Move(c.R2[0], P256R2[0], 32);
  Move(c.OneM[0], P256One[0], 32);
  Move(c.BM[0], P256B[0], 32);
  Move(c.GX[0], P256GX[0], 32);
  Move(c.GY[0], P256GY[0], 32);
  P256NearN := BigSub(BigAdd(c.N, c.N), BigFromInt(64));
end;
{$ENDIF}

var cv: TEcdhCurve;
initialization
  {$IFDEF XELSSL_X64}
  HaveMulx := AsmAvailable([cfBmi2, cfAdx]);
  HaveP384x := HaveMulx;
  {$ENDIF}
  for cv := Low(TEcdhCurve) to High(TEcdhCurve) do InitCurve(cv);
  {$IFDEF XELSSL_X64}
  InitP256;
  {$ENDIF}
finalization
  {$IFDEF XELSSL_X64}
  if P256GTab <> nil then Dispose(P256GTab);
  {$ENDIF}
end.
