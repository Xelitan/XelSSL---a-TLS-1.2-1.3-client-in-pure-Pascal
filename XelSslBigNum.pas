// XelSSL - minimal big natural number arithmetic (for RSA/ECDSA verification).
// 32-bit little-endian limbs; division: Knuth's algorithm D (after "Hacker's
// Delight", divmnu64). Operations are NOT constant time - used only on
// public data (signatures, public keys) - except BigModExp with an odd modulus:
// Montgomery multiplication (CIOS; on x86-64 an assembler addition on 64-bit limbs),
// short (public) exponents bit by bit, long ones in fixed 4-bit windows with a
// constant-time table lookup and a masked final subtraction. R^2 mod n is cached for
// the last few moduli (the same CA keys are verified again and again). License: MIT.
unit XelSslBigNum;

{$mode objfpc}{$H+}{$Q-}{$R-}
{$IFDEF CPUX86_64}
  {$asmmode intel}
  {$DEFINE XELSSL_X64}
{$ENDIF}

interface

uses
  SysUtils;

type
  TBig = array of UInt32;        // normalized: no trailing zero limbs; 0 = []

function BigFromBytes(const B: TBytes): TBig;          // big-endian
function BigFromHex(const S: string): TBig;
function BigFromInt(V: UInt32): TBig;
function BigToBytes(const A: TBig; Len: Integer = 0): TBytes;   // Len=0: minimal length
function BigIsZero(const A: TBig): Boolean; inline;
function BigCmp(const A, B: TBig): Integer;
function BigBits(const A: TBig): Integer;
function BigBit(const A: TBig; I: Integer): Integer; inline;
function BigAdd(const A, B: TBig): TBig;
function BigSub(const A, B: TBig): TBig;               // requires A >= B
function BigMul(const A, B: TBig): TBig;
procedure BigDivMod(const U, V: TBig; out Q, R: TBig);
function BigMod(const A, M: TBig): TBig;
function BigShr(const A: TBig; N: Integer): TBig;
function BigModAdd(const A, B, M: TBig): TBig;
function BigModSub(const A, B, M: TBig): TBig;
function BigModMul(const A, B, M: TBig): TBig;
function BigModExp(const Base, Exp, M: TBig): TBig;
function BigModInvPrime(const A, P: TBig): TBig;       // A^(P-2) mod P
// A^-1 mod M for odd M and gcd(A, M) = 1 (binary GCD on approximations, Pornin);
// variable time - for public values only (ECDSA verification). nil if A has no inverse.
function BigModInvOdd(const A, M: TBig): TBig;
// the bit-by-bit binary Euclid (32-bit limbs, any size): for tests
function BigModInvOdd32(const A, M: TBig): TBig;

var
  // Montgomery exponentiation for odd moduli (False: the old division-based code;
  // tests compare both)
  BigUseMont: Boolean = True;
  // the MULX/ADX kernel for moduli of a multiple of 256 bits (tests switch it off)
  BigUseMontx: Boolean = True;
  // the dedicated squaring kernel (with MULX; tests switch it off)
  BigUseMontSqr: Boolean = True;

implementation

uses XelSslCpu;

procedure Norm(var A: TBig); inline;
var n: Integer;
begin
  n := Length(A);
  while (n > 0) and (A[n - 1] = 0) do Dec(n);
  SetLength(A, n);
end;

function BigFromBytes(const B: TBytes): TBig;
var i, n: Integer;
begin
  n := (Length(B) + 3) div 4;
  SetLength(Result, n);
  for i := 0 to n - 1 do Result[i] := 0;
  for i := 0 to High(B) do
    Result[(Length(B) - 1 - i) div 4] := Result[(Length(B) - 1 - i) div 4] or
      (UInt32(B[i]) shl (8 * ((Length(B) - 1 - i) mod 4)));
  Norm(Result);
end;

function BigFromHex(const S: string): TBig;
var t: string; i: Integer; b: TBytes;
begin
  t := '';
  for i := 1 to Length(S) do if S[i] in ['0'..'9', 'a'..'f', 'A'..'F'] then t := t + S[i];
  if Odd(Length(t)) then t := '0' + t;
  SetLength(b, Length(t) div 2);
  for i := 0 to High(b) do b[i] := StrToInt('$' + Copy(t, i * 2 + 1, 2));
  Result := BigFromBytes(b);
end;

function BigFromInt(V: UInt32): TBig;
begin
  if V = 0 then Result := nil
  else begin SetLength(Result, 1); Result[0] := V; end;
end;

function BigToBytes(const A: TBig; Len: Integer): TBytes;
var i, nb: Integer;
begin
  nb := (BigBits(A) + 7) div 8;
  if Len = 0 then Len := nb;
  if nb > Len then raise Exception.Create('XelSSL BigNum: number too long');
  SetLength(Result, Len);
  FillChar(Result[0], Len, 0);
  for i := 0 to nb - 1 do
    Result[Len - 1 - i] := Byte(A[i div 4] shr (8 * (i mod 4)));
end;

function BigIsZero(const A: TBig): Boolean;
begin Result := Length(A) = 0; end;

function BigCmp(const A, B: TBig): Integer;
var i: Integer;
begin
  if Length(A) <> Length(B) then
  begin
    if Length(A) > Length(B) then Exit(1) else Exit(-1);
  end;
  for i := High(A) downto 0 do
    if A[i] <> B[i] then
    begin
      if A[i] > B[i] then Exit(1) else Exit(-1);
    end;
  Result := 0;
end;

function BigBits(const A: TBig): Integer;
var t: UInt32;
begin
  if Length(A) = 0 then Exit(0);
  Result := (Length(A) - 1) * 32;
  t := A[High(A)];
  while t <> 0 do begin Inc(Result); t := t shr 1; end;
end;

function BigBit(const A: TBig; I: Integer): Integer;
begin
  if I shr 5 >= Length(A) then Result := 0
  else Result := (A[I shr 5] shr (I and 31)) and 1;
end;

function BigAdd(const A, B: TBig): TBig;
var i, n: Integer; c: UInt64;
begin
  n := Length(A); if Length(B) > n then n := Length(B);
  SetLength(Result, n + 1);
  c := 0;
  for i := 0 to n - 1 do
  begin
    if i < Length(A) then c := c + A[i];
    if i < Length(B) then c := c + B[i];
    Result[i] := UInt32(c);
    c := c shr 32;
  end;
  Result[n] := UInt32(c);
  Norm(Result);
end;

function BigSub(const A, B: TBig): TBig;
var i: Integer; t: Int64; borrow: Int64;
begin
  SetLength(Result, Length(A));
  borrow := 0;
  for i := 0 to High(A) do
  begin
    t := Int64(A[i]) - borrow;
    if i < Length(B) then t := t - B[i];
    if t < 0 then begin t := t + (Int64(1) shl 32); borrow := 1; end else borrow := 0;
    Result[i] := UInt32(t);
  end;
  if borrow <> 0 then raise Exception.Create('XelSSL BigNum: negative subtraction result');
  Norm(Result);
end;

function BigMul(const A, B: TBig): TBig;
var i, j: Integer; c: UInt64;
begin
  if (Length(A) = 0) or (Length(B) = 0) then Exit(nil);
  SetLength(Result, Length(A) + Length(B));
  for i := 0 to High(Result) do Result[i] := 0;
  for i := 0 to High(A) do
  begin
    c := 0;
    for j := 0 to High(B) do
    begin
      c := c + UInt64(A[i]) * B[j] + Result[i + j];
      Result[i + j] := UInt32(c);
      c := c shr 32;
    end;
    Result[i + Length(B)] := UInt32(c);
  end;
  Norm(Result);
end;

function Nlz(X: UInt32): Integer;
begin
  Result := 0;
  if X = 0 then Exit(32);
  while (X and $80000000) = 0 do begin Inc(Result); X := X shl 1; end;
end;

procedure BigDivMod(const U, V: TBig; out Q, R: TBig);
const B = UInt64($100000000);
var
  m, n, s, i, j: Integer;
  un, vn: array of UInt32;
  qhat, rhat, p, rem: UInt64; t, k: Int64;
begin
  if Length(V) = 0 then raise EDivByZero.Create('XelSSL BigNum: division by zero');
  if BigCmp(U, V) < 0 then begin Q := nil; R := Copy(U); Exit; end;
  n := Length(V); m := Length(U) - n;
  SetLength(Q, m + 1);
  if n = 1 then
  begin
    rem := 0;
    for j := High(U) downto 0 do
    begin
      rem := (rem shl 32) or U[j];
      Q[j] := UInt32(rem div V[0]);
      rem := rem mod V[0];
    end;
    Norm(Q);
    R := BigFromInt(UInt32(rem));
    Exit;
  end;
  s := Nlz(V[n - 1]);
  SetLength(vn, n);
  for i := n - 1 downto 1 do
    if s > 0 then vn[i] := (V[i] shl s) or (V[i - 1] shr (32 - s)) else vn[i] := V[i];
  vn[0] := V[0] shl s;
  SetLength(un, m + n + 1);
  if s > 0 then un[m + n] := U[m + n - 1] shr (32 - s) else un[m + n] := 0;
  for i := m + n - 1 downto 1 do
    if s > 0 then un[i] := (U[i] shl s) or (U[i - 1] shr (32 - s)) else un[i] := U[i];
  un[0] := U[0] shl s;
  for j := m downto 0 do
  begin
    p := (UInt64(un[j + n]) shl 32) or un[j + n - 1];
    qhat := p div vn[n - 1];
    rhat := p mod vn[n - 1];
    while (qhat >= B) or (qhat * vn[n - 2] > (rhat shl 32) + un[j + n - 2]) do
    begin
      Dec(qhat);
      rhat := rhat + vn[n - 1];
      if rhat >= B then Break;
    end;
    k := 0;
    for i := 0 to n - 1 do
    begin
      p := qhat * vn[i];
      t := Int64(un[i + j]) - k - Int64(p and $FFFFFFFF);
      un[i + j] := UInt32(t);
      k := Int64(p shr 32) - SarInt64(t, 32);
    end;
    t := Int64(un[j + n]) - k;
    un[j + n] := UInt32(t);
    Q[j] := UInt32(qhat);
    if t < 0 then
    begin
      Q[j] := Q[j] - 1;
      k := 0;
      for i := 0 to n - 1 do
      begin
        t := Int64(un[i + j]) + vn[i] + k;
        un[i + j] := UInt32(t);
        k := t shr 32;
      end;
      un[j + n] := un[j + n] + UInt32(k);
    end;
  end;
  Norm(Q);
  SetLength(R, n);
  for i := 0 to n - 1 do
    if s > 0 then R[i] := (un[i] shr s) or (un[i + 1] shl (32 - s)) else R[i] := un[i];
  Norm(R);
end;

function BigMod(const A, M: TBig): TBig;
var q: TBig;
begin
  BigDivMod(A, M, q, Result);
end;

function BigShr(const A: TBig; N: Integer): TBig;
var w, b, i: Integer;
begin
  w := N shr 5; b := N and 31;
  if w >= Length(A) then Exit(nil);
  SetLength(Result, Length(A) - w);
  for i := 0 to High(Result) do
  begin
    Result[i] := A[i + w] shr b;
    if (b > 0) and (i + w + 1 < Length(A)) then Result[i] := Result[i] or (A[i + w + 1] shl (32 - b));
  end;
  Norm(Result);
end;

function BigModAdd(const A, B, M: TBig): TBig;
begin
  Result := BigAdd(A, B);
  if BigCmp(Result, M) >= 0 then Result := BigSub(Result, M);
end;

function BigModSub(const A, B, M: TBig): TBig;
begin
  if BigCmp(A, B) >= 0 then Result := BigSub(A, B)
  else Result := BigSub(BigAdd(A, M), B);
end;

function BigModMul(const A, B, M: TBig): TBig;
begin
  Result := BigMod(BigMul(A, B), M);
end;

function BigModExpDiv(const Base, Exp, M: TBig): TBig; forward;

// ---- Montgomery arithmetic (odd moduli) ----

type
  TMont = record
    NL: Integer;              // 32-bit limbs (even when the assembler is used: R = 2^(32 * NL))
    N, RR: array of UInt32;   // modulus, R^2 mod N
    M32: UInt32;              // -N^-1 mod 2^32
    M64: UInt64;              // -N^-1 mod 2^64
    Hw: Boolean;
    Mx: Boolean;              // MULX/ADX kernel (64-bit limb count a multiple of 4)
  end;

{$IFDEF XELSSL_X64}
// T[0..K] := A*B*2^(-64K) (T < 2N, T[K] = carry 0/1). One pass per word of B: the
// product and the reduction share the loop (two carry chains). M = -N^-1 mod 2^64.
procedure HwMont(T, A, B, N: PUInt64; K: Integer; M: UInt64);
var pt, pa, pb, pn: Pointer; cnt: PtrInt; mm: UInt64;
begin
  pt := T; pa := A; pb := B; pn := N; cnt := K; mm := M;
  asm
    mov rax, pt
    mov rcx, pa
    mov rdx, pb
    mov r8, pn
    mov r9, cnt
    mov r10, mm
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    push rbp
    mov rbx, rax
    mov rsi, rcx
    mov rdi, rdx
    // t[0..k] := 0
    xor rax, rax
    lea rcx, [r9 + 1]
    mov rdx, rbx
  @zero:
    mov [rdx], rax
    add rdx, 8
    dec rcx
    jnz @zero
    xor r11, r11                             // i
  @outer:
    cmp r11, r9
    jae @done
    mov r15, [rdi + r11 * 8]                 // b[i]
    // word 0: m = (t0 + a0*b[i]) * M, its reduction term cancels the low word
    mov rax, [rsi]
    mul r15
    add rax, [rbx]
    adc rdx, 0
    mov r13, rdx                             // carry of the product chain
    mov rbp, rax
    mov rcx, rax
    imul rcx, r10                            // m
    mov rax, rcx
    mul qword ptr [r8]
    add rax, rbp
    adc rdx, 0
    mov r14, rdx                             // carry of the reduction chain
    mov r12, 1
  @inner:
    cmp r12, r9
    jae @top
    mov rax, [rsi + r12 * 8]
    mul r15
    add rax, [rbx + r12 * 8]
    adc rdx, 0
    add rax, r13
    adc rdx, 0
    mov r13, rdx
    mov rbp, rax
    mov rax, [r8 + r12 * 8]
    mul rcx
    add rax, rbp
    adc rdx, 0
    add rax, r14
    adc rdx, 0
    mov r14, rdx
    mov [rbx + r12 * 8 - 8], rax
    inc r12
    jmp @inner
  @top:
    xor rdx, rdx
    mov rax, r13
    add rax, r14
    adc rdx, 0
    add rax, [rbx + r9 * 8]
    adc rdx, 0
    mov [rbx + r9 * 8 - 8], rax
    mov [rbx + r9 * 8], rdx
    inc r11
    jmp @outer
  @done:
    pop rbp
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
type
  // parameters of the generated MULX kernel (offsets in test/gen_mont_asm.py)
  TMontxCtx = record
    T, A, B, N: Pointer;
    K: Int64;
    M: UInt64;
    K4: Int64;
    R: Pointer;                    // the result (the kernel does the final subtraction)
  end;

  // the squaring kernel (test/gen_montsqr_asm.py)
  TMontSqrxCtx = record
    T, A, P, N: Pointer;           // P: work area of 2K + 1 words
    K: Int64;
    M: UInt64;
    K4, G, RC: Int64;
    R: Pointer;
  end;

procedure HwMontx(Ctx: Pointer);
var p: Pointer;
begin
  p := Ctx;
  asm
    mov rax, p
    {$I XelSslMontx.inc}
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11'];
end;

procedure HwMontSqrx(Ctx: Pointer);
var p: Pointer;
begin
  p := Ctx;
  asm
    mov rax, p
    {$I XelSslMontSqrx.inc}
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11'];
end;
{$ENDIF}

// R := A*B*R^-1 mod N (R < N); R may be A or B. T: work area of NL + 4 limbs, with two
// more limbs in front of it (the MULX kernel writes one 64-bit word below T).
procedure MontMul(const C: TMont; R, A, B, T: PUInt32);
var i, j, nl: Integer; cy, cy2: UInt64; m, top, borrow, mask: UInt32; d: Int64;
  {$IFDEF XELSSL_X64}mx: TMontxCtx;{$ENDIF}
begin
  nl := C.NL;
  {$IFDEF XELSSL_X64}
  if C.Mx then
  begin
    mx.T := T; mx.A := A; mx.B := B; mx.N := @C.N[0];
    mx.K := nl div 2; mx.M := C.M64; mx.K4 := nl div 8; mx.R := R;
    HwMontx(@mx);                    // including the final subtraction
    Exit;
  end
  else if C.Hw then
  begin
    HwMont(PUInt64(T), PUInt64(A), PUInt64(B), PUInt64(@C.N[0]), nl div 2, C.M64);
    top := T[nl];
  end
  else
  {$ENDIF}
  begin
    for i := 0 to nl + 1 do T[i] := 0;
    for i := 0 to nl - 1 do
    begin
      cy := 0;
      for j := 0 to nl - 1 do
      begin
        cy := cy + T[j] + UInt64(A[j]) * B[i];
        T[j] := UInt32(cy);
        cy := cy shr 32;
      end;
      cy := cy + T[nl];
      T[nl] := UInt32(cy);
      T[nl + 1] := UInt32(cy shr 32);
      m := T[0] * C.M32;
      cy2 := (UInt64(T[0]) + UInt64(m) * C.N[0]) shr 32;
      for j := 1 to nl - 1 do
      begin
        cy2 := cy2 + T[j] + UInt64(m) * C.N[j];
        T[j - 1] := UInt32(cy2);
        cy2 := cy2 shr 32;
      end;
      cy2 := cy2 + T[nl];
      T[nl - 1] := UInt32(cy2);
      T[nl] := T[nl + 1] + UInt32(cy2 shr 32);
    end;
    top := T[nl];
  end;
  // T < 2N: subtract N when T >= N (the carry word set, or no borrow) - masked
  borrow := 0;
  for i := 0 to nl - 1 do
  begin
    d := Int64(T[i]) - C.N[i] - borrow;
    R[i] := UInt32(d);
    borrow := UInt32(d shr 63) and 1;
  end;
  // keep T when top = 0 and there was a borrow
  mask := UInt32(0) - (borrow and (1 - (top and 1)));
  for i := 0 to nl - 1 do R[i] := (R[i] and not mask) or (T[i] and mask);
end;

// R := A*A*R^-1 mod N; the squaring kernel computes the cross products once.
// W: work area of 2 * NL + 4 limbs (MULX path); otherwise MontMul(A, A).
procedure MontSqr(const C: TMont; R, A, T, W: PUInt32);
{$IFDEF XELSSL_X64}var sq: TMontSqrxCtx;{$ENDIF}
begin
  {$IFDEF XELSSL_X64}
  if C.Mx and BigUseMontSqr then
  begin
    sq.T := T; sq.A := A; sq.P := W; sq.N := @C.N[0];
    sq.K := C.NL div 2; sq.M := C.M64; sq.K4 := C.NL div 8; sq.R := R;
    HwMontSqrx(@sq);
    Exit;
  end;
  {$ENDIF}
  MontMul(C, R, A, A, T);
end;

const
  MONT_CACHE = 8;

var
  MontCacheLock: TRTLCriticalSection;
  MontCacheN, MontCacheRR: array[0..MONT_CACHE - 1] of TBig;
  MontCacheNL: array[0..MONT_CACHE - 1] of Integer;
  MontCacheNext: Integer = 0;

// -x^-1 mod 2^64 for odd x (Newton's iteration doubles the correct bits)
function NegInv64(X: UInt64): UInt64;
var y: UInt64; k: Integer;
begin
  y := X;                                        // correct to 3 bits
  for k := 1 to 6 do y := y * (2 - X * y);
  Result := UInt64(0) - y;
end;

procedure MontInit(out C: TMont; const M: TBig);
var i: Integer; rr: TBig; found: Boolean;
begin
  C.NL := Length(M);
  {$IFDEF XELSSL_X64}
  C.Hw := XelSslAsm and AsmAvailable([cfSse2]);
  if C.Hw and Odd(C.NL) then Inc(C.NL);
  C.Mx := C.Hw and BigUseMontx and AsmAvailable([cfBmi2, cfAdx]) and (C.NL mod 8 = 0);
  {$ELSE}
  C.Hw := False;
  C.Mx := False;
  {$ENDIF}
  SetLength(C.N, C.NL);
  for i := 0 to C.NL - 1 do
    if i < Length(M) then C.N[i] := M[i] else C.N[i] := 0;
  C.M64 := NegInv64(UInt64(C.N[0]) or (UInt64(C.N[1 mod C.NL]) shl 32));
  if C.NL = 1 then C.M64 := NegInv64(C.N[0]);
  C.M32 := UInt32(C.M64);
  // R^2 mod N from the cache (R depends on the limb count), else by division
  found := False;
  EnterCriticalSection(MontCacheLock);
  try
    for i := 0 to MONT_CACHE - 1 do
      if (MontCacheNL[i] = C.NL) and (BigCmp(MontCacheN[i], M) = 0) then
      begin
        rr := MontCacheRR[i];
        found := True;
        Break;
      end;
  finally
    LeaveCriticalSection(MontCacheLock);
  end;
  if not found then
  begin
    SetLength(rr, 2 * C.NL + 1);
    for i := 0 to High(rr) do rr[i] := 0;
    rr[2 * C.NL] := 1;                            // 2^(64 * NL) = R^2
    rr := BigMod(rr, M);
    EnterCriticalSection(MontCacheLock);
    try
      MontCacheN[MontCacheNext] := Copy(M);
      MontCacheRR[MontCacheNext] := rr;
      MontCacheNL[MontCacheNext] := C.NL;
      MontCacheNext := (MontCacheNext + 1) mod MONT_CACHE;
    finally
      LeaveCriticalSection(MontCacheLock);
    end;
  end;
  SetLength(C.RR, C.NL);
  for i := 0 to C.NL - 1 do
    if i < Length(rr) then C.RR[i] := rr[i] else C.RR[i] := 0;
end;

function MontModExp(const Base, Exp, M: TBig): TBig;
var
  C: TMont; nl, i, j, w, bits, top: Integer; b: TBig;
  x, acc, t, one, sel, wk: array of UInt32; tab: array of array of UInt32; mask, d: UInt32;
begin
  MontInit(C, M);
  nl := C.NL;
  // t: 2 limbs in front of the work area (the MULX kernel), NL + 4 limbs after them
  SetLength(x, nl); SetLength(acc, nl); SetLength(t, nl + 8); SetLength(wk, 2 * nl + 8); SetLength(one, nl); SetLength(sel, nl);
  if BigCmp(Base, M) < 0 then b := Base else b := BigMod(Base, M);   // e.g. signatures are < n
  for i := 0 to nl - 1 do
  begin
    if i < Length(b) then x[i] := b[i] else x[i] := 0;
    one[i] := 0;
  end;
  one[0] := 1;
  MontMul(C, @x[0], @x[0], @C.RR[0], @t[2]);       // x in Montgomery form
  bits := BigBits(Exp);
  if bits = 0 then
  begin
    MontMul(C, @acc[0], @one[0], @C.RR[0], @t[2]);  // 1 (mod M)
  end
  else if bits <= 64 then
  begin
    // short public exponent: bit by bit
    acc := Copy(x);
    for i := bits - 2 downto 0 do
    begin
      MontSqr(C, @acc[0], @acc[0], @t[2], @wk[0]);
      if BigBit(Exp, i) = 1 then MontMul(C, @acc[0], @acc[0], @x[0], @t[2]);
    end;
  end
  else
  begin
    // long (possibly secret) exponent: fixed 4-bit windows, every window does 4
    // squarings and one multiplication with a table entry read in constant time
    SetLength(tab, 16);
    for j := 0 to 15 do SetLength(tab[j], nl);
    MontMul(C, @tab[0][0], @one[0], @C.RR[0], @t[2]);
    for j := 1 to 15 do MontMul(C, @tab[j][0], @tab[j - 1][0], @x[0], @t[2]);
    top := ((bits + 3) div 4) * 4;
    acc := Copy(tab[0]);
    i := top - 4;
    while i >= 0 do
    begin
      for w := 1 to 4 do MontSqr(C, @acc[0], @acc[0], @t[2], @wk[0]);
      d := (UInt32(BigBit(Exp, i + 3)) shl 3) or (UInt32(BigBit(Exp, i + 2)) shl 2) or
           (UInt32(BigBit(Exp, i + 1)) shl 1) or UInt32(BigBit(Exp, i));
      for w := 0 to nl - 1 do sel[w] := 0;
      for j := 0 to 15 do
      begin
        // all ones when j = d (a 32-bit variable: FPC computes UInt32 - 1 as Int64)
        mask := UInt32(j) xor d;
        mask := mask - 1;
        mask := UInt32(0) - (mask shr 31);
        for w := 0 to nl - 1 do sel[w] := sel[w] or (tab[j][w] and mask);
      end;
      MontMul(C, @acc[0], @acc[0], @sel[0], @t[2]);
      Dec(i, 4);
    end;
    for j := 0 to 15 do FillChar(tab[j][0], nl * 4, 0);
  end;
  MontMul(C, @acc[0], @acc[0], @one[0], @t[2]);    // out of Montgomery form
  SetLength(Result, nl);
  for i := 0 to nl - 1 do Result[i] := acc[i];
  Norm(Result);
  FillChar(x[0], nl * 4, 0); FillChar(acc[0], nl * 4, 0); FillChar(t[0], (nl + 8) * 4, 0);
  FillChar(sel[0], nl * 4, 0); FillChar(wk[0], Length(wk) * 4, 0);
end;

function BigModExp(const Base, Exp, M: TBig): TBig;
begin
  if BigUseMont and (Length(M) > 0) and Odd(M[0]) and not ((Length(M) = 1) and (M[0] = 1)) then
    Result := MontModExp(Base, Exp, M)
  else
    Result := BigModExpDiv(Base, Exp, M);
end;

// square-and-multiply with a division after each step (even moduli, tests)
function BigModExpDiv(const Base, Exp, M: TBig): TBig;
var i: Integer; b: TBig;
begin
  Result := BigFromInt(1);
  b := BigMod(Base, M);
  for i := BigBits(Exp) - 1 downto 0 do
  begin
    Result := BigModMul(Result, Result, M);
    if BigBit(Exp, i) = 1 then Result := BigModMul(Result, b, M);
  end;
  Result := BigMod(Result, M);
end;

// ---- inverse modulo an odd number (variable time, public data) ----

const
  INVQ = 10;                     // 64-bit limbs: moduli up to 576 bits plus a carry limb

type
  TQ = array[0..INVQ - 1] of UInt64;

procedure QShr1(var W: TQ; N: Integer); inline;
var i: Integer;
begin
  for i := 0 to N - 2 do W[i] := (W[i] shr 1) or (W[i + 1] shl 63);
  W[N - 1] := W[N - 1] shr 1;
end;

procedure QAdd(var W: TQ; const B: TQ; N: Integer); inline;
var i: Integer; c, t: UInt64;
begin
  c := 0;
  for i := 0 to N - 1 do
  begin
    t := W[i] + c; c := Ord(t < c);
    W[i] := t + B[i]; c := c + Ord(W[i] < t);
  end;
end;

procedure QSub(var W: TQ; const B: TQ; N: Integer); inline;
var i: Integer; t, bw, b1: UInt64;
begin
  bw := 0;
  for i := 0 to N - 1 do
  begin
    t := W[i] - B[i]; b1 := Ord(W[i] < B[i]);
    W[i] := t - bw; bw := b1 + Ord(t < bw);
  end;
end;

function QGE(const X, Y: TQ; N: Integer): Boolean; inline;
var i: Integer;
begin
  for i := N - 1 downto 0 do
    if X[i] <> Y[i] then Exit(X[i] > Y[i]);
  Result := True;
end;

function QIsOne(const W: TQ; N: Integer): Boolean; inline;
var i: Integer;
begin
  if W[0] <> 1 then Exit(False);
  for i := 1 to N - 1 do if W[i] <> 0 then Exit(False);
  Result := True;
end;

function QIsZero(const W: TQ; N: Integer): Boolean; inline;
var i: Integer;
begin
  for i := 0 to N - 1 do if W[i] <> 0 then Exit(False);
  Result := True;
end;

function BigModInvOddQ(const A, M: TBig): TBig; forward;

// ---- binary GCD on approximations (T. Pornin, "Optimized Binary GCD for Modular
// Inversion", 2020), variable time ----
// 30 steps of the binary GCD run on 62-bit approximations of a and b (the low 30 bits
// exact, the top 32 bits); the 2x2 matrix of those steps is then applied once to the
// whole numbers. Limbs of 30 bits in Int64: every product stays far below 2^63.

const
  GL = 24;                       // 30-bit limbs: moduli up to 690 bits
  GMASK = (Int64(1) shl 30) - 1;

type
  TG = array[0..GL + 2] of Int64;    // two zero limbs above for the bit extraction

function GBits(const W: TG; N: Integer): Integer;
var i: Integer;
begin
  for i := N - 1 downto 0 do
    if W[i] <> 0 then Exit(30 * i + BsrQWord(QWord(W[i])) + 1);
  Result := 0;
end;

// 32 bits of W from bit Pos
function GTop(const W: TG; Pos: Integer): UInt64;
var li, off: Integer;
begin
  li := Pos div 30; off := Pos mod 30;
  Result := (UInt64(W[li]) shr off) or (UInt64(W[li + 1]) shl (30 - off)) or
            (UInt64(W[li + 2]) shl (60 - off));
  Result := Result and $FFFFFFFF;
end;

// R := (A * F + B * G) / 2^30 (exact); a negative result is negated, then True
function GComb(const A, B: TG; F, G: Int64; out R: TG; N: Integer): Boolean;
var i: Integer; t, c: Int64;
begin
  FillChar(R, SizeOf(R), 0);
  c := 0;
  for i := 0 to N - 1 do
  begin
    t := A[i] * F + B[i] * G + c;
    if i > 0 then R[i - 1] := t and GMASK;
    c := SarInt64(t, 30);
  end;
  R[N - 1] := c;
  Result := c < 0;
  if Result then
  begin
    c := 0;
    for i := 0 to N - 2 do
    begin
      t := c - R[i];
      R[i] := t and GMASK;
      c := SarInt64(t, 30);
    end;
    R[N - 1] := c - R[N - 1];
  end;
end;

// R := (U * F + V * G) / 2^30 mod M (U, V, R in [0, M)); M0I = -M^-1 mod 2^30
procedure GCombMod(const U, V: TG; F, G: Int64; const M: TG; M0I: Int64; out R: TG; N: Integer);
var i: Integer; t, c, q: Int64; neg, ge: Boolean;
begin
  FillChar(R, SizeOf(R), 0);
  q := (((U[0] * F + V[0] * G) and GMASK) * M0I) and GMASK;
  c := 0;
  for i := 0 to N - 1 do
  begin
    t := U[i] * F + V[i] * G + q * M[i] + c;
    if i > 0 then R[i - 1] := t and GMASK;
    c := SarInt64(t, 30);
  end;
  R[N - 1] := c;
  // the value lies in (-M, 2M): one correction
  neg := c < 0;
  if not neg then
  begin
    ge := True;
    for i := N - 1 downto 0 do
      if R[i] <> M[i] then begin ge := R[i] > M[i]; Break; end;
    if not ge then Exit;
  end;
  c := 0;
  for i := 0 to N - 1 do
  begin
    if neg then t := R[i] + M[i] + c else t := R[i] - M[i] + c;
    if i < N - 1 then begin R[i] := t and GMASK; c := SarInt64(t, 30); end
    else R[i] := t;
  end;
end;

function BigModInvOdd(const A, M: TBig): TBig;
var
  ga, gb, gu, gv, mm, na, nb: TG; n, bits, i, j, iter, lim: Integer; a_: TBig;
  xa, xb, xt: UInt64; f0, g0, f1, g1, ft, m0i, inv: Int64;

  // 32-bit limbs -> 30-bit limbs
  procedure Load(out W: TG; const B: TBig);
  var k, nbits, o: Integer; acc: UInt64;
  begin
    FillChar(W, SizeOf(W), 0);
    acc := 0; nbits := 0; o := 0;
    for k := 0 to High(B) do
    begin
      acc := acc or (UInt64(B[k]) shl nbits); Inc(nbits, 32);
      while nbits >= 30 do
      begin
        W[o] := Int64(acc and GMASK); Inc(o);
        acc := acc shr 30; Dec(nbits, 30);
      end;
    end;
    W[o] := Int64(acc);
  end;

begin
  Result := nil;
  if (Length(M) = 0) or (M[0] and 1 = 0) then Exit;
  bits := BigBits(M);
  n := (bits + 29) div 30 + 1;
  if n > GL then Exit(BigModInvOddQ(A, M));
  a_ := BigMod(A, M);
  if Length(a_) = 0 then Exit;
  Load(mm, M); Load(ga, a_); gb := mm;
  FillChar(gu, SizeOf(gu), 0); gu[0] := 1;
  FillChar(gv, SizeOf(gv), 0);
  // -M^-1 mod 2^30 (Newton: each step doubles the correct low bits)
  inv := mm[0];
  for i := 1 to 5 do inv := (inv * (2 - mm[0] * inv)) and GMASK;
  m0i := (-inv) and GMASK;
  lim := (2 * bits) div 30 + 4;
  iter := 0;
  while GBits(ga, n) > 0 do
  begin
    Inc(iter);
    if iter > lim then Exit(BigModInvOddQ(A, M));      // not expected: the proven bound
    j := GBits(ga, n); i := GBits(gb, n); if i > j then j := i;
    if j < 62 then j := 62;
    // low 30 bits exact, the top 32 bits of the common length
    xa := (UInt64(ga[0]) and GMASK) or (GTop(ga, j - 32) shl 30);
    xb := (UInt64(gb[0]) and GMASK) or (GTop(gb, j - 32) shl 30);
    f0 := 1; g0 := 0; f1 := 0; g1 := 1;
    for i := 1 to 30 do
    begin
      if xa and 1 = 0 then
        xa := xa shr 1
      else
      begin
        if xa < xb then
        begin
          xt := xa; xa := xb; xb := xt;
          ft := f0; f0 := f1; f1 := ft;
          ft := g0; g0 := g1; g1 := ft;
        end;
        xa := (xa - xb) shr 1;
        f0 := f0 - f1; g0 := g0 - g1;
      end;
      f1 := f1 * 2; g1 := g1 * 2;
    end;
    if GComb(ga, gb, f0, g0, na, n) then begin f0 := -f0; g0 := -g0; end;
    if GComb(ga, gb, f1, g1, nb, n) then begin f1 := -f1; g1 := -g1; end;
    ga := na; gb := nb;
    GCombMod(gu, gv, f0, g0, mm, m0i, na, n);
    GCombMod(gu, gv, f1, g1, mm, m0i, nb, n);
    gu := na; gv := nb;
  end;
  // gb = gcd(ga, m)
  if (gb[0] <> 1) or (GBits(gb, n) <> 1) then Exit;
  // 30-bit limbs -> 32-bit limbs
  SetLength(Result, (30 * n + 31) div 32 + 1);
  xa := 0; j := 0; iter := 0;
  for i := 0 to n - 1 do
  begin
    xa := xa or (UInt64(gv[i]) shl j); Inc(j, 30);
    if j >= 32 then
    begin
      Result[iter] := UInt32(xa); Inc(iter);
      xa := xa shr 32; Dec(j, 32);
    end;
  end;
  while iter < Length(Result) do begin Result[iter] := UInt32(xa); xa := xa shr 32; Inc(iter); end;
  Norm(Result);
end;

// binary extended Euclid on 64-bit limbs (one limb more than M for the carries)
function BigModInvOddQ(const A, M: TBig): TBig;
var u, v, x1, x2, mm: TQ; n, i: Integer; a_: TBig;
  procedure Load(out W: TQ; const B: TBig);
  var k: Integer;
  begin
    FillChar(W, SizeOf(W), 0);
    for k := 0 to High(B) do
      W[k shr 1] := W[k shr 1] or (UInt64(B[k]) shl (32 * (k and 1)));
  end;
begin
  Result := nil;
  if (Length(M) = 0) or (M[0] and 1 = 0) then Exit;
  n := (Length(M) + 1) div 2 + 1;
  if n > INVQ then Exit(BigModInvOdd32(A, M));
  a_ := BigMod(A, M);
  if Length(a_) = 0 then Exit;
  Load(mm, M);
  Load(u, a_);
  v := mm;
  FillChar(x1, SizeOf(x1), 0); x1[0] := 1;
  FillChar(x2, SizeOf(x2), 0);
  while not QIsOne(u, n) and not QIsOne(v, n) do
  begin
    if QIsZero(u, n) or QIsZero(v, n) then Exit;     // gcd > 1
    while u[0] and 1 = 0 do
    begin
      QShr1(u, n);
      if x1[0] and 1 = 1 then QAdd(x1, mm, n);     // x1 / 2 mod m
      QShr1(x1, n);
    end;
    while v[0] and 1 = 0 do
    begin
      QShr1(v, n);
      if x2[0] and 1 = 1 then QAdd(x2, mm, n);
      QShr1(x2, n);
    end;
    if QGE(u, v, n) then
    begin
      QSub(u, v, n);
      if not QGE(x1, x2, n) then QAdd(x1, mm, n);
      QSub(x1, x2, n);
    end
    else
    begin
      QSub(v, u, n);
      if not QGE(x2, x1, n) then QAdd(x2, mm, n);
      QSub(x2, x1, n);
    end;
  end;
  if not QIsOne(u, n) then x1 := x2;
  SetLength(Result, 2 * n);
  for i := 0 to n - 1 do
  begin
    Result[2 * i] := UInt32(x1[i]);
    Result[2 * i + 1] := UInt32(x1[i] shr 32);
  end;
  Norm(Result);
end;

// the same on 32-bit limbs (larger moduli)
function BigModInvOdd32(const A, M: TBig): TBig;
const
  MAXW = 20;
type
  TW = array[0..MAXW - 1] of UInt32;
var
  u, v, x1, x2, mm: TW; n: Integer;

  procedure Load(out W: TW; const B: TBig);
  var i: Integer;
  begin
    FillChar(W, SizeOf(W), 0);
    for i := 0 to High(B) do W[i] := B[i];
  end;
  function IsOne(const W: TW): Boolean;
  var i: Integer;
  begin
    if W[0] <> 1 then Exit(False);
    for i := 1 to n do if W[i] <> 0 then Exit(False);
    Result := True;
  end;
  function IsZeroW(const W: TW): Boolean;
  var i: Integer;
  begin
    for i := 0 to n do if W[i] <> 0 then Exit(False);
    Result := True;
  end;
  procedure Shr1(var W: TW);
  var i: Integer;
  begin
    for i := 0 to n - 1 do W[i] := (W[i] shr 1) or (W[i + 1] shl 31);
    W[n] := W[n] shr 1;
  end;
  procedure AddW(var W: TW; const B: TW);
  var i: Integer; c: UInt64;
  begin
    c := 0;
    for i := 0 to n do begin c := c + W[i] + B[i]; W[i] := UInt32(c); c := c shr 32; end;
  end;
  procedure SubW(var W: TW; const B: TW);
  var i: Integer; d: Int64; br: UInt32;
  begin
    br := 0;
    for i := 0 to n do
    begin
      d := Int64(W[i]) - B[i] - br;
      W[i] := UInt32(d);
      br := UInt32(QWord(d) shr 63);
    end;
  end;
  function GE(const X, Y: TW): Boolean;
  var i: Integer;
  begin
    for i := n downto 0 do
      if X[i] <> Y[i] then Exit(X[i] > Y[i]);
    Result := True;
  end;
  // x := x / 2 mod m (x < m)
  procedure Half(var X: TW);
  begin
    if X[0] and 1 = 1 then AddW(X, mm);
    Shr1(X);
  end;
  // x := x - y mod m (x, y < m)
  procedure SubMod(var X: TW; const Y: TW);
  begin
    if not GE(X, Y) then AddW(X, mm);
    SubW(X, Y);
  end;
  function Store(const W: TW): TBig;
  var i: Integer;
  begin
    SetLength(Result, n + 1);
    for i := 0 to n do Result[i] := W[i];
    Norm(Result);
  end;

begin
  Result := nil;
  n := Length(M);                               // one limb more than M for the carries
  if (n = 0) or (n >= MAXW) or (M[0] and 1 = 0) then Exit;
  Load(mm, M);
  Load(u, BigMod(A, M));
  if IsZeroW(u) then Exit;
  v := mm;
  FillChar(x1, SizeOf(x1), 0); x1[0] := 1;
  FillChar(x2, SizeOf(x2), 0);
  while not IsOne(u) and not IsOne(v) do
  begin
    if IsZeroW(u) or IsZeroW(v) then Exit;      // gcd > 1
    while u[0] and 1 = 0 do begin Shr1(u); Half(x1); end;
    while v[0] and 1 = 0 do begin Shr1(v); Half(x2); end;
    if GE(u, v) then begin SubW(u, v); SubMod(x1, x2); end
    else begin SubW(v, u); SubMod(x2, x1); end;
  end;
  if IsOne(u) then Result := Store(x1) else Result := Store(x2);
end;

function BigModInvPrime(const A, P: TBig): TBig;
begin
  Result := BigModExp(A, BigSub(P, BigFromInt(2)), P);
end;

initialization
  InitCriticalSection(MontCacheLock);
finalization
  DoneCriticalSection(MontCacheLock);
end.
