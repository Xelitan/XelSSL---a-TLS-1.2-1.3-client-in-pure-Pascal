// XelSSL - X25519 (RFC 7748): Montgomery ladder with branch-free conditional swaps
// (constant time). Field arithmetic: XelSslFe25519 (Pascal, or the x86-64 addition);
// on x86-64 with BMI2 + ADX: 4 x 64-bit limbs kept below 2^256 (2^256 = 38 mod p),
// MULX/ADCX/ADOX kernels from test/gen_x25519_asm.py. License: MIT.
unit XelSslX25519;

{$mode objfpc}{$H+}{$Q-}{$R-}
{$IFDEF CPUX86_64}
  {$asmmode intel}
  {$DEFINE XELSSL_X64}
{$ENDIF}

interface

uses
  SysUtils;

// Q = scalar * point (32 bytes each).
function X25519(const Scalar, Point: TBytes): TBytes;
// Public key = scalar * 9
function X25519Base(const Scalar: TBytes): TBytes;

var
  // x86-64 with BMI2 + ADX: the whole ladder in assembler (False: the Pascal ladder over
  // the same field kernels; tests compare both)
  X25519WholeLadder: Boolean = True;
  // X25519Base through the Edwards form with a precomputed table (False: the ladder)
  X25519FixedBase: Boolean = True;

implementation

uses XelSslFe25519, XelSslCpu;


{$IFDEF XELSSL_X64}
type
  TF4 = array[0..3] of UInt64;               // < 2^256, congruent mod 2^255 - 19

// kernels: arguments moved from the ABI registers to rax = R, rcx = A, rdx = B;
// R may be A or B
procedure XMulAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslX25519Mul.inc}
end;

procedure XSqrAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslX25519Sqr.inc}
end;

procedure XAddAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslX25519Add.inc}
end;

procedure XSubAsm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslX25519Sub.inc}
end;

procedure XMul121665Asm(R, A, B: Pointer); assembler; nostackframe;
asm
  {$IFDEF WIN64}
  mov rax, rcx
  mov rcx, rdx
  mov rdx, r8
  {$ELSE}
  mov rax, rdi
  mov rcx, rsi
  {$ENDIF}
  {$I XelSslX25519Mul121665.inc}
end;

procedure XSqrN(var A: TF4; N: Integer);
var i: Integer;
begin
  for i := 1 to N do XSqrAsm(@A, @A, nil);
end;

// z^(p-2) = z^(2^255 - 21): 254 squarings, 11 multiplications
procedure XInv(out R: TF4; const Z: TF4);
var z2, z9, z11, z2_5, z2_10, z2_20, z2_50, z2_100, t: TF4;
begin
  XSqrAsm(@z2, @Z, nil);                         // 2
  t := z2; XSqrN(t, 2);                          // 8
  XMulAsm(@z9, @t, @Z);                          // 9
  XMulAsm(@z11, @z9, @z2);                       // 11
  XSqrAsm(@t, @z11, nil);                        // 22
  XMulAsm(@z2_5, @t, @z9);                       // 2^5 - 1
  t := z2_5; XSqrN(t, 5); XMulAsm(@z2_10, @t, @z2_5);          // 2^10 - 1
  t := z2_10; XSqrN(t, 10); XMulAsm(@z2_20, @t, @z2_10);       // 2^20 - 1
  t := z2_20; XSqrN(t, 20); XMulAsm(@t, @t, @z2_20);           // 2^40 - 1
  XSqrN(t, 10); XMulAsm(@z2_50, @t, @z2_10);                   // 2^50 - 1
  t := z2_50; XSqrN(t, 50); XMulAsm(@z2_100, @t, @z2_50);      // 2^100 - 1
  t := z2_100; XSqrN(t, 100); XMulAsm(@t, @t, @z2_100);        // 2^200 - 1
  XSqrN(t, 50); XMulAsm(@t, @t, @z2_50);                       // 2^250 - 1
  XSqrN(t, 5); XMulAsm(@R, @t, @z11);                          // 2^255 - 21
end;

// constant-time swap when Bit = 1
procedure XCSwap(var A, B: TF4; Bit: UInt64);
var mask, t: UInt64; i: Integer;
begin
  mask := UInt64(0) - Bit;
  for i := 0 to 3 do
  begin
    t := mask and (A[i] xor B[i]);
    A[i] := A[i] xor t; B[i] := B[i] xor t;
  end;
end;

// the canonical value (< p) from a value below 2^256: subtract p twice under masks
procedure XFreeze(var A: TF4);
const P: TF4 = (UInt64($FFFFFFFFFFFFFFED), UInt64($FFFFFFFFFFFFFFFF), UInt64($FFFFFFFFFFFFFFFF),
  UInt64($7FFFFFFFFFFFFFFF));
var d: TF4; t, bw, b1, mask: UInt64; i, k: Integer;
begin
  for k := 1 to 2 do
  begin
    bw := 0;
    for i := 0 to 3 do
    begin
      t := A[i] - P[i]; b1 := Ord(A[i] < P[i]);
      d[i] := t - bw; bw := b1 + Ord(t < bw);
    end;
    mask := UInt64(0) - (bw xor 1);               // no borrow: A >= p, take A - p
    for i := 0 to 3 do A[i] := (d[i] and mask) or (A[i] and not mask);
  end;
end;

type
  // variables of the assembler ladder (offsets in test/gen_x25519_ladder.py)
  TX25519LadderCtx = record
    X1, X2, Z2, X3, Z3, A, AA, B, BB, E, C, D, DA, CB, T: TF4;
    K: array[0..31] of Byte;
    Swap, I: Int64;
    Dst: Pointer;
  end;

procedure HwX25519Ladder(Ctx: Pointer);
var p: Pointer;
begin
  p := Ctx;
  asm
    mov rax, p
    {$I XelSslX25519Ladder.inc}
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11'];
end;

function X25519Fast(const K: array of Byte; const Point: TBytes): TBytes;
var
  x1, x2, z2, x3, z3, a, aa, b, bb, e, c, d, da, cb, t: TF4;
  i, j: Integer; bit, swap: UInt64; lc: TX25519LadderCtx;
begin
  if X25519WholeLadder then
  begin
    // the whole ladder in one assembler block (XelSslX25519Ladder.inc)
    FillChar(lc, SizeOf(lc), 0);
    for i := 0 to 3 do
      for j := 7 downto 0 do lc.X1[i] := (lc.X1[i] shl 8) or Point[8 * i + j];
    lc.X1[3] := lc.X1[3] and UInt64($7FFFFFFFFFFFFFFF);
    lc.X2[0] := 1;
    lc.X3 := lc.X1;
    lc.Z3[0] := 1;
    Move(K[0], lc.K[0], 32);
    HwX25519Ladder(@lc);
    XInv(t, lc.Z2);
    XMulAsm(@x2, @lc.X2, @t);
    XFreeze(x2);
    SetLength(Result, 32);
    for i := 0 to 3 do
      for j := 0 to 7 do Result[8 * i + j] := Byte(x2[i] shr (8 * j));
    FillChar(lc, SizeOf(lc), 0); FillChar(x2, SizeOf(x2), 0); FillChar(t, SizeOf(t), 0);
    Exit;
  end;
  for i := 0 to 3 do
  begin
    x1[i] := 0;
    for j := 7 downto 0 do x1[i] := (x1[i] shl 8) or Point[8 * i + j];
  end;
  x1[3] := x1[3] and UInt64($7FFFFFFFFFFFFFFF);  // the top bit is ignored
  FillChar(x2, SizeOf(x2), 0); x2[0] := 1;
  FillChar(z2, SizeOf(z2), 0);
  x3 := x1;
  FillChar(z3, SizeOf(z3), 0); z3[0] := 1;
  swap := 0;
  for i := 254 downto 0 do
  begin
    bit := (K[i shr 3] shr (i and 7)) and 1;
    swap := swap xor bit;
    XCSwap(x2, x3, swap);
    XCSwap(z2, z3, swap);
    swap := bit;
    XAddAsm(@a, @x2, @z2);
    XSqrAsm(@aa, @a, nil);
    XSubAsm(@b, @x2, @z2);
    XSqrAsm(@bb, @b, nil);
    XSubAsm(@e, @aa, @bb);
    XAddAsm(@c, @x3, @z3);
    XSubAsm(@d, @x3, @z3);
    XMulAsm(@da, @d, @a);
    XMulAsm(@cb, @c, @b);
    XAddAsm(@t, @da, @cb);
    XSqrAsm(@x3, @t, nil);
    XSubAsm(@t, @da, @cb);
    XSqrAsm(@t, @t, nil);
    XMulAsm(@z3, @x1, @t);
    XMulAsm(@x2, @aa, @bb);
    XMul121665Asm(@t, @e, nil);
    XAddAsm(@t, @aa, @t);
    XMulAsm(@z2, @e, @t);
  end;
  XCSwap(x2, x3, swap);
  XCSwap(z2, z3, swap);
  XInv(t, z2);
  XMulAsm(@x2, @x2, @t);
  XFreeze(x2);
  SetLength(Result, 32);
  for i := 0 to 3 do
    for j := 0 to 7 do Result[8 * i + j] := Byte(x2[i] shr (8 * j));
  FillChar(x2, SizeOf(x2), 0); FillChar(z2, SizeOf(z2), 0); FillChar(x3, SizeOf(x3), 0);
  FillChar(z3, SizeOf(z3), 0); FillChar(aa, SizeOf(aa), 0); FillChar(bb, SizeOf(bb), 0);
  FillChar(e, SizeOf(e), 0); FillChar(t, SizeOf(t), 0);
end;
{$ENDIF}

// ---- fixed base: k * 9 through the Edwards form (ref10 / libsodium method) ----

const
  {$I XelSslX25519Base.inc}

type
  TNiels = record YpX, YmX, XY2d: TF4; end;       // y + x, y - x, 2dxy (affine)
  TEd = record X, Y, Z, T: TF4; end;              // extended coordinates, x = X/Z, y = Y/Z, T = XY/Z

// R := sign(B) * Base[I][|B| - 1] (identity for 0), constant time
procedure EdSelect(out R: TNiels; I, B: Integer);
var bneg, babs, m, j, k: UInt64; e: TNiels; neg: TF4; zero: TF4;
begin
  bneg := (UInt64(Int64(B)) shr 63) and 1;
  babs := UInt64(Int64(B) - ((-Int64(bneg)) and Int64(B)) * 2);
  FillChar(R, SizeOf(R), 0);
  R.YpX[0] := 1; R.YmX[0] := 1;
  for j := 1 to 8 do
  begin
    m := babs xor j;
    m := UInt64(0) - ((m - 1) shr 63);           // all ones when babs = j
    Move(X25519BaseTable[I, j - 1], e, SizeOf(e));
    for k := 0 to 3 do
    begin
      R.YpX[k] := R.YpX[k] xor (m and (R.YpX[k] xor e.YpX[k]));
      R.YmX[k] := R.YmX[k] xor (m and (R.YmX[k] xor e.YmX[k]));
      R.XY2d[k] := R.XY2d[k] xor (m and (R.XY2d[k] xor e.XY2d[k]));
    end;
  end;
  // negative digit: swap y + x and y - x, negate 2dxy
  FillChar(zero, SizeOf(zero), 0);
  XSubAsm(@neg, @zero, @R.XY2d);
  m := UInt64(0) - bneg;
  for k := 0 to 3 do
  begin
    j := m and (R.YpX[k] xor R.YmX[k]);
    R.YpX[k] := R.YpX[k] xor j; R.YmX[k] := R.YmX[k] xor j;
    R.XY2d[k] := R.XY2d[k] xor (m and (R.XY2d[k] xor neg[k]));
  end;
end;

// H := H + Q (Q affine, Niels form)
procedure EdMAdd(var H: TEd; const Q: TNiels);
var a, b, c, d, x1, y1, z1, t1: TF4;
begin
  XAddAsm(@a, @H.Y, @H.X);
  XSubAsm(@b, @H.Y, @H.X);
  XMulAsm(@a, @a, @Q.YpX);
  XMulAsm(@b, @b, @Q.YmX);
  XMulAsm(@c, @Q.XY2d, @H.T);
  XAddAsm(@d, @H.Z, @H.Z);
  XSubAsm(@x1, @a, @b);
  XAddAsm(@y1, @a, @b);
  XAddAsm(@z1, @d, @c);
  XSubAsm(@t1, @d, @c);
  XMulAsm(@H.X, @x1, @t1);
  XMulAsm(@H.Y, @y1, @z1);
  XMulAsm(@H.Z, @z1, @t1);
  XMulAsm(@H.T, @x1, @y1);
end;

// H := 2H (T of the input is not used)
procedure EdDouble(var H: TEd);
var xx, yy, b, a, x1, y1, z1, t1: TF4;
begin
  XSqrAsm(@xx, @H.X, nil);
  XSqrAsm(@yy, @H.Y, nil);
  XSqrAsm(@b, @H.Z, nil);
  XAddAsm(@b, @b, @b);
  XAddAsm(@a, @H.X, @H.Y);
  XSqrAsm(@a, @a, nil);
  XAddAsm(@y1, @yy, @xx);
  XSubAsm(@z1, @yy, @xx);
  XSubAsm(@x1, @a, @y1);
  XSubAsm(@t1, @b, @z1);
  XMulAsm(@H.X, @x1, @t1);
  XMulAsm(@H.Y, @y1, @z1);
  XMulAsm(@H.Z, @z1, @t1);
  XMulAsm(@H.T, @x1, @y1);
end;

// u(K * B) for the clamped scalar K: 64 additions of table points and 4 doublings
function X25519BaseFast(const K: array of Byte): TBytes;
var e: array[0..63] of Integer; i, carry, j: Integer; h: TEd; q: TNiels; num, den, t: TF4;
begin
  for i := 0 to 31 do
  begin
    e[2 * i] := K[i] and 15;
    e[2 * i + 1] := (K[i] shr 4) and 15;
  end;
  // signed digits -8..8
  carry := 0;
  for i := 0 to 62 do
  begin
    e[i] := e[i] + carry;
    carry := (e[i] + 8) shr 4;
    e[i] := e[i] - carry * 16;
  end;
  e[63] := e[63] + carry;
  FillChar(h, SizeOf(h), 0);
  h.Y[0] := 1; h.Z[0] := 1;                      // identity
  i := 1;
  while i < 64 do
  begin
    EdSelect(q, i div 2, e[i]);
    EdMAdd(h, q);
    Inc(i, 2);
  end;
  for j := 1 to 4 do EdDouble(h);
  i := 0;
  while i < 64 do
  begin
    EdSelect(q, i div 2, e[i]);
    EdMAdd(h, q);
    Inc(i, 2);
  end;
  // u = (1 + y) / (1 - y) = (Z + Y) / (Z - Y)
  XAddAsm(@num, @h.Z, @h.Y);
  XSubAsm(@den, @h.Z, @h.Y);
  XInv(t, den);
  XMulAsm(@num, @num, @t);
  XFreeze(num);
  SetLength(Result, 32);
  for i := 0 to 3 do
    for j := 0 to 7 do Result[8 * i + j] := Byte(num[i] shr (8 * j));
  FillChar(e, SizeOf(e), 0); FillChar(h, SizeOf(h), 0); FillChar(q, SizeOf(q), 0);
end;

function X25519(const Scalar, Point: TBytes): TBytes;
var
  k: array[0..31] of Byte; a24b: array[0..31] of Byte;
  x1, x2, z2, x3, z3, a, aa, b, bb, e, c, d, da, cb, a24, t: TFe;
  i, bit, swap: Integer;
begin
  if (Length(Scalar) <> 32) or (Length(Point) <> 32) then
    raise Exception.Create('XelSSL X25519: scalar and point must be 32 bytes');
  FeSelect;
  Move(Scalar[0], k[0], 32);
  k[0] := k[0] and 248;                       // clamping
  k[31] := (k[31] and 127) or 64;
  {$IFDEF XELSSL_X64}
  if AsmAvailable([cfBmi2, cfAdx]) then
  begin
    Result := X25519Fast(k, Point);
    FillChar(k, SizeOf(k), 0);
    Exit;
  end;
  {$ENDIF}
  FeFromBytes(x1, @Point[0]);                 // the top bit is ignored
  FillChar(a24b, 32, 0);
  a24b[0] := Byte(121665); a24b[1] := Byte(121665 shr 8); a24b[2] := Byte(121665 shr 16);
  FeFromBytes(a24, @a24b[0]);
  FeOne(x2); FeZero(z2);
  x3 := x1; FeOne(z3);
  swap := 0;
  for i := 254 downto 0 do
  begin
    bit := (k[i shr 3] shr (i and 7)) and 1;
    swap := swap xor bit;
    FeCSwap(x2, x3, swap);
    FeCSwap(z2, z3, swap);
    swap := bit;
    FeAdd(a, x2, z2);                         // A = x2 + z2
    FeSq(aa, a);                              // AA = A^2
    FeSub(b, x2, z2);                         // B = x2 - z2
    FeSq(bb, b);                              // BB = B^2
    FeSub(e, aa, bb);                         // E = AA - BB
    FeAdd(c, x3, z3);                         // C = x3 + z3
    FeSub(d, x3, z3);                         // D = x3 - z3
    FeMul(da, d, a);                          // DA = D * A
    FeMul(cb, c, b);                          // CB = C * B
    FeAdd(t, da, cb);
    FeSq(x3, t);                              // x3 = (DA + CB)^2
    FeSub(t, da, cb);
    FeSq(t, t);
    FeMul(z3, x1, t);                         // z3 = x1 * (DA - CB)^2
    FeMul(x2, aa, bb);                        // x2 = AA * BB
    FeMul(t, a24, e);
    FeAdd(t, aa, t);
    FeMul(z2, e, t);                          // z2 = E * (AA + a24 * E)
  end;
  FeCSwap(x2, x3, swap);
  FeCSwap(z2, z3, swap);
  FeInv(t, z2);
  FeMul(x2, x2, t);
  SetLength(Result, 32);
  FeToBytes(@Result[0], x2);
  FillChar(k, SizeOf(k), 0);
end;

function X25519Base(const Scalar: TBytes): TBytes;
var nine: TBytes; {$IFDEF XELSSL_X64}k: array[0..31] of Byte;{$ENDIF}
begin
  {$IFDEF XELSSL_X64}
  if X25519FixedBase and (Length(Scalar) = 32) and AsmAvailable([cfBmi2, cfAdx]) then
  begin
    Move(Scalar[0], k[0], 32);
    k[0] := k[0] and 248;
    k[31] := (k[31] and 127) or 64;
    Result := X25519BaseFast(k);
    FillChar(k, SizeOf(k), 0);
    Exit;
  end;
  {$ENDIF}
  SetLength(nine, 32);
  FillChar(nine[0], 32, 0);
  nine[0] := 9;
  Result := X25519(Scalar, nine);
end;

end.
