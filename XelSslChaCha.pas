// XelSSL - ChaCha20-Poly1305 AEAD (RFC 8439).
// Poly1305 in the 26-bit variant (poly1305-donna, A. Moon) - no data-dependent
// branches. ChaCha20: unrolled Pascal; on x86-64 with SSSE3 an assembler addition
// computes two blocks at a time (rows of the state in xmm registers); with AVX2 eight
// blocks at a time in column layout (register i = word i of 8 blocks, no shuffles in
// the rounds; XelSslChaChaAvx2.inc from test/gen_chacha_asm.py), the rest four blocks
// at a time (two blocks per ymm register). Poly1305 on x86-64: with AVX2 four blocks
// at a time in 64-bit lanes (26-bit limbs, VPMULUDQ, powers r^1..r^4;
// XelSslPolyAvx2.inc from test/gen_poly_asm.py), otherwise an assembler addition with
// 64-bit limbs (MUL 64 x 64 -> 128).
// License: MIT.
unit XelSslChaCha;

{$mode objfpc}{$H+}{$Q-}{$R-}
{$IFDEF CPUX86_64}
  {$asmmode intel}
  {$DEFINE XELSSL_X64}
{$ENDIF}{$Q-}{$R-}

interface

uses
  SysUtils;

// Returns ciphertext || tag (16 bytes). Key = 32 bytes, Nonce = 12 bytes.
function ChaChaPolySeal(const Key, Nonce, AAD, Plain: TBytes): TBytes;
function ChaChaPolyOpen(const Key, Nonce, AAD, Data: TBytes; out Plain: TBytes): Boolean;
// In-place variants for record layers: Data is encrypted / decrypted where it is,
// Tag = 16 bytes. ChaChaPolyOpenP checks the tag first (Data unchanged if it fails).
procedure ChaChaPolySealP(const Key, Nonce: TBytes; AAD: PByte; AadLen: Integer; Data: PByte; Len: Integer; Tag: PByte);
function ChaChaPolyOpenP(const Key, Nonce: TBytes; AAD: PByte; AadLen: Integer; Data: PByte; Len: Integer; Tag: PByte): Boolean;

var
  // use the assembler addition when the CPU allows it (tests switch it off)
  ChaChaUseAsm: Boolean = True;
  // the 8-block AVX2 kernel (False: 4-block steps; tests compare both)
  ChaChaWide: Boolean = True;
  // the 4-lane AVX2 Poly1305 (False: one block at a time; tests compare both)
  PolyWide: Boolean = True;

// Exported for tests
procedure ChaCha20Xor(const Key, Nonce: TBytes; Counter: UInt32; Src, Dst: PByte; Len: Integer);
function Poly1305Mac(const Key32: TBytes; const Msg: TBytes): TBytes;
// Poly1305 of Len bytes at Msg with a 32-byte key; 16-byte tag to Tag (no allocations
// of the message)
procedure Poly1305MacP(Key32, Msg: PByte; Len: Integer; Tag: PByte);

implementation

uses XelSslHash, XelSslCpu;

function Rol(X: UInt32; N: Integer): UInt32; inline;
begin Result := (X shl N) or (X shr (32 - N)); end;

function LE32(P: PByte): UInt32; inline;
begin Result := P[0] or (UInt32(P[1]) shl 8) or (UInt32(P[2]) shl 16) or (UInt32(P[3]) shl 24); end;

// 16 state words -> 64 bytes of key stream (unrolled, words kept in local variables)
procedure ChaChaBlock(const Inp: array of UInt32; out Outp: array of UInt32);
var
  x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15: UInt32; i: Integer;
begin
  x0 := Inp[0]; x1 := Inp[1]; x2 := Inp[2]; x3 := Inp[3];
  x4 := Inp[4]; x5 := Inp[5]; x6 := Inp[6]; x7 := Inp[7];
  x8 := Inp[8]; x9 := Inp[9]; x10 := Inp[10]; x11 := Inp[11];
  x12 := Inp[12]; x13 := Inp[13]; x14 := Inp[14]; x15 := Inp[15];
  for i := 1 to 10 do
  begin
    // columns
    x0 := x0 + x4; x12 := RolDWord(x12 xor x0, 16); x8 := x8 + x12; x4 := RolDWord(x4 xor x8, 12);
    x0 := x0 + x4; x12 := RolDWord(x12 xor x0, 8); x8 := x8 + x12; x4 := RolDWord(x4 xor x8, 7);
    x1 := x1 + x5; x13 := RolDWord(x13 xor x1, 16); x9 := x9 + x13; x5 := RolDWord(x5 xor x9, 12);
    x1 := x1 + x5; x13 := RolDWord(x13 xor x1, 8); x9 := x9 + x13; x5 := RolDWord(x5 xor x9, 7);
    x2 := x2 + x6; x14 := RolDWord(x14 xor x2, 16); x10 := x10 + x14; x6 := RolDWord(x6 xor x10, 12);
    x2 := x2 + x6; x14 := RolDWord(x14 xor x2, 8); x10 := x10 + x14; x6 := RolDWord(x6 xor x10, 7);
    x3 := x3 + x7; x15 := RolDWord(x15 xor x3, 16); x11 := x11 + x15; x7 := RolDWord(x7 xor x11, 12);
    x3 := x3 + x7; x15 := RolDWord(x15 xor x3, 8); x11 := x11 + x15; x7 := RolDWord(x7 xor x11, 7);
    // diagonals
    x0 := x0 + x5; x15 := RolDWord(x15 xor x0, 16); x10 := x10 + x15; x5 := RolDWord(x5 xor x10, 12);
    x0 := x0 + x5; x15 := RolDWord(x15 xor x0, 8); x10 := x10 + x15; x5 := RolDWord(x5 xor x10, 7);
    x1 := x1 + x6; x12 := RolDWord(x12 xor x1, 16); x11 := x11 + x12; x6 := RolDWord(x6 xor x11, 12);
    x1 := x1 + x6; x12 := RolDWord(x12 xor x1, 8); x11 := x11 + x12; x6 := RolDWord(x6 xor x11, 7);
    x2 := x2 + x7; x13 := RolDWord(x13 xor x2, 16); x8 := x8 + x13; x7 := RolDWord(x7 xor x8, 12);
    x2 := x2 + x7; x13 := RolDWord(x13 xor x2, 8); x8 := x8 + x13; x7 := RolDWord(x7 xor x8, 7);
    x3 := x3 + x4; x14 := RolDWord(x14 xor x3, 16); x9 := x9 + x14; x4 := RolDWord(x4 xor x9, 12);
    x3 := x3 + x4; x14 := RolDWord(x14 xor x3, 8); x9 := x9 + x14; x4 := RolDWord(x4 xor x9, 7);
  end;
  Outp[0] := x0 + Inp[0]; Outp[1] := x1 + Inp[1]; Outp[2] := x2 + Inp[2]; Outp[3] := x3 + Inp[3];
  Outp[4] := x4 + Inp[4]; Outp[5] := x5 + Inp[5]; Outp[6] := x6 + Inp[6]; Outp[7] := x7 + Inp[7];
  Outp[8] := x8 + Inp[8]; Outp[9] := x9 + Inp[9]; Outp[10] := x10 + Inp[10]; Outp[11] := x11 + Inp[11];
  Outp[12] := x12 + Inp[12]; Outp[13] := x13 + Inp[13]; Outp[14] := x14 + Inp[14]; Outp[15] := x15 + Inp[15];
end;

{$IFDEF XELSSL_X64}
const
  // pshufb masks: rotate every 32-bit lane left by 16 and by 8 bits; then the counter step
  ChaChaConst: array[0..47] of Byte = (
    2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13,
    3, 0, 1, 2, 7, 4, 5, 6, 11, 8, 9, 10, 15, 12, 13, 14,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

// Pairs x 128 bytes: Dst = Src xor key stream of two blocks at a time (state rows in
// xmm0..3 and xmm4..7, the second block with counter + 1). St[12] is advanced by 2
// per pair. xmm6..xmm11 are saved (callee-saved on Win64).
procedure HwChaCha2(St: PUInt32; Src, Dst: PByte; Pairs: Integer);
var pst, ps, pd, pm, psave: Pointer; cnt: PtrInt; save: array[0..95] of Byte;
begin
  pst := St; ps := Src; pd := Dst; cnt := Pairs; pm := @ChaChaConst; psave := @save[0];
  asm
    mov rax, psave
    movdqu [rax], xmm6
    movdqu [rax + 16], xmm7
    movdqu [rax + 32], xmm8
    movdqu [rax + 48], xmm9
    movdqu [rax + 64], xmm10
    movdqu [rax + 80], xmm11
    mov rcx, pst
    mov r8, ps
    mov r9, pd
    mov r10, cnt
    mov rdx, pm
    movdqu xmm10, [rdx]
    movdqu xmm11, [rdx + 16]
  @pair:
    test r10, r10
    jz @done
    movdqu xmm0, [rcx]
    movdqu xmm1, [rcx + 16]
    movdqu xmm2, [rcx + 32]
    movdqu xmm3, [rcx + 48]
    movdqa xmm4, xmm0
    movdqa xmm5, xmm1
    movdqa xmm6, xmm2
    movdqa xmm7, xmm3
    movdqu xmm8, [rdx + 32]
    paddd xmm7, xmm8
    mov r11, 10
  @dr:
    paddd xmm0, xmm1
    paddd xmm4, xmm5
    pxor xmm3, xmm0
    pxor xmm7, xmm4
    pshufb xmm3, xmm10
    pshufb xmm7, xmm10
    paddd xmm2, xmm3
    paddd xmm6, xmm7
    pxor xmm1, xmm2
    pxor xmm5, xmm6
    movdqa xmm8, xmm1
    pslld xmm1, 12
    psrld xmm8, 20
    por xmm1, xmm8
    movdqa xmm9, xmm5
    pslld xmm5, 12
    psrld xmm9, 20
    por xmm5, xmm9
    paddd xmm0, xmm1
    paddd xmm4, xmm5
    pxor xmm3, xmm0
    pxor xmm7, xmm4
    pshufb xmm3, xmm11
    pshufb xmm7, xmm11
    paddd xmm2, xmm3
    paddd xmm6, xmm7
    pxor xmm1, xmm2
    pxor xmm5, xmm6
    movdqa xmm8, xmm1
    pslld xmm1, 7
    psrld xmm8, 25
    por xmm1, xmm8
    movdqa xmm9, xmm5
    pslld xmm5, 7
    psrld xmm9, 25
    por xmm5, xmm9
    pshufd xmm1, xmm1, $39
    pshufd xmm2, xmm2, $4E
    pshufd xmm3, xmm3, $93
    pshufd xmm5, xmm5, $39
    pshufd xmm6, xmm6, $4E
    pshufd xmm7, xmm7, $93
    paddd xmm0, xmm1
    paddd xmm4, xmm5
    pxor xmm3, xmm0
    pxor xmm7, xmm4
    pshufb xmm3, xmm10
    pshufb xmm7, xmm10
    paddd xmm2, xmm3
    paddd xmm6, xmm7
    pxor xmm1, xmm2
    pxor xmm5, xmm6
    movdqa xmm8, xmm1
    pslld xmm1, 12
    psrld xmm8, 20
    por xmm1, xmm8
    movdqa xmm9, xmm5
    pslld xmm5, 12
    psrld xmm9, 20
    por xmm5, xmm9
    paddd xmm0, xmm1
    paddd xmm4, xmm5
    pxor xmm3, xmm0
    pxor xmm7, xmm4
    pshufb xmm3, xmm11
    pshufb xmm7, xmm11
    paddd xmm2, xmm3
    paddd xmm6, xmm7
    pxor xmm1, xmm2
    pxor xmm5, xmm6
    movdqa xmm8, xmm1
    pslld xmm1, 7
    psrld xmm8, 25
    por xmm1, xmm8
    movdqa xmm9, xmm5
    pslld xmm5, 7
    psrld xmm9, 25
    por xmm5, xmm9
    pshufd xmm1, xmm1, $93
    pshufd xmm2, xmm2, $4E
    pshufd xmm3, xmm3, $39
    pshufd xmm5, xmm5, $93
    pshufd xmm6, xmm6, $4E
    pshufd xmm7, xmm7, $39
    dec r11
    jnz @dr
    movdqu xmm8, [rcx]
    paddd xmm0, xmm8
    paddd xmm4, xmm8
    movdqu xmm8, [rcx + 16]
    paddd xmm1, xmm8
    paddd xmm5, xmm8
    movdqu xmm8, [rcx + 32]
    paddd xmm2, xmm8
    paddd xmm6, xmm8
    movdqu xmm8, [rcx + 48]
    paddd xmm3, xmm8
    movdqu xmm9, [rdx + 32]
    paddd xmm8, xmm9
    paddd xmm7, xmm8
    movdqu xmm8, [r8 + 0]
    pxor xmm0, xmm8
    movdqu [r9 + 0], xmm0
    movdqu xmm8, [r8 + 16]
    pxor xmm1, xmm8
    movdqu [r9 + 16], xmm1
    movdqu xmm8, [r8 + 32]
    pxor xmm2, xmm8
    movdqu [r9 + 32], xmm2
    movdqu xmm8, [r8 + 48]
    pxor xmm3, xmm8
    movdqu [r9 + 48], xmm3
    movdqu xmm8, [r8 + 64]
    pxor xmm4, xmm8
    movdqu [r9 + 64], xmm4
    movdqu xmm8, [r8 + 80]
    pxor xmm5, xmm8
    movdqu [r9 + 80], xmm5
    movdqu xmm8, [r8 + 96]
    pxor xmm6, xmm8
    movdqu [r9 + 96], xmm6
    movdqu xmm8, [r8 + 112]
    pxor xmm7, xmm8
    movdqu [r9 + 112], xmm7
    add dword ptr [rcx + 48], 2
    add r8, 128
    add r9, 128
    dec r10
    jmp @pair
  @done:
    mov rax, psave
    movdqu xmm6, [rax]
    movdqu xmm7, [rax + 16]
    movdqu xmm8, [rax + 32]
    movdqu xmm9, [rax + 48]
    movdqu xmm10, [rax + 64]
    movdqu xmm11, [rax + 80]
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11', 'xmm0', 'xmm1', 'xmm2', 'xmm3', 'xmm4', 'xmm5',
    'xmm6', 'xmm7', 'xmm8', 'xmm9', 'xmm10', 'xmm11'];
  FillChar(save, SizeOf(save), 0);
end;

const
  // counter steps for the two lanes of the AVX2 rows: (0, 1) and (2, 3)
  ChaChaInc: array[0..63] of Byte = (
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);

// Quads x 256 bytes with AVX2: each ymm register holds one row of two blocks (one per
// 128-bit lane), two such groups give 4 blocks per step. St[12] is advanced by 4 per step.
// The low halves of xmm6..xmm11 are saved (callee-saved on Win64); VZEROUPPER at the end.
procedure HwChaCha4Avx2(St: PUInt32; Src, Dst: PByte; Quads: Integer);
var pst, ps, pd, pm, pi, psave: Pointer; cnt: PtrInt; save: array[0..95] of Byte;
begin
  pst := St; ps := Src; pd := Dst; cnt := Quads; pm := @ChaChaConst; pi := @ChaChaInc; psave := @save[0];
  asm
    mov rax, psave
    movdqu [rax], xmm6
    movdqu [rax + 16], xmm7
    movdqu [rax + 32], xmm8
    movdqu [rax + 48], xmm9
    movdqu [rax + 64], xmm10
    movdqu [rax + 80], xmm11
    mov rcx, pst
    mov r8, ps
    mov r9, pd
    mov r10, cnt
    mov rdx, pm
    mov rax, pi
    vbroadcasti128 ymm10, [rdx]
    vbroadcasti128 ymm11, [rdx + 16]
  @quad:
    test r10, r10
    jz @done
    vbroadcasti128 ymm0, [rcx]
    vbroadcasti128 ymm1, [rcx + 16]
    vbroadcasti128 ymm2, [rcx + 32]
    vbroadcasti128 ymm3, [rcx + 48]
    vmovdqa ymm4, ymm0
    vmovdqa ymm5, ymm1
    vmovdqa ymm6, ymm2
    vpaddd ymm7, ymm3, [rax + 32]
    vpaddd ymm3, ymm3, [rax]
    mov r11, 10
  @dr:
    vpaddd ymm0, ymm0, ymm1
    vpaddd ymm4, ymm4, ymm5
    vpxor ymm3, ymm3, ymm0
    vpxor ymm7, ymm7, ymm4
    vpshufb ymm3, ymm3, ymm10
    vpshufb ymm7, ymm7, ymm10
    vpaddd ymm2, ymm2, ymm3
    vpaddd ymm6, ymm6, ymm7
    vpxor ymm1, ymm1, ymm2
    vpxor ymm5, ymm5, ymm6
    vpslld ymm8, ymm1, 12
    vpsrld ymm1, ymm1, 20
    vpor ymm1, ymm1, ymm8
    vpslld ymm9, ymm5, 12
    vpsrld ymm5, ymm5, 20
    vpor ymm5, ymm5, ymm9
    vpaddd ymm0, ymm0, ymm1
    vpaddd ymm4, ymm4, ymm5
    vpxor ymm3, ymm3, ymm0
    vpxor ymm7, ymm7, ymm4
    vpshufb ymm3, ymm3, ymm11
    vpshufb ymm7, ymm7, ymm11
    vpaddd ymm2, ymm2, ymm3
    vpaddd ymm6, ymm6, ymm7
    vpxor ymm1, ymm1, ymm2
    vpxor ymm5, ymm5, ymm6
    vpslld ymm8, ymm1, 7
    vpsrld ymm1, ymm1, 25
    vpor ymm1, ymm1, ymm8
    vpslld ymm9, ymm5, 7
    vpsrld ymm5, ymm5, 25
    vpor ymm5, ymm5, ymm9
    vpshufd ymm1, ymm1, $39
    vpshufd ymm2, ymm2, $4E
    vpshufd ymm3, ymm3, $93
    vpshufd ymm5, ymm5, $39
    vpshufd ymm6, ymm6, $4E
    vpshufd ymm7, ymm7, $93
    vpaddd ymm0, ymm0, ymm1
    vpaddd ymm4, ymm4, ymm5
    vpxor ymm3, ymm3, ymm0
    vpxor ymm7, ymm7, ymm4
    vpshufb ymm3, ymm3, ymm10
    vpshufb ymm7, ymm7, ymm10
    vpaddd ymm2, ymm2, ymm3
    vpaddd ymm6, ymm6, ymm7
    vpxor ymm1, ymm1, ymm2
    vpxor ymm5, ymm5, ymm6
    vpslld ymm8, ymm1, 12
    vpsrld ymm1, ymm1, 20
    vpor ymm1, ymm1, ymm8
    vpslld ymm9, ymm5, 12
    vpsrld ymm5, ymm5, 20
    vpor ymm5, ymm5, ymm9
    vpaddd ymm0, ymm0, ymm1
    vpaddd ymm4, ymm4, ymm5
    vpxor ymm3, ymm3, ymm0
    vpxor ymm7, ymm7, ymm4
    vpshufb ymm3, ymm3, ymm11
    vpshufb ymm7, ymm7, ymm11
    vpaddd ymm2, ymm2, ymm3
    vpaddd ymm6, ymm6, ymm7
    vpxor ymm1, ymm1, ymm2
    vpxor ymm5, ymm5, ymm6
    vpslld ymm8, ymm1, 7
    vpsrld ymm1, ymm1, 25
    vpor ymm1, ymm1, ymm8
    vpslld ymm9, ymm5, 7
    vpsrld ymm5, ymm5, 25
    vpor ymm5, ymm5, ymm9
    vpshufd ymm1, ymm1, $93
    vpshufd ymm2, ymm2, $4E
    vpshufd ymm3, ymm3, $39
    vpshufd ymm5, ymm5, $93
    vpshufd ymm6, ymm6, $4E
    vpshufd ymm7, ymm7, $39
    dec r11
    jnz @dr
    vbroadcasti128 ymm8, [rcx]
    vpaddd ymm0, ymm0, ymm8
    vpaddd ymm4, ymm4, ymm8
    vbroadcasti128 ymm8, [rcx + 16]
    vpaddd ymm1, ymm1, ymm8
    vpaddd ymm5, ymm5, ymm8
    vbroadcasti128 ymm8, [rcx + 32]
    vpaddd ymm2, ymm2, ymm8
    vpaddd ymm6, ymm6, ymm8
    vbroadcasti128 ymm8, [rcx + 48]
    vpaddd ymm9, ymm8, [rax]
    vpaddd ymm3, ymm3, ymm9
    vpaddd ymm9, ymm8, [rax + 32]
    vpaddd ymm7, ymm7, ymm9
    vperm2i128 ymm8, ymm0, ymm1, $20
    vpxor ymm8, ymm8, [r8 + 0]
    vmovdqu [r9 + 0], ymm8
    vperm2i128 ymm9, ymm2, ymm3, $20
    vpxor ymm9, ymm9, [r8 + 32]
    vmovdqu [r9 + 32], ymm9
    vperm2i128 ymm8, ymm0, ymm1, $31
    vpxor ymm8, ymm8, [r8 + 64]
    vmovdqu [r9 + 64], ymm8
    vperm2i128 ymm9, ymm2, ymm3, $31
    vpxor ymm9, ymm9, [r8 + 96]
    vmovdqu [r9 + 96], ymm9
    vperm2i128 ymm8, ymm4, ymm5, $20
    vpxor ymm8, ymm8, [r8 + 128]
    vmovdqu [r9 + 128], ymm8
    vperm2i128 ymm9, ymm6, ymm7, $20
    vpxor ymm9, ymm9, [r8 + 160]
    vmovdqu [r9 + 160], ymm9
    vperm2i128 ymm8, ymm4, ymm5, $31
    vpxor ymm8, ymm8, [r8 + 192]
    vmovdqu [r9 + 192], ymm8
    vperm2i128 ymm9, ymm6, ymm7, $31
    vpxor ymm9, ymm9, [r8 + 224]
    vmovdqu [r9 + 224], ymm9
    add dword ptr [rcx + 48], 4
    add r8, 256
    add r9, 256
    dec r10
    jmp @quad
  @done:
    vzeroupper
    mov rax, psave
    movdqu xmm6, [rax]
    movdqu xmm7, [rax + 16]
    movdqu xmm8, [rax + 32]
    movdqu xmm9, [rax + 48]
    movdqu xmm10, [rax + 64]
    movdqu xmm11, [rax + 80]
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11', 'xmm0', 'xmm1', 'xmm2', 'xmm3', 'xmm4', 'xmm5',
    'xmm6', 'xmm7', 'xmm8', 'xmm9', 'xmm10', 'xmm11'];
  FillChar(save, SizeOf(save), 0);
end;
{$ENDIF}

{$IFDEF XELSSL_X64}
type
  // parameters and work area of the generated kernel (offsets in test/gen_chacha_asm.py)
  TChaChaAsmCtx = record
    St: Pointer;                    // 0: 16 state words (the counter is not advanced)
    Src, Dst: Pointer;              // 8, 16
    Steps: Int64;                   // 24: steps of 8 blocks (512 bytes)
    Consts: Pointer;                // 32: ChaChaAsmConsts
    Save: array[0..159] of Byte;    // 40: xmm6..xmm15 of the caller
    Work: array[0..831] of Byte;    // 200: input state, spilled words, scratch (wiped)
  end;

var
  // rotate-left-16 and rotate-left-8 byte masks, lane offsets 0..7, 8 in every lane
  ChaChaAsmConsts: array[0..127] of Byte;

procedure InitChaChaAsmConsts;
var i: Integer;
begin
  for i := 0 to 7 do
  begin
    ChaChaAsmConsts[4 * i] := (4 * i + 2) and 15; ChaChaAsmConsts[4 * i + 1] := (4 * i + 3) and 15;
    ChaChaAsmConsts[4 * i + 2] := (4 * i) and 15; ChaChaAsmConsts[4 * i + 3] := (4 * i + 1) and 15;
    ChaChaAsmConsts[32 + 4 * i] := (4 * i + 3) and 15; ChaChaAsmConsts[32 + 4 * i + 1] := (4 * i) and 15;
    ChaChaAsmConsts[32 + 4 * i + 2] := (4 * i + 1) and 15; ChaChaAsmConsts[32 + 4 * i + 3] := (4 * i + 2) and 15;
    PUInt32(@ChaChaAsmConsts[64 + 4 * i])^ := i;
    PUInt32(@ChaChaAsmConsts[96 + 4 * i])^ := 8;
  end;
end;

procedure HwChaCha8(Ctx: Pointer);
var p: Pointer;
begin
  p := Ctx;
  asm
    mov rax, p
    {$I XelSslChaChaAvx2.inc}
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11', 'xmm0', 'xmm1', 'xmm2', 'xmm3', 'xmm4', 'xmm5'];
end;
{$ENDIF}

procedure ChaCha20Xor(const Key, Nonce: TBytes; Counter: UInt32; Src, Dst: PByte; Len: Integer);
var st, ks: array[0..15] of UInt32; i, n: Integer; kb: PByte; {$IFDEF XELSSL_X64}ctx: TChaChaAsmCtx;{$ENDIF}
begin
  st[0] := $61707865; st[1] := $3320646E; st[2] := $79622D32; st[3] := $6B206574;
  for i := 0 to 7 do st[4 + i] := LE32(@Key[i * 4]);
  st[12] := Counter;
  for i := 0 to 2 do st[13 + i] := LE32(@Nonce[i * 4]);
  {$IFDEF XELSSL_X64}
  if ChaChaUseAsm and ChaChaWide and AsmAvailable([cfAvx2]) and (Len >= 512) then
  begin
    n := Len div 512;
    ctx.St := @st[0]; ctx.Src := Src; ctx.Dst := Dst; ctx.Steps := n;
    ctx.Consts := @ChaChaAsmConsts[0];
    HwChaCha8(@ctx);
    st[12] := st[12] + UInt32(8 * n);
    Inc(Src, 512 * n); Inc(Dst, 512 * n); Dec(Len, 512 * n);
    FillChar(ctx.Save, SizeOf(ctx.Save), 0);
  end;
  if ChaChaUseAsm and AsmAvailable([cfAvx2]) and (Len >= 256) then
  begin
    n := Len div 256;
    HwChaCha4Avx2(@st[0], Src, Dst, n);         // advances st[12] by 4 per step
    Inc(Src, 256 * n); Inc(Dst, 256 * n); Dec(Len, 256 * n);
  end;
  if ChaChaUseAsm and AsmAvailable([cfSsse3]) and (Len >= 128) then
  begin
    n := Len div 128;
    HwChaCha2(@st[0], Src, Dst, n);             // advances st[12] by 2 per pair
    Inc(Src, 128 * n); Inc(Dst, 128 * n); Dec(Len, 128 * n);
  end;
  {$ENDIF}
  kb := @ks[0];
  while Len > 0 do
  begin
    ChaChaBlock(st, ks);
    {$IFDEF ENDIAN_BIG}
    for i := 0 to 15 do ks[i] := NtoLE(ks[i]);
    {$ENDIF}
    if Len >= 64 then
    begin
      for i := 0 to 15 do PUInt32(Dst)[i] := PUInt32(Src)[i] xor ks[i];
      n := 64;
    end
    else
    begin
      n := Len;
      for i := 0 to n - 1 do Dst[i] := Src[i] xor kb[i];
    end;
    Inc(Src, n); Inc(Dst, n); Dec(Len, n);
    st[12] := st[12] + 1;
  end;
  FillChar(ks, SizeOf(ks), 0); FillChar(st, SizeOf(st), 0);
end;

// ---- Poly1305 (26-bit limbs) ----

type
  TPoly = record
    r, h, pad: array[0..4] of UInt32;
    s: array[0..3] of UInt32;
  end;

procedure PolyInit(out P: TPoly; const Key: TBytes);
begin
  FillChar(P, SizeOf(P), 0);
  // r &= 0ffffffc0ffffffc0ffffffc0fffffff
  P.r[0] := (LE32(@Key[0])) and $3FFFFFF;
  P.r[1] := (LE32(@Key[3]) shr 2) and $3FFFF03;
  P.r[2] := (LE32(@Key[6]) shr 4) and $3FFC0FF;
  P.r[3] := (LE32(@Key[9]) shr 6) and $3F03FFF;
  P.r[4] := (LE32(@Key[12]) shr 8) and $00FFFFF;
  P.s[0] := LE32(@Key[16]); P.s[1] := LE32(@Key[20]);
  P.s[2] := LE32(@Key[24]); P.s[3] := LE32(@Key[28]);
end;

// one 16-byte block; HiBit = 1 shl 24 for full blocks (bit 2^128), 0 for the padded last one
procedure PolyBlock(var P: TPoly; M: PByte; HiBit: UInt32);
var r0, r1, r2, r3, r4, s1, s2, s3, s4, h0, h1, h2, h3, h4, c: UInt32;
    d0, d1, d2, d3, d4: UInt64;
begin
  r0 := P.r[0]; r1 := P.r[1]; r2 := P.r[2]; r3 := P.r[3]; r4 := P.r[4];
  s1 := r1 * 5; s2 := r2 * 5; s3 := r3 * 5; s4 := r4 * 5;
  h0 := P.h[0]; h1 := P.h[1]; h2 := P.h[2]; h3 := P.h[3]; h4 := P.h[4];
  h0 := h0 + (LE32(M) and $3FFFFFF);
  h1 := h1 + ((LE32(M + 3) shr 2) and $3FFFFFF);
  h2 := h2 + ((LE32(M + 6) shr 4) and $3FFFFFF);
  h3 := h3 + ((LE32(M + 9) shr 6) and $3FFFFFF);
  h4 := h4 + ((LE32(M + 12) shr 8) or HiBit);
  d0 := UInt64(h0) * r0 + UInt64(h1) * s4 + UInt64(h2) * s3 + UInt64(h3) * s2 + UInt64(h4) * s1;
  d1 := UInt64(h0) * r1 + UInt64(h1) * r0 + UInt64(h2) * s4 + UInt64(h3) * s3 + UInt64(h4) * s2;
  d2 := UInt64(h0) * r2 + UInt64(h1) * r1 + UInt64(h2) * r0 + UInt64(h3) * s4 + UInt64(h4) * s3;
  d3 := UInt64(h0) * r3 + UInt64(h1) * r2 + UInt64(h2) * r1 + UInt64(h3) * r0 + UInt64(h4) * s4;
  d4 := UInt64(h0) * r4 + UInt64(h1) * r3 + UInt64(h2) * r2 + UInt64(h3) * r1 + UInt64(h4) * r0;
  c := UInt32(d0 shr 26); h0 := UInt32(d0) and $3FFFFFF;
  d1 := d1 + c; c := UInt32(d1 shr 26); h1 := UInt32(d1) and $3FFFFFF;
  d2 := d2 + c; c := UInt32(d2 shr 26); h2 := UInt32(d2) and $3FFFFFF;
  d3 := d3 + c; c := UInt32(d3 shr 26); h3 := UInt32(d3) and $3FFFFFF;
  d4 := d4 + c; c := UInt32(d4 shr 26); h4 := UInt32(d4) and $3FFFFFF;
  h0 := h0 + c * 5; c := h0 shr 26; h0 := h0 and $3FFFFFF;
  h1 := h1 + c;
  P.h[0] := h0; P.h[1] := h1; P.h[2] := h2; P.h[3] := h3; P.h[4] := h4;
end;

{$IFDEF XELSSL_X64}
// N full 16-byte blocks (each + 2^128). St = h0, h1, h2, r0, r1: h = h0 + h1*2^64 + h2*2^128,
// r = r0 + r1*2^64. Since the clamped r1 is a multiple of 4, h1*r1*2^128 = h1*(r1/4)*2^130
// = 5*h1*(r1/4) = h1*s1 (mod 2^130 - 5) with s1 = r1 + r1/4; the same for h2*r1*2^192.
procedure HwPolyBlocks(St: PUInt64; M: PByte; N: Integer);
var pst, pm: Pointer; cnt: PtrInt;
begin
  pst := St; pm := M; cnt := N;
  asm
    mov rax, pst
    mov rcx, pm
    mov rdx, cnt
    push rbx
    push rsi
    push rdi
    push r12
    push r13
    push r14
    push r15
    push rax
    mov rsi, rcx
    mov rdi, rdx
    mov r8, [rax]                            // h0
    mov r9, [rax + 8]                        // h1
    mov r10, [rax + 16]                      // h2
    mov r12, [rax + 24]                      // r0
    mov r13, [rax + 32]                      // r1
    mov r14, r13
    shr r14, 2
    add r14, r13                             // s1 = r1 + r1/4
  @blk:
    test rdi, rdi
    jz @done
    add r8, [rsi]
    adc r9, [rsi + 8]
    adc r10, 1                               // + 2^128
    mov rax, r8
    mul r12
    mov rbx, rax
    mov rcx, rdx                             // d0 = h0*r0
    mov rax, r9
    mul r14
    add rbx, rax
    adc rcx, rdx                             //    + h1*s1
    mov rax, r8
    mul r13
    mov r11, rax
    mov r15, rdx                             // d1 = h0*r1
    mov rax, r9
    mul r12
    add r11, rax
    adc r15, rdx                             //    + h1*r0
    mov rax, r10
    imul rax, r14
    add r11, rax
    adc r15, 0                               //    + h2*s1
    add r11, rcx
    adc r15, 0                               //    + high part of d0
    imul r10, r12
    add r10, r15                             // d2 = h2*r0 + high part of d1
    mov r8, rbx
    mov r9, r11
    mov rax, r10                             // partial reduction: bits >= 130 times 5
    shr rax, 2
    and r10, 3
    lea rax, [rax + rax * 4]
    add r8, rax
    adc r9, 0
    adc r10, 0
    add rsi, 16
    dec rdi
    jmp @blk
  @done:
    pop rax
    mov [rax], r8
    mov [rax + 8], r9
    mov [rax + 16], r10
    pop r15
    pop r14
    pop r13
    pop r12
    pop rdi
    pop rsi
    pop rbx
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11'];
end;

// full carry of the 26-bit limbs (value below 2^130 afterwards, limbs exactly 26 bits)
procedure PolyNormalize(var P: TPoly);
var c: UInt32;
begin
  c := P.h[0] shr 26; P.h[0] := P.h[0] and $3FFFFFF;
  P.h[1] := P.h[1] + c; c := P.h[1] shr 26; P.h[1] := P.h[1] and $3FFFFFF;
  P.h[2] := P.h[2] + c; c := P.h[2] shr 26; P.h[2] := P.h[2] and $3FFFFFF;
  P.h[3] := P.h[3] + c; c := P.h[3] shr 26; P.h[3] := P.h[3] and $3FFFFFF;
  P.h[4] := P.h[4] + c; c := P.h[4] shr 26; P.h[4] := P.h[4] and $3FFFFFF;
  P.h[0] := P.h[0] + c * 5; c := P.h[0] shr 26; P.h[0] := P.h[0] and $3FFFFFF;
  P.h[1] := P.h[1] + c;
end;

// N blocks with the assembler: 26-bit limbs -> 64-bit limbs -> back
procedure PolyBlocksAsm(var P: TPoly; M: PByte; N: Integer);
var st: array[0..4] of UInt64;
  function Pack(const L: array of UInt32; out Hi: UInt64; out Top: UInt64): UInt64;
  begin
    Result := UInt64(L[0]) or (UInt64(L[1]) shl 26) or (UInt64(L[2]) shl 52);
    Hi := (UInt64(L[2]) shr 12) or (UInt64(L[3]) shl 14) or (UInt64(L[4]) shl 40);
    Top := UInt64(L[4]) shr 24;
  end;
var top: UInt64;
begin
  PolyNormalize(P);
  st[0] := Pack(P.h, st[1], st[2]);
  st[3] := Pack(P.r, st[4], top);
  HwPolyBlocks(@st[0], M, N);
  P.h[0] := UInt32(st[0]) and $3FFFFFF;
  P.h[1] := UInt32(st[0] shr 26) and $3FFFFFF;
  P.h[2] := UInt32((st[0] shr 52) or (st[1] shl 12)) and $3FFFFFF;
  P.h[3] := UInt32(st[1] shr 14) and $3FFFFFF;
  P.h[4] := UInt32((st[1] shr 40) or (st[2] shl 24));
  FillChar(st, SizeOf(st), 0);
end;
{$ENDIF}

{$IFDEF XELSSL_X64}
type
  // parameters and tables of the generated kernel (offsets in test/gen_poly_asm.py)
  TPolyAsmCtx = record
    Msg: Pointer;                       // 0
    Groups: Int64;                      // 8: groups of 4 blocks (64 bytes)
    Consts: Pointer;                    // 16: PolyAsmConsts
    Pad: array[0..1] of UInt64;         // 24
    Save: array[0..159] of Byte;        // 40: xmm6..xmm15 of the caller
    Tab: array[0..17, 0..3] of UInt64;  // 200: r^4, 5r^4, last-step powers, 5 * them
    Acc: array[0..4, 0..3] of UInt64;   // 776: A (lane 0 = h); on return Acc[0, limb] = lane sums
  end;

const
  // 26-bit mask and 2^24 (the 2^128 bit in limb 4), in 4 lanes each
  PolyAsmConsts: array[0..7] of UInt64 = ($3FFFFFF, $3FFFFFF, $3FFFFFF, $3FFFFFF,
    1 shl 24, 1 shl 24, 1 shl 24, 1 shl 24);

procedure HwPoly4(Ctx: Pointer);
var p: Pointer;
begin
  p := Ctx;
  asm
    mov rax, p
    {$I XelSslPolyAvx2.inc}
  end ['rax', 'rcx', 'rdx', 'r8', 'r9', 'r10', 'r11', 'xmm0', 'xmm1', 'xmm2', 'xmm3', 'xmm4', 'xmm5'];
end;

// C := A * B mod 2^130 - 5 in 26-bit limbs (limbs carried to at most 26 bits + a little)
procedure PolyMulLimbs(const A, B: array of UInt32; out C: array of UInt32);
var s1, s2, s3, s4: UInt64; d0, d1, d2, d3, d4: UInt64; c_: UInt64;
begin
  s1 := UInt64(B[1]) * 5; s2 := UInt64(B[2]) * 5; s3 := UInt64(B[3]) * 5; s4 := UInt64(B[4]) * 5;
  d0 := UInt64(A[0]) * B[0] + A[1] * s4 + A[2] * s3 + A[3] * s2 + A[4] * s1;
  d1 := UInt64(A[0]) * B[1] + UInt64(A[1]) * B[0] + A[2] * s4 + A[3] * s3 + A[4] * s2;
  d2 := UInt64(A[0]) * B[2] + UInt64(A[1]) * B[1] + UInt64(A[2]) * B[0] + A[3] * s4 + A[4] * s3;
  d3 := UInt64(A[0]) * B[3] + UInt64(A[1]) * B[2] + UInt64(A[2]) * B[1] + UInt64(A[3]) * B[0] + A[4] * s4;
  d4 := UInt64(A[0]) * B[4] + UInt64(A[1]) * B[3] + UInt64(A[2]) * B[2] + UInt64(A[3]) * B[1] + UInt64(A[4]) * B[0];
  c_ := d0 shr 26; C[0] := UInt32(d0) and $3FFFFFF;
  d1 := d1 + c_; c_ := d1 shr 26; C[1] := UInt32(d1) and $3FFFFFF;
  d2 := d2 + c_; c_ := d2 shr 26; C[2] := UInt32(d2) and $3FFFFFF;
  d3 := d3 + c_; c_ := d3 shr 26; C[3] := UInt32(d3) and $3FFFFFF;
  d4 := d4 + c_; c_ := d4 shr 26; C[4] := UInt32(d4) and $3FFFFFF;
  d0 := C[0] + c_ * 5; C[0] := UInt32(d0) and $3FFFFFF;
  C[1] := C[1] + UInt32(d0 shr 26);
end;

// Groups x 4 full blocks with the AVX2 kernel
procedure PolyBlocksAvx2(var P: TPoly; M: PByte; Groups: Integer);
var ctx: TPolyAsmCtx; r2, r3, r4: array[0..4] of UInt32; i, k: Integer; v: UInt32;
  d: array[0..4] of UInt64; c_: UInt64;
begin
  PolyNormalize(P);
  PolyMulLimbs(P.r, P.r, r2);
  PolyMulLimbs(r2, P.r, r3);
  PolyMulLimbs(r3, P.r, r4);
  FillChar(ctx, SizeOf(ctx), 0);
  ctx.Msg := M; ctx.Groups := Groups; ctx.Consts := @PolyAsmConsts[0];
  for i := 0 to 4 do
    for k := 0 to 3 do
    begin
      ctx.Tab[i, k] := r4[i];
      // last step: lanes hold the blocks 0, 2, 1, 3 of the group
      case k of
        0: v := r4[i];
        1: v := r2[i];
        2: v := r3[i];
      else v := P.r[i];
      end;
      ctx.Tab[9 + i, k] := v;
      if i > 0 then
      begin
        ctx.Tab[4 + i, k] := r4[i] * 5;
        ctx.Tab[13 + i, k] := v * 5;
      end;
    end;
  for i := 0 to 4 do ctx.Acc[i, 0] := P.h[i];
  HwPoly4(@ctx);
  for i := 0 to 4 do d[i] := ctx.Acc[0, i];                // the kernel stores the sums here
  c_ := d[0] shr 26; P.h[0] := UInt32(d[0]) and $3FFFFFF;
  d[1] := d[1] + c_; c_ := d[1] shr 26; P.h[1] := UInt32(d[1]) and $3FFFFFF;
  d[2] := d[2] + c_; c_ := d[2] shr 26; P.h[2] := UInt32(d[2]) and $3FFFFFF;
  d[3] := d[3] + c_; c_ := d[3] shr 26; P.h[3] := UInt32(d[3]) and $3FFFFFF;
  d[4] := d[4] + c_; c_ := d[4] shr 26; P.h[4] := UInt32(d[4]) and $3FFFFFF;
  d[0] := P.h[0] + c_ * 5; P.h[0] := UInt32(d[0]) and $3FFFFFF;
  P.h[1] := P.h[1] + UInt32(d[0] shr 26);
  FillChar(ctx, SizeOf(ctx), 0);
  FillChar(r2, SizeOf(r2), 0); FillChar(r3, SizeOf(r3), 0); FillChar(r4, SizeOf(r4), 0);
end;
{$ENDIF}

procedure PolyUpdateP(var P: TPoly; Data: PByte; Len: Integer; PadTo16: Boolean);
var i, n, r, g: Integer; blk: array[0..15] of Byte;
begin
  n := Len div 16;
  {$IFDEF XELSSL_X64}
  if (n >= 8) and ChaChaUseAsm and PolyWide and AsmAvailable([cfAvx2]) then
  begin
    g := n div 4;
    PolyBlocksAvx2(P, Data, g);
    Inc(Data, 64 * g); Dec(Len, 64 * g); Dec(n, 4 * g);
  end;
  if (n >= 4) and ChaChaUseAsm and AsmAvailable([cfSse2]) then
    PolyBlocksAsm(P, Data, n)
  else
  {$ENDIF}
  for i := 0 to n - 1 do PolyBlock(P, Data + i * 16, 1 shl 24);
  r := Len - n * 16;
  if r > 0 then
  begin
    FillChar(blk, 16, 0);
    Move(Data[n * 16], blk[0], r);
    if PadTo16 then
      PolyBlock(P, @blk[0], 1 shl 24)         // AEAD: zero padding to 16 bytes, full block
    else
    begin
      blk[r] := 1;                             // plain Poly1305: a 1 bit after the data
      PolyBlock(P, @blk[0], 0);
    end;
  end;
end;

procedure PolyUpdate(var P: TPoly; const Data: TBytes; PadTo16: Boolean);
begin
  if Length(Data) > 0 then PolyUpdateP(P, @Data[0], Length(Data), PadTo16);
end;

function PolyFinish(var P: TPoly): TBytes;
var h0, h1, h2, h3, h4, c, g0, g1, g2, g3, g4, mask: UInt32; f: UInt64;
begin
  h0 := P.h[0]; h1 := P.h[1]; h2 := P.h[2]; h3 := P.h[3]; h4 := P.h[4];
  c := h1 shr 26; h1 := h1 and $3FFFFFF;
  h2 := h2 + c; c := h2 shr 26; h2 := h2 and $3FFFFFF;
  h3 := h3 + c; c := h3 shr 26; h3 := h3 and $3FFFFFF;
  h4 := h4 + c; c := h4 shr 26; h4 := h4 and $3FFFFFF;
  h0 := h0 + c * 5; c := h0 shr 26; h0 := h0 and $3FFFFFF;
  h1 := h1 + c;
  // g = h + -p
  g0 := h0 + 5; c := g0 shr 26; g0 := g0 and $3FFFFFF;
  g1 := h1 + c; c := g1 shr 26; g1 := g1 and $3FFFFFF;
  g2 := h2 + c; c := g2 shr 26; g2 := g2 and $3FFFFFF;
  g3 := h3 + c; c := g3 shr 26; g3 := g3 and $3FFFFFF;
  g4 := h4 + c - (1 shl 26);
  // select h if h < p, otherwise g (branch-free)
  mask := (g4 shr 31) - 1;
  g0 := g0 and mask; g1 := g1 and mask; g2 := g2 and mask; g3 := g3 and mask; g4 := g4 and mask;
  mask := not mask;
  h0 := (h0 and mask) or g0; h1 := (h1 and mask) or g1; h2 := (h2 and mask) or g2;
  h3 := (h3 and mask) or g3; h4 := (h4 and mask) or g4;
  // h = h % 2^128
  h0 := (h0 or (h1 shl 26));
  h1 := ((h1 shr 6) or (h2 shl 20));
  h2 := ((h2 shr 12) or (h3 shl 14));
  h3 := ((h3 shr 18) or (h4 shl 8));
  // tag = h + s
  f := UInt64(h0) + P.s[0]; h0 := UInt32(f);
  f := UInt64(h1) + P.s[1] + (f shr 32); h1 := UInt32(f);
  f := UInt64(h2) + P.s[2] + (f shr 32); h2 := UInt32(f);
  f := UInt64(h3) + P.s[3] + (f shr 32); h3 := UInt32(f);
  SetLength(Result, 16);
  Move(h0, Result[0], 4); Move(h1, Result[4], 4); Move(h2, Result[8], 4); Move(h3, Result[12], 4);
  {$IFDEF ENDIAN_BIG}{$ERROR XelSSL Poly1305: wymaga little-endian}{$ENDIF}
  FillChar(P, SizeOf(P), 0);
end;

procedure Poly1305MacP(Key32, Msg: PByte; Len: Integer; Tag: PByte);
var P: TPoly; k, t: TBytes;
begin
  SetLength(k, 32);
  Move(Key32^, k[0], 32);
  PolyInit(P, k);
  if Len > 0 then PolyUpdateP(P, Msg, Len, False);
  t := PolyFinish(P);
  Move(t[0], Tag^, 16);
  Wipe(k);
end;

function Poly1305Mac(const Key32: TBytes; const Msg: TBytes): TBytes;
var P: TPoly;
begin
  PolyInit(P, Key32);
  PolyUpdate(P, Msg, False);
  Result := PolyFinish(P);
end;

// tag over AAD and the ciphertext C (CLen bytes)
function AeadTagP(const OtkKey: TBytes; AAD: PByte; AadLen: Integer; C: PByte; CLen: Integer): TBytes;
var P: TPoly; lens: array[0..15] of Byte; i: Integer; a, n: QWord;
begin
  PolyInit(P, OtkKey);
  if AadLen > 0 then PolyUpdateP(P, AAD, AadLen, True);
  if CLen > 0 then PolyUpdateP(P, C, CLen, True);
  a := AadLen; n := CLen;
  for i := 0 to 7 do begin lens[i] := Byte(a shr (8 * i)); lens[8 + i] := Byte(n shr (8 * i)); end;
  PolyUpdateP(P, @lens[0], 16, True);
  Result := PolyFinish(P);
end;

function AeadTag(const OtkKey, AAD: TBytes; C: PByte; CLen: Integer): TBytes;
begin
  if Length(AAD) > 0 then Result := AeadTagP(OtkKey, @AAD[0], Length(AAD), C, CLen)
  else Result := AeadTagP(OtkKey, nil, 0, C, CLen);
end;

function OneTimeKey(const Key, Nonce: TBytes): TBytes;
var z: array[0..31] of Byte;
begin
  FillChar(z, 32, 0);
  SetLength(Result, 32);
  ChaCha20Xor(Key, Nonce, 0, @z[0], @Result[0], 32);
end;

function ChaChaPolySeal(const Key, Nonce, AAD, Plain: TBytes): TBytes;
var otk, tag: TBytes; n: Integer;
begin
  if (Length(Key) <> 32) or (Length(Nonce) <> 12) then raise Exception.Create('XelSSL ChaCha20: invalid key/nonce');
  n := Length(Plain);
  SetLength(Result, n + 16);
  if n > 0 then ChaCha20Xor(Key, Nonce, 1, @Plain[0], @Result[0], n);
  otk := OneTimeKey(Key, Nonce);
  tag := AeadTag(otk, AAD, @Result[0], n);
  Move(tag[0], Result[n], 16);
  Wipe(otk);
end;

function ChaChaPolyOpen(const Key, Nonce, AAD, Data: TBytes; out Plain: TBytes): Boolean;
var otk, tag: TBytes; n: Integer;
begin
  Plain := nil;
  if (Length(Key) <> 32) or (Length(Nonce) <> 12) or (Length(Data) < 16) then Exit(False);
  n := Length(Data) - 16;
  otk := OneTimeKey(Key, Nonce);
  tag := AeadTag(otk, AAD, @Data[0], n);
  Wipe(otk);
  if not SameBytesCT(tag, Copy(Data, n, 16)) then Exit(False);
  SetLength(Plain, n);
  if n > 0 then ChaCha20Xor(Key, Nonce, 1, @Data[0], @Plain[0], n);
  Result := True;
end;

procedure ChaChaPolySealP(const Key, Nonce: TBytes; AAD: PByte; AadLen: Integer; Data: PByte; Len: Integer; Tag: PByte);
var otk, t: TBytes;
begin
  if (Length(Key) <> 32) or (Length(Nonce) <> 12) then raise Exception.Create('XelSSL ChaCha20: invalid key/nonce');
  if Len > 0 then ChaCha20Xor(Key, Nonce, 1, Data, Data, Len);
  otk := OneTimeKey(Key, Nonce);
  t := AeadTagP(otk, AAD, AadLen, Data, Len);
  Move(t[0], Tag^, 16);
  Wipe(otk);
end;

function ChaChaPolyOpenP(const Key, Nonce: TBytes; AAD: PByte; AadLen: Integer; Data: PByte; Len: Integer; Tag: PByte): Boolean;
var otk, t: TBytes; i: Integer; d: Byte;
begin
  if (Length(Key) <> 32) or (Length(Nonce) <> 12) then Exit(False);
  otk := OneTimeKey(Key, Nonce);
  t := AeadTagP(otk, AAD, AadLen, Data, Len);
  Wipe(otk);
  d := 0;
  for i := 0 to 15 do d := d or (t[i] xor Tag[i]);
  Result := d = 0;
  if Result and (Len > 0) then ChaCha20Xor(Key, Nonce, 1, Data, Data, Len);
end;

{$IFDEF XELSSL_X64}
initialization
  InitChaChaAsmConsts;
{$ENDIF}
end.
