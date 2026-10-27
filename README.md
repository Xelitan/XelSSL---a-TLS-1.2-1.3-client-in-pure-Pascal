# XelSSL — a TLS 1.2 / 1.3 client in pure Pascal

About 5,000 lines, no DLLs and no OpenSSL. Works on every platform supported by
Free Pascal.

XelSSL has no code from CryptoLib4Pascal, TlsLib4Pascal nor
HashLib4Pascal.

## Speed: Pascal everywhere, assembler as an addition

Every algorithm is written in Pascal and works on every platform Free Pascal supports.
On x86-64 some of them also have an assembler version, which is used only when CPUID
reports the needed instructions (`XelSslCpu`); `XelSslAsm := False` switches all of
them off (the tests run everything both ways and compare).

One core of an i7-13700F (MB/s, X25519 in operations per second):

| | Pascal | with the x86-64 additions | addition |
|---|---|---|---|
| AES-128-GCM | 86 | 12 600 | VAES + VPCLMULQDQ: CTR and GHASH in one loop, 16 blocks per step; AVX: 8 blocks (8 300); AES-NI only: 4 blocks, two passes (4 700) |
| AES-256-GCM | - | 11 000 | the same |
| ChaCha20-Poly1305 | 414 | 2 800 | ChaCha20 with AVX2, 8 blocks in column layout (4 100 alone); Poly1305 with AVX2, 4 blocks in 64-bit lanes (9 200 alone) |
| SHA-256 | 368 | 2 404 | SHA-NI |
| SHA-384 / SHA-512 | 510 | 1 040 | AVX2 message schedule of two blocks at once (one per pair of lanes), interleaved with scalar rounds (RORX/ANDN, Sigma0 deferred to the next round as in OpenSSL), loops of 8 rounds (4.6 KB of code) |
| SHA-1 | 454 | same | - |
| X25519 key pair (fixed base) | - | 105 500 /s | the Edwards form with a precomputed table (32 x 8 points, test/gen_x25519_base.py), 64 additions + 4 doublings, signed digits, constant-time selection; u = (Z + Y) / (Z - Y) |
| X25519 | 13 400 /s | 49 700 /s | BMI2 + ADX: the whole ladder in one assembler block, 4 x 64-bit limbs below 2^256 (2^256 = 38 mod p), MULX/ADCX/ADOX, independent products next to each other; otherwise 5 x 51-bit limbs with MUL (21 500 /s) |
| ECDSA P-256 verify | 2 150 /s | 22 700 /s | P-256 on 4 x 64-bit limbs: MULX multiplication and squaring with a shift-based reduction (the shape of p, carry deferred to the next round); u2 * Q in the assembler window loop, u1 * G from a fixed table (52 x 16 affine points, built on first use) with mixed additions; s^-1 mod n by the binary GCD on approximations (Pornin, 1.7 us) |
| ECDH P-256 shared | - | 28 100 /s | the same arithmetic; the whole window loop in assembler: signed 5-bit digits (Booth, as OpenSSL) on k + n, constant-time selection of 16 entries; the inversion by an addition chain |
| ECDH P-256 key pair | - | 69 200 /s | k * G from the fixed table: 52 mixed additions, no doublings, constant-time selection of 16 affine entries |
| ECDSA P-384 verify | - | 6 150 /s | 6 x 64-bit MULX Montgomery multiplication, add/sub and whole point routines in assembler (test/gen_p384_asm.py, gen_p384_points.py) |
| RSA-2048 verify | - | 79 400 /s | Montgomery multiplication and a separate squaring (cross products once) with MULX/ADCX/ADOX, two carry chains through the loops (LEA + JRCXZ keep the flags), final subtraction in the kernel; for multiples of 256 bits, MUL/ADC otherwise; R^2 mod n cached for recent keys |

AEAD figures: sealing 1 MB in place (`GcmSealP`, `ChaChaPolySealP`, as the TLS and SSH
record layers do); decryption runs at the same speed.

OpenSSL 3.2.3 on the same core: AES-128-GCM 9 170 MB/s, ChaCha20-Poly1305 2 890 MB/s,
SHA-256 2 340 MB/s, SHA-384 1 080 MB/s, X25519 51 400/s, ECDSA P-256 verify 21 730/s
(sign 67 800/s: k * G from a table, as our key pair), ECDSA P-384 verify 2 700/s,
ECDH P-256 28 290/s, RSA-2048 verify 85 900/s. The i7-13700F mixes P- and E-cores:
benchmarks must be pinned to one core (an E-core gives about half of these figures).

TlsLib4Pascal (CryptoLib4Pascal with its SIMD code) on the same machine, measured the
same way: AES-128-GCM 8 180 MB/s (8 blocks, CTR and GHASH fused), ChaCha20-Poly1305
2 850 MB/s, SHA-256 2 366 MB/s, SHA-384 1 052 MB/s, X25519 15 550/s, RSA-2048 verify
4 202/s, ECDSA P-256 verify 3 736/s.

The GCM, ChaCha20 and Poly1305 kernels are written as assembler source by Python
generators (`test/gen_gcm_asm.py`, `gen_chacha_asm.py`, `gen_poly_asm.py`), assembled
with GNU as (WSL) and included as `db` bytes with the instruction in a comment
(`XelSslGcmAvx.inc`, `XelSslGcmVaes.inc`, `XelSslChaChaAvx2.inc`, `XelSslPolyAvx2.inc`):
FPC 3.2.2 does not know the VAES/VPCLMULQDQ mnemonics. Lookup tables are deliberately
not used: AES T-tables and table-driven GHASH read memory at secret-dependent addresses
(a cache-timing leak), and AES-NI is faster anyway.

## Features

| | |
|---|---|
| Versions | TLS 1.3, TLS 1.2 (with downgrade protection) |
| TLS 1.3 suites | AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305 |
| TLS 1.2 suites | ECDHE-ECDSA/RSA with AES-128/256-GCM and ChaCha20-Poly1305 |
| Key exchange | X25519, P-256, P-384, P-521 (HelloRetryRequest in 1.3) |
| Signatures | RSA PKCS#1 v1.5, RSA-PSS, ECDSA P-256/384/521 |
| Resumption | 1.3: PSK tickets (psk_dhe_ke); 1.2: session IDs and tickets (RFC 5077) |
| Other | SNI, ALPN, extended master secret, KeyUpdate, renegotiation refused |
| Certificates | full path building, validity dates, basicConstraints/pathLen, keyUsage, EKU, nameConstraints (DNS/IP/DN), unknown critical extensions, host name (RFC 6125, IPv4/IPv6) |
| CA store | Windows: ROOT/CA minus Disallowed, plus a fallback to the system chain engine (fetches missing roots). Linux/BSD/macOS: CA bundles, `SSL_CERT_FILE`/`SSL_CERT_DIR` |

Operations on secrets (AES, GHASH, ChaCha20, Poly1305, X25519, ECDH) run in constant time.

## Limitations

- client only (no server mode, no client certificates — an empty one is sent when requested);
- no revocation checking (CRL/OCSP), like most non-browser clients;
- no CBC suites and no RSA key exchange in TLS 1.2 (ECDHE + AEAD only);
- no 0-RTT, compression, Ed25519/Ed448 or Brainpool curves in certificates;
- tested on Windows; the Unix code paths (`/dev/urandom`, CA bundle files, sockets) have not been built or run yet.

## Files

| Unit | Contents |
|---|---|
| XelSslHash | SHA-1/256/384/512, HMAC, HKDF, TLS 1.2 PRF |
| XelSslAes | AES (AES-NI or bitsliced), AES-GCM (PCLMULQDQ or portable GHASH); `XelSslAesSbox.inc` is generated |
| XelSslCurves | parameters of P-256/384/521 (generated) |
| XelSslCpu | CPU feature detection, `XelSslAsm` switch |
| XelSslFe25519 | arithmetic mod 2^255-19 (X25519, Ed25519): Pascal 10 x 25.5-bit limbs (`XelSslFe25519Mul.inc` generated), x86-64 addition 5 x 51-bit limbs |
| XelSslChaCha | ChaCha20-Poly1305 |
| XelSslX25519, XelSslEcdh | X25519, ECDH on P-256/384/521 |
| XelSslBigNum, XelSslPk | big numbers, RSA/ECDSA verification |
| XelSslX509, XelSslTrust | X.509, path validation, CA store |
| XelSslRandom | OS CSPRNG |
| XelSslClient | the TLS protocol (transport through two functions) |
| XelSslFclNet | `TSSLSocketHandler` handler (TFPHTTPClient, TInetSocket) |

## Usage

With fcl-net it is enough to add `XelSslFclNet` to `uses` — it registers itself as the
default SSL handler, so `TFPHTTPClient` handles `https://` URLs. To upgrade an
already connected socket (STARTTLS), use `TXelSslSocketHandler.Attach` + `Connect`.
`TXelSslClient` can also be used directly with any transport (two callbacks: send
and receive raw bytes).

Connections made through `XelSslFclNet` share a process-wide session cache
(`XelSslSharedCache`, keyed by host and port), so a new connection to a known server
resumes the session (a shorter handshake). It is used only for connections verified
against the system store; a handler with its own `SessionCache`, its own `TrustStore`
or without verification does not touch it.

Records are built and encrypted in place and decrypted in place in the receive
buffer; application data is copied once, from there into the caller's buffer
(TLS 1.3 download over a VM network: 1 060–1 400 MB/s). `ReadAhead` + `ShutdownFn`
(or `TXelSslSocketHandler.ReadAhead`) start a reader thread that receives and decrypts
records after the handshake, pausing after each post-handshake message (KeyUpdate
changes the keys). It is off by default: when the caller does little with the data,
the hand-off between threads costs as much as the overlap saves.

## License

MIT — see [LICENSE](LICENSE), which also credits the authors of the code this
library builds on.
