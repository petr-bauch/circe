// sha256_compress: SHA-256 compression function (K5, FIPS 180-4 §6.2).
// Discipline: `st` is the single `__restrict__` 24-word buffer —
// `st[0..8)` digest state, `st[8..24)` message block (single-`&mut`
// containment — one live pointer, so the pair check passes with no
// oracle change; the verdict still confirms the attr). Schedule
// `w[64]`, working vars `v[8]`, round constants `K[64]` are locals
// abstracted downstream as whole-list copies (never address-taken).
// All arithmetic is wrapping unsigned; rotates are shift-or with
// folded `32 - n` amounts (no rotate leaf in the subset — K3
// precedent); `Ch` uses the no-complement identity
// `z ^ (x & (y ^ z))` (no u32 `cir.not` leaf in the subset).
// Spec: compress updates `st[0..8)`; checked against the "abc" vector.
#include <stddef.h>
#include <stdint.h>

#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define S0(x) (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define S1(x) (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define S0M(x) (ROTR(x, 7) ^ ROTR(x, 18) ^ ((x) >> 3))
#define S1M(x) (ROTR(x, 17) ^ ROTR(x, 19) ^ ((x) >> 10))
#define CH(x, y, z) ((z) ^ ((x) & ((y) ^ (z))))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))

void sha256_compress(uint32_t *__restrict st) {
  const uint32_t K[64] = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u,
    0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u,
    0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
    0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u,
    0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
    0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u,
    0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u,
    0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
    0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u,
    0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
    0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u,
    0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u,
    0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u
  };
  uint32_t w[64];
  uint32_t v[8];
  for (size_t t = 0; t < 16; t++)
    w[t] = st[8 + t];
  for (size_t t = 16; t < 64; t++)
    w[t] = w[t - 16] + S0M(w[t - 15]) + w[t - 7] + S1M(w[t - 2]);
  for (size_t i = 0; i < 8; i++)
    v[i] = st[i];
  for (size_t t = 0; t < 64; t++) {
    uint32_t t1 = v[7] + S1(v[4]) + CH(v[4], v[5], v[6]) + K[t] + w[t];
    uint32_t t2 = S0(v[0]) + MAJ(v[0], v[1], v[2]);
    v[7] = v[6];
    v[6] = v[5];
    v[5] = v[4];
    v[4] = v[3] + t1;
    v[3] = v[2];
    v[2] = v[1];
    v[1] = v[0];
    v[0] = t1 + t2;
  }
  for (size_t i = 0; i < 8; i++)
    st[i] += v[i];
}
