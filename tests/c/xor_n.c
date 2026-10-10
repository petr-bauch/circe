// xor_n: bounded buffer xor kernel (K2).
// Discipline: `out` is `__restrict__` (mutBorrow), `a`/`b` const
// `__restrict__` readers (sharedBorrow), length-paired `n`; single
// bounded `for` loop, stores only to `out[i]`, one xor per iteration.
// All three buffers carry attr text (the verdict confirms claims but
// never substitutes for missing text — the A-track policy).
// Spec: out[i] = a[i] ^ b[i] for 0 <= i < n.
#include <stddef.h>
#include <stdint.h>

void xor_n(uint32_t *__restrict out, const uint32_t *__restrict a,
           const uint32_t *__restrict b, size_t n) {
  for (size_t i = 0; i < n; i++) {
    out[i] = a[i] ^ b[i];
  }
}
