// vec_alloc_leak: uniquely-owned heap block, leak variant (M1d).
// Same fill/sum discipline as `vec_alloc` but the block is never freed.
// M1d admits this: leak = forgetting a value, sound for the return value
// (the emitted Lean is `vecFillSumU32 n.toNat`, same body as `vec_alloc`;
// relaxation is validator-side only). Double-`free` / use-after-`free`
// stay loud (affine token + `free <= malloc` gate).
// Spec: return = sum of indices 0 .. n-1 (wrapping u32).
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

uint32_t vec_alloc_leak(size_t n) {
  uint32_t *v = (uint32_t *)malloc(n * sizeof(uint32_t));
  for (size_t i = 0; i < n; i++) {
    v[i] = (uint32_t)i;
  }
  uint32_t s = 0;
  for (size_t j = 0; j < n; j++) {
    s += v[j];
  }
  return s;
}
