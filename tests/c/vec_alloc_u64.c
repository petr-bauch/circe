// vec_alloc_u64: uniquely-owned heap block (u64-only, strict free).
// Discipline: malloc(n) with n the same-function length, only access
// pattern is v[i] for 0 <= i < n, free(v) exactly once, no escape.
// Monomorphized mirror of vec_alloc (M1b): same fill/copy-free/sum
// discipline at width 64; mixed-width access is AssertFail (S3b policy).
// Spec: return = sum of indices 0 .. n-1 (wrapping u64).
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

uint64_t vec_alloc_u64(size_t n) {
  uint64_t *v = (uint64_t *)malloc(n * sizeof(uint64_t));
  for (size_t i = 0; i < n; i++) {
    v[i] = (uint64_t)i;
  }
  uint64_t s = 0;
  for (size_t j = 0; j < n; j++) {
    s += v[j];
  }
  free(v);
  return s;
}
