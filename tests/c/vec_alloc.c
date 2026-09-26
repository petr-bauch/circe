// vec_alloc: uniquely-owned heap block (u32-only, strict free).
// Discipline: malloc(n) with n the same-function length, only access
// pattern is v[i] for 0 <= i < n, free(v) exactly once, no escape.
// Aeneas analogue: block as a value with an affine token.
// Spec: return = sum of indices 0 .. n-1 (wrapping u32).
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

uint32_t vec_alloc(size_t n) {
  uint32_t *v = (uint32_t *)malloc(n * sizeof(uint32_t));
  for (size_t i = 0; i < n; i++) {
    v[i] = (uint32_t)i;
  }
  uint32_t s = 0;
  for (size_t j = 0; j < n; j++) {
    s += v[j];
  }
  free(v);
  return s;
}
