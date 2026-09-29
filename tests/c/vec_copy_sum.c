// vec_copy_sum: two live heap blocks (u32-only, strict free).
// Discipline: malloc(n) twice with n the same-function length, fill a
// with indices, copy a into b, sum b, free(a) then free(b), no escape.
// The two blocks are disjoint by construction (two `malloc` results);
// the Lean model captures this as two separate values (M1a).
// Spec: return = sum of indices 0 .. n-1 (wrapping u32), i.e. the same
// result as `vec_alloc` with the copy in the middle.
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

uint32_t vec_copy_sum(size_t n) {
  uint32_t *a = (uint32_t *)malloc(n * sizeof(uint32_t));
  uint32_t *b = (uint32_t *)malloc(n * sizeof(uint32_t));
  for (size_t i = 0; i < n; i++) {
    a[i] = (uint32_t)i;
  }
  for (size_t j = 0; j < n; j++) {
    b[j] = a[j];
  }
  uint32_t s = 0;
  for (size_t k = 0; k < n; k++) {
    s += b[k];
  }
  free(a);
  free(b);
  return s;
}
