// sum_array: bounded array traversal with length-paired param.
// Discipline: a is __restrict__ + const, n is the exact length,
// only access pattern is a[i] for 0 <= i < n.
// Aeneas analogue: sum_fwd (a : List BV32) (h : a.length = n).
// Spec: return = sum of first n elements.
#include <stddef.h>
#include <stdint.h>

uint32_t sum_array(const uint32_t *__restrict a, size_t n) {
  uint32_t s = 0;
  for (size_t i = 0; i < n; i++) {
    s += a[i];
  }
  return s;
}
