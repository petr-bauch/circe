// find_eq: early return inside a bounded loop.
// Discipline: a is __restrict__ + const, n is the exact length,
// only access pattern is a[i] for 0 <= i < n; the loop body either
// returns the index or falls through.
// Spec: return = first i < n with a[i] == k, else n.
#include <stddef.h>
#include <stdint.h>

uint32_t find_eq(const uint32_t *__restrict a, size_t n, uint32_t k) {
  for (size_t i = 0; i < n; i++) {
    if (a[i] == k) {
      return (uint32_t)i;
    }
  }
  return (uint32_t)n;
}
