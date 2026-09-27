// nested_sum: nested bounded loops over u32 indices.
// Discipline: n, m are exact bounds; only op is wrapping `s += i * j`.
// Spec: return = sum over 0<=i<n, 0<=j<m of i*j (wrapping u32).
#include <stdint.h>

uint32_t nested_sum(uint32_t n, uint32_t m) {
  uint32_t s = 0;
  for (uint32_t i = 0; i < n; i++) {
    for (uint32_t j = 0; j < m; j++) {
      s += i * j;
    }
  }
  return s;
}
