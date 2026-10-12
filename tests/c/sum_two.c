// sum_two: bounded traversal over two length-paired readonly arrays.
// Discipline: a, b are __restrict__ + const, n is the exact length,
// only access patterns are a[i], b[i] for 0 <= i < n.
// Readers never write, so aliasing (a == b) is value-sound: the
// two-reader admission resting on the N2a model-side discipline
// (see Circe.ReadOnly: bindMemArgs_twoShared, twoShared_alias_sound).
// Aeneas analogue: sum_two_fwd (a b : List BV32).
// Spec: return = wrapping sum of pairwise sums of first n elements.
#include <stddef.h>
#include <stdint.h>

uint32_t sum_two(const uint32_t *__restrict a,
                 const uint32_t *__restrict b, size_t n) {
  uint32_t s = 0;
  for (size_t i = 0; i < n; i++) {
    s += a[i] + b[i];
  }
  return s;
}
