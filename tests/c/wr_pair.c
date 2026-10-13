// wr_pair: two disjoint mutable writers, functionalized (G2/N12).
// Discipline: p, q are __restrict__ (oracle must confirm `noalias`),
// non-escaping, single live owners; disjoint writes commute, so no
// sequencing license is needed (unlike F1 sequential reborrows).
// Aliased callers are caller-UB under `noalias` (documented, unfuzzed).
// Aeneas analogue: (p', q') := wr_pair_fwd p q.
// Spec: *p' = *p + 1, *q' = *q + 2 (checked `nsw` adds).
#include <stdint.h>

void wr_pair(int32_t *__restrict p, int32_t *__restrict q) {
  *p = *p + 1;
  *q = *q + 2;
}
