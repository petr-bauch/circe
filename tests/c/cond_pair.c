// cond_pair: branch writer under restrict (G2b/N13).
// Discipline: p, q are __restrict__ (oracle must confirm `noalias`),
// non-escaping, single live owners; c selects whether `*p += 1`
// fires, `*q += 2` always runs. Disjoint cells commute with the
// branch, so the functionalization (`a = c ? p+1 : p`, `b = q+2`)
// is sound — the unknown-verdict `alias_cond` twin stays deferred
// (no pure function is sound for ordered writers under unknown
// aliasing; see the G3 investigation). Aliased callers are
// caller-UB under `noalias` (documented, unfuzzed).
// Aeneas analogue: (a, b) := cond_pair_fwd p q c.
// Spec: a = c ? *p + 1 : *p, b = *q + 2 (checked `nsw` adds).
#include <stdbool.h>
#include <stdint.h>

void cond_pair(int32_t *__restrict p, int32_t *__restrict q, bool c) {
  if (c) {
    *p = *p + 1;
  }
  *q = *q + 2;
}
