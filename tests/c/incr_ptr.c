// incr_ptr: single unique mutable borrow.
// Discipline: p is __restrict__, non-escaping, single live owner.
// Aeneas analogue: x := incr_fwd x.
// Spec: *p' = *p + 1.
#include <stdint.h>

void incr(int32_t *__restrict p) {
  *p = *p + 1;
}
