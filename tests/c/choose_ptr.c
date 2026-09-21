// choose_ptr: borrow-return (Aeneas choose-shape).
// Returns exactly one of its inputs; triggers forward + backward functions.
// Discipline: both params __restrict__, noalias (oracle must confirm),
// returned pointer's region ends before x/y are reused.
// Spec (fwd): *ret = b ? *x : *y.
// Spec (back): write through ret propagates to the selected input.
#include <stdbool.h>
#include <stdint.h>

int32_t *choose(bool b, int32_t *__restrict x, int32_t *__restrict y) {
  return b ? x : y;
}
