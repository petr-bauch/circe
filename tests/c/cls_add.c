// cls_add: switch with unsigned wrapping arithmetic in the cases,
// if-chain lowerable. Discipline: `cir.switch` with equality cases on
// `0`/`1` + `default`; the `0`/`1` cases return `y + 1` / `y + 2`
// (plain unsigned `cir.add`, wrapping — no `nsw`); `default` returns
// `y` directly. The validator admits exactly this shape and maps it to
// the `uadd` if-chain canonical Func below (signed/`nsw`/other-op
// compute bodies stay out with a dedicated message).
// Spec: (0, y) -> y + 1, (1, y) -> y + 2, else y (wrapping).
#include <stdint.h>

uint32_t cls_add(uint32_t x, uint32_t y) {
  switch (x) {
  case 0:
    return y + 1;
  case 1:
    return y + 2;
  default:
    return y;
  }
}
