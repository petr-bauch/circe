// cls_fall: switch with fallthrough into the next case, if-chain lowerable.
// Discipline: `cir.switch` with equality cases on consts + default;
// the `case 0` body is empty (a bare `cir.yield`: control falls through
// to `case 1`), every non-empty case is a bare `return` of a const.
// The validator admits exactly this shape and maps it to the nested-`if_`
// canonical Func below (empty case duplicates the fallthrough target).
// Spec: 0 -> 10 (via fallthrough), 1 -> 10, else 30.
#include <stdint.h>

uint32_t cls_fall(uint32_t x) {
  switch (x) {
  case 0:
  case 1:
    return 10;
  default:
    return 30;
  }
}
