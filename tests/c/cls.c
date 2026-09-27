// cls: switch over small const cases, if-chain lowerable.
// Discipline: `cir.switch` with equality cases on consts + default,
// every case body is a bare `return` of a const (no fallthrough).
// The validator admits exactly this shape and maps it to the nested-`if_`
// canonical Func below (lowering check, S3a).
// Spec: 0 -> 10, 1 -> 20, else 30.
#include <stdint.h>

uint32_t cls(uint32_t x) {
  switch (x) {
  case 0:
    return 10;
  case 1:
    return 20;
  default:
    return 30;
  }
}
