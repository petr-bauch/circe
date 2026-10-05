// cls_dense: switch over eight dense const cases, if-chain lowerable.
// Discipline: `cir.switch` with equality cases on `0`..`7` + default,
// every case body is a bare `return` of a const (no fallthrough).
// At CIR level a dense switch is still `cir.switch` (jump tables only
// appear at LLVM lowering), so the validator admits exactly this shape
// and maps it to the nested-`if_` canonical Func below.
// Spec: 0 -> 0, 1 -> 10, ..., 7 -> 70, else 80.
#include <stdint.h>

uint32_t cls_dense(uint32_t x) {
  switch (x) {
  case 0:
    return 0;
  case 1:
    return 10;
  case 2:
    return 20;
  case 3:
    return 30;
  case 4:
    return 40;
  case 5:
    return 50;
  case 6:
    return 60;
  case 7:
    return 70;
  default:
    return 80;
  }
}
