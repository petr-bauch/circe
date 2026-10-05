// cls_break: switch with `break` exits and no `default`, if-chain lowerable.
// Discipline: `cir.switch` with equality cases on `0`/`1` and no `default`;
// every case stores a const to the result local and exits via `cir.break`;
// the function epilogue returns the local (unmatched scrutinees keep the
// `99` initializer). The validator admits exactly this shape and maps it
// to guarded assigns over a `99`-initialized local (the `break`s erase:
// disjoint guards make the sequential assigns exact).
// Spec: 0 -> 10, 1 -> 20, else 99.
#include <stdint.h>

uint32_t cls_break(uint32_t x) {
  uint32_t r = 99;
  switch (x) {
  case 0:
    r = 10;
    break;
  case 1:
    r = 20;
    break;
  }
  return r;
}
