// Running example for the user guide (README "For users").
// Same shape as the `tests/c/add.c` corpus baseline: pure
// by-value checked addition. Recapture its CIR with
// tools/emit-cir.sh (needs the CIR-enabled clang, docs/PINS.md);
// the gate reuses the checked-in `tests/cir/add.cir` capture,
// whose single `add` definition validates under the synthesized
// `.unknown` default and emits `Hello/Emitted.lean`.
#include <stdint.h>

int32_t add(int32_t a, int32_t b) {
  return a + b;
}
