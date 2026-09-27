// skip_sum: break/continue in a bounded u32 loop.
// Discipline: single `cir.for` with `i < n`; `continue` skips `i == 2`,
// `break` exits at `i == 8`; the only accumulation is wrapping `s += i`.
// Spec: return = sum of i in [0, min(n,8)) except i == 2 (wrapping u32).
#include <stdint.h>

uint32_t skip_sum(uint32_t n) {
  uint32_t s = 0;
  for (uint32_t i = 0; i < n; i++) {
    if (i == 2) {
      continue;
    }
    if (i == 8) {
      break;
    }
    s += i;
  }
  return s;
}
