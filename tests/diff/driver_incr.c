// Differential-test driver for `incr`: reads one int32 (decimal), runs
// `incr(&p)` (caller-side `y ← incr_fwd y`), prints the updated value.
//
// Only exercised on in-range inputs by `tools/check-phase3.sh` (`p = INT_MAX`
// would overflow in C, which is UB; asserted on the Lean side only).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void incr(int32_t *__restrict p);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  int32_t p = (int32_t)strtol(argv[1], 0, 10);
  incr(&p);
  printf("%ld\n", (long)p);
  return 0;
}
