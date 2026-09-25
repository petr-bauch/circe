// Differential-test driver for `add`: reads two int32 (decimal), prints `add(a,b)`.
//
// Only exercised on in-range inputs by `tools/check-phase3.sh` (signed
// overflow is UB in C; overflow behavior is asserted on the Lean side only).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int32_t add(int32_t a, int32_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  int32_t a = (int32_t)strtol(argv[1], 0, 10);
  int32_t b = (int32_t)strtol(argv[2], 0, 10);
  printf("%ld\n", (long)add(a, b));
  return 0;
}
