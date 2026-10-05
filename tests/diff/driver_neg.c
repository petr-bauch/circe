// Differential-test driver for `neg`: arg is `x` (as signed 32-bit),
// prints `neg(x)` by calling the real function (so tampering the C
// under test is caught). `INT_MIN` exits 3 (negation overflow is UB;
// the Lean fuzzer only feeds in-range values to native and asserts
// Lean-Lean agreement on overflow).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int neg(int x);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  long v = strtol(argv[1], 0, 10);
  if (v < (long)INT32_MIN || v > (long)INT32_MAX)
    return 2;
  int32_t x = (int32_t)v;
  // Stay in range (nsw discipline); INT_MIN is driver misuse.
  if (x == INT32_MIN)
    return 3;
  printf("%d\n", neg(x));
  return 0;
}
