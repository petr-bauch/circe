// Differential-test driver for `add_caller`: args are `x y z`,
// prints the `nsw` sum by calling the real function (so tampering the
// C under test is caught). Out-of-range inputs exit 3 (signed overflow
// is UB; the Lean fuzzer only feeds in-range values to native and
// asserts Lean-Lean agreement on overflow).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

int32_t add_caller(int32_t x, int32_t y, int32_t z);

int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  long x = strtol(argv[1], 0, 10);
  long y = strtol(argv[2], 0, 10);
  long z = strtol(argv[3], 0, 10);
  long t = x + y;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (t < INT32_MIN || t > INT32_MAX || t + z < INT32_MIN || t + z > INT32_MAX)
    return 3;
  int32_t r = add_caller((int32_t)x, (int32_t)y, (int32_t)z);
  printf("%ld\n", (long)r);
  return 0;
}
