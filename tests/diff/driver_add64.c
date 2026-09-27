// Differential-test driver for `add64`: args are `a b` (as signed
// 64-bit), prints `add64(a, b)` by calling the real function (so
// tampering the C under test is caught). Out-of-range results exit 3
// (signed overflow is UB; the Lean fuzzer only feeds in-range values
// to native and asserts Lean-Lean agreement on overflow).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

int64_t add64(int64_t a, int64_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  int64_t a = (int64_t)strtoll(argv[1], 0, 10);
  int64_t b = (int64_t)strtoll(argv[2], 0, 10);
  __int128 s = (__int128)a + (__int128)b;
  // Stay in int64 range (nsw discipline); out-of-range is driver misuse.
  if (s < (__int128)INT64_MIN || s > (__int128)INT64_MAX)
    return 3;
  printf("%" PRId64 "\n", add64(a, b));
  return 0;
}
