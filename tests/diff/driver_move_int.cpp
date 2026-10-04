// Differential-test driver for N4b-i `move_int`: args are `x y`
// (as signed ints), prints `move_int(x,y)` on one line by calling the
// real function (so tampering the C++ under test is caught).
// Out-of-range results exit 3 (signed overflow is UB; the Lean fuzzer
// only feeds in-range values to native and asserts Lean-Lean
// agreement on overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

int32_t move_int(int32_t a, int32_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long x = strtol(argv[1], 0, 10);
  long y = strtol(argv[2], 0, 10);
  long s = x + y;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (s < INT32_MIN || s > INT32_MAX)
    return 3;
  int32_t m = move_int((int32_t)x, (int32_t)y);
  printf("%ld\n", (long)m);
  return 0;
}
