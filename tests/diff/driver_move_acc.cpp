// Differential-test driver for N4b-ii `move_acc`: args are `x y`
// (as signed ints), prints `move_acc(x,y)` on one line by calling the
// real function (so tampering the C++ under test is caught).
// Out-of-range results exit 3 (signed overflow is UB; the Lean fuzzer
// only feeds in-range values to native and asserts Lean-Lean
// agreement on overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

int32_t move_acc(int32_t a, int32_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long x = strtol(argv[1], 0, 10);
  long y = strtol(argv[2], 0, 10);
  long s1 = 0 + x;
  long s2 = s1 + y;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (s1 < INT32_MIN || s1 > INT32_MAX || s2 < INT32_MIN || s2 > INT32_MAX)
    return 3;
  int32_t m = move_acc((int32_t)x, (int32_t)y);
  printf("%ld\n", (long)m);
  return 0;
}
