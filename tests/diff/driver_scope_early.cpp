// Differential-test driver for N4b-iii `scope_early`: args are `x y`
// (as signed ints), prints `scope_early(x,y)` on one line by calling
// the real function (so tampering the C++ under test is caught).
// Out-of-range results exit 3 (signed overflow is UB; the Lean fuzzer
// only feeds in-range values to native and asserts Lean-Lean
// agreement on overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

int32_t scope_early(int32_t a, int32_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long x = strtol(argv[1], 0, 10);
  long y = strtol(argv[2], 0, 10);
  long s1 = 0 + x;
  // Early path (x == y) returns s1 without computing s2; only the
  // fallthrough adds y (signed overflow is UB, so out-of-range s2 on
  // the fallthrough path is driver misuse).
  long s2 = s1 + y;
  if (x != y && (s2 < INT32_MIN || s2 > INT32_MAX))
    return 3;
  int32_t m = scope_early((int32_t)x, (int32_t)y);
  printf("%ld\n", (long)m);
  return 0;
}
