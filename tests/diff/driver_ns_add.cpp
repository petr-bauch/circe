// Differential-test driver for the N4a namespace entry: args are
// `x y` (as signed ints), prints `use_ns_add(x,y)` by calling the real
// function (so tampering the C++ under test is caught). Out-of-range
// results exit 3 (signed overflow is UB; the Lean fuzzer only feeds
// in-range values to native and asserts Lean-Lean agreement on
// overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

namespace ns {
int32_t add(int32_t a, int32_t b);
}
int32_t use_ns_add(int32_t x, int32_t y);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long x = strtol(argv[1], 0, 10);
  long y = strtol(argv[2], 0, 10);
  long s = x + y;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (s < INT32_MIN || s > INT32_MAX)
    return 3;
  int32_t r = use_ns_add((int32_t)x, (int32_t)y);
  printf("%ld\n", (long)r);
  return 0;
}
