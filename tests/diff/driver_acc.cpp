// Differential-test driver for `acc_two`: args are `a b`
// (as signed ints), prints `s` by calling the real function (so
// tampering the C++ under test is caught). Out-of-range results exit 3
// (signed overflow is UB; the Lean fuzzer only feeds in-range values
// to native and asserts Lean-Lean agreement on overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

int32_t acc_two(int32_t a, int32_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long a = strtol(argv[1], 0, 10);
  long b = strtol(argv[2], 0, 10);
  long s = a + b;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (s < INT32_MIN || s > INT32_MAX)
    return 3;
  int32_t r = acc_two((int32_t)a, (int32_t)b);
  printf("%ld\n", (long)r);
  return 0;
}
