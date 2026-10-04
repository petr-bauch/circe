// Differential-test driver for the N4a overload set: args are `x y z`
// (as signed ints), prints `add(x,y) add(x,y,z) use_add(x,y)` on one
// line by calling the real functions (so tampering the C++ under test
// is caught). Out-of-range results exit 3 (signed overflow is UB; the
// Lean fuzzer only feeds in-range values to native and asserts
// Lean-Lean agreement on overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

int32_t add(int32_t a, int32_t b);
int32_t add(int32_t a, int32_t b, int32_t c);
int32_t use_add(int32_t x, int32_t y);

int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  long x = strtol(argv[1], 0, 10);
  long y = strtol(argv[2], 0, 10);
  long z = strtol(argv[3], 0, 10);
  long s2 = x + y;
  long s3 = s2 + z;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (s2 < INT32_MIN || s2 > INT32_MAX || s3 < INT32_MIN || s3 > INT32_MAX)
    return 3;
  int32_t a2 = add((int32_t)x, (int32_t)y);
  int32_t a3 = add((int32_t)x, (int32_t)y, (int32_t)z);
  int32_t u = use_add((int32_t)x, (int32_t)y);
  printf("%ld %ld %ld\n", (long)a2, (long)a3, (long)u);
  return 0;
}
