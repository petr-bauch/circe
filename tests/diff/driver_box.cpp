// Differential-test driver for `box_through`: arg is `x`
// (as a signed int), prints `r` by calling the real function (so
// tampering the C++ under test is caught). The passthrough is total
// (no overflow possible: `new` never fails, the read is in-bounds,
// `delete` only flips the token), so every input compares.
#include <cstdint>
#include <cstdio>
#include <cstdlib>

int32_t box_through(int32_t x);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  long x = strtol(argv[1], 0, 10);
  int32_t r = box_through((int32_t)x);
  printf("%ld\n", (long)r);
  return 0;
}
