// Differential-test driver for `nested_sum`: args are `n m`,
// prints `nested_sum(n, m)` by calling the real function (so tampering
// the C under test is caught).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t nested_sum(uint32_t n, uint32_t m);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  uint32_t n = (uint32_t)strtoul(argv[1], 0, 10);
  uint32_t m = (uint32_t)strtoul(argv[2], 0, 10);
  printf("%u\n", nested_sum(n, m));
  return 0;
}
