// Differential-test driver for `skip_sum`: arg is `n`,
// prints `skip_sum(n)` by calling the real function (so tampering
// the C under test is caught).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t skip_sum(uint32_t n);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  uint32_t n = (uint32_t)strtoul(argv[1], 0, 10);
  printf("%u\n", skip_sum(n));
  return 0;
}
