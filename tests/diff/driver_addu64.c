// Differential-test driver for `addu64`: args are `a b` (as unsigned
// 64-bit), prints `addu64(a, b)` by calling the real function (so
// tampering the C under test is caught). Unsigned wrap is defined in C,
// so every input is comparable.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

uint64_t addu64(uint64_t a, uint64_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  uint64_t a = (uint64_t)strtoull(argv[1], 0, 10);
  uint64_t b = (uint64_t)strtoull(argv[2], 0, 10);
  printf("%" PRIu64 "\n", addu64(a, b));
  return 0;
}
