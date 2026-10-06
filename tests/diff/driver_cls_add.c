// Differential-test driver for `cls_add`: args are `x` and `y`,
// prints `cls_add(x, y)` by calling the real function (so tampering
// the C under test is caught).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t cls_add(uint32_t x, uint32_t y);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  uint32_t x = (uint32_t)strtoul(argv[1], 0, 10);
  uint32_t y = (uint32_t)strtoul(argv[2], 0, 10);
  printf("%u\n", cls_add(x, y));
  return 0;
}
