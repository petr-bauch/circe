// Differential-test driver for `cls_dense`: arg is `x`,
// prints `cls_dense(x)` by calling the real function (so tampering
// the C under test is caught).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t cls_dense(uint32_t x);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  uint32_t x = (uint32_t)strtoul(argv[1], 0, 10);
  printf("%u\n", cls_dense(x));
  return 0;
}
