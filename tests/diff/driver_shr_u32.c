// Differential-test driver for `shr_u32`: args are `a b` (as unsigned
// 32-bit), prints `shr_u32(a, b)` by calling the real function.
// Amounts >= 32 exit 3 (shift overflow is UB; the Lean fuzzer only
// feeds in-range amounts to native and asserts Lean-Lean agreement
// on `OOB`).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t shr_u32(uint32_t a, uint32_t b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  unsigned long a = strtoul(argv[1], 0, 10);
  unsigned long b = strtoul(argv[2], 0, 10);
  if (a > (unsigned long)UINT32_MAX || b > (unsigned long)UINT32_MAX)
    return 2;
  if (b >= 32)
    return 3;
  printf("%u\n", shr_u32((uint32_t)a, (uint32_t)b));
  return 0;
}
