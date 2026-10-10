// Differential-test driver for `xor_n`: args are `n a0 .. a{n-1}
// b0 .. b{n-1}` (as unsigned 32-bit), prints `out[0] .. out[n-1]` by
// calling the real function (so tampering the C under test is
// caught). `out` starts zeroed; only in-range `n` are exercised here
// (over-long `n` is UB in C — those cases assert Lean-Lean only).
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void xor_n(uint32_t *out, const uint32_t *a, const uint32_t *b, size_t n);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  unsigned long n = strtoul(argv[1], 0, 10);
  if (n > 64 || (unsigned long)argc != 2 + 2 * n)
    return 2;
  uint32_t out[64] = {0};
  uint32_t a[64] = {0};
  uint32_t b[64] = {0};
  for (unsigned long i = 0; i < n; i++) {
    unsigned long x = strtoul(argv[2 + i], 0, 10);
    unsigned long y = strtoul(argv[2 + n + i], 0, 10);
    if (x > (unsigned long)UINT32_MAX || y > (unsigned long)UINT32_MAX)
      return 2;
    a[i] = (uint32_t)x;
    b[i] = (uint32_t)y;
  }
  xor_n(out, a, b, (size_t)n);
  for (unsigned long i = 0; i < n; i++) {
    if (i > 0)
      printf(" ");
    printf("%u", out[i]);
  }
  printf("\n");
  return 0;
}
