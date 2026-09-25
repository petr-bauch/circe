// Differential-test driver for `sum_array`: args are `n v0 v1 ...`,
// prints the wrapping `uint32_t` sum (unsigned arithmetic: no UB).
// Caps n at 64 (the Lean side tests small inputs; the bound is a driver
// limit, not a semantic one).
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t sum_array(const uint32_t *__restrict a, size_t n);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  unsigned long n = strtoul(argv[1], 0, 10);
  if (n > 64 || argc < (int)(n + 2))
    return 2;
  uint32_t a[64];
  for (unsigned long i = 0; i < n; i++)
    a[i] = (uint32_t)strtoul(argv[2 + i], 0, 10);
  printf("%lu\n", (unsigned long)sum_array(a, n));
  return 0;
}
