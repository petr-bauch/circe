// Differential-test driver for `find_eq`: args are `k n v0 .. v(n-1)`,
// prints `find_eq(a, n, k)` by calling the real function (so tampering
// the C under test is caught). The fuzzer only passes `n <= len`
// (over-long `n` is UB in C; the Lean side asserts Lean-Lean
// agreement there instead).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t find_eq(const uint32_t *__restrict a, size_t n, uint32_t k);

int main(int argc, char **argv) {
  if (argc < 3)
    return 2;
  uint32_t k = (uint32_t)strtoul(argv[1], 0, 10);
  unsigned long n = strtoul(argv[2], 0, 10);
  if ((unsigned long)(argc - 3) < n)
    return 2;
  uint32_t *a = NULL;
  if (n > 0) {
    a = malloc(n * sizeof(uint32_t));
    if (!a)
      return 3;
    for (unsigned long i = 0; i < n; i++)
      a[i] = (uint32_t)strtoul(argv[3 + i], 0, 10);
  }
  // n == 0 with NULL is fine: the loop never dereferences.
  printf("%u\n", find_eq(a, n, k));
  free(a);
  return 0;
}
