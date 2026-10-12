// Differential-test driver for `sum_two` (two-reader admission): args are
// `n av0 ... bv0 ...` (n words per reader), prints the wrapping
// `uint32_t` pairwise sum (unsigned arithmetic: no UB). In-range legs
// compare against this binary; OOB legs are UB in C, so they assert
// Lean-Lean agreement only. Aliasing (`a == b`) is exercised value-wise
// by passing identical word sequences for both readers.
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t sum_two(const uint32_t *a, const uint32_t *b, size_t n);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  unsigned long n = strtoul(argv[1], 0, 10);
  if (n > 64 || argc < (int)(2 * n + 2))
    return 2;
  uint32_t a[64], b[64];
  for (unsigned long i = 0; i < n; i++)
    a[i] = (uint32_t)strtoul(argv[2 + i], 0, 10);
  for (unsigned long i = 0; i < n; i++)
    b[i] = (uint32_t)strtoul(argv[2 + n + i], 0, 10);
  printf("%lu\n", (unsigned long)sum_two(a, b, n));
  return 0;
}
