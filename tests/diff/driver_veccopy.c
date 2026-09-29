// Differential-test driver for `vec_copy_sum`: arg is `n`,
// prints the wrapping `uint32_t` index-sum (unsigned arithmetic: no UB).
// Caps n at 1024 (the Lean side tests small inputs; the bound is a driver
// limit, not a semantic one). The copy between the two blocks is
// value-invisible, so the expected output matches `vec_alloc`.
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t vec_copy_sum(size_t n);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  unsigned long n = strtoul(argv[1], 0, 10);
  if (n > 1024)
    return 2;
  printf("%lu\n", (unsigned long)vec_copy_sum(n));
  return 0;
}
