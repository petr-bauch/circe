// Differential-test driver for `vec_alloc_leak` (M1d): arg is `n`,
// prints the wrapping `uint32_t` index-sum. Same result as `vec_alloc`:
// leak = forgetting a value, sound for the return value.
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

uint32_t vec_alloc_leak(size_t n);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  unsigned long n = strtoul(argv[1], 0, 10);
  if (n > 1024)
    return 2;
  printf("%lu\n", (unsigned long)vec_alloc_leak(n));
  return 0;
}
