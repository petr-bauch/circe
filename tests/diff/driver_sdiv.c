// Differential-test driver for `sdiv`: args are `a b` (as signed
// 32-bit), prints `sdiv(a, b)` by calling the real function (so
// tampering the C under test is caught). Zero divisor and `INT_MIN /
// -1` exit 3 (both UB in C; the Lean fuzzer only feeds defined values
// to native and asserts Lean-Lean agreement on `DivZero`/overflow).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int sdiv(int a, int b);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long va = strtol(argv[1], 0, 10);
  long vb = strtol(argv[2], 0, 10);
  if (va < (long)INT32_MIN || va > (long)INT32_MAX ||
      vb < (long)INT32_MIN || vb > (long)INT32_MAX)
    return 2;
  int32_t a = (int32_t)va;
  int32_t b = (int32_t)vb;
  // Stay in defined behavior; UB inputs are driver misuse.
  if (b == 0 || (a == INT32_MIN && b == -1))
    return 3;
  printf("%d\n", sdiv(a, b));
  return 0;
}
