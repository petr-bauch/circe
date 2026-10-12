// Differential-test driver for `sha256_compress`: args are the 24 state
// words (8 digest + 16 block, as unsigned 32-bit), prints the compressed
// state by calling the real function (so tampering the C under test is
// caught). Only in-range (24-word) states are exercised here (short
// states are UB in C — those cases assert Lean-Lean `OOB` only).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void sha256_compress(uint32_t *st);

int main(int argc, char **argv) {
  if (argc != 25)
    return 2;
  uint32_t st[24];
  for (int i = 0; i < 24; i++) {
    unsigned long v = strtoul(argv[1 + i], 0, 0);
    if (v > (unsigned long)UINT32_MAX)
      return 2;
    st[i] = (uint32_t)v;
  }
  sha256_compress(st);
  for (int i = 0; i < 24; i++) {
    if (i > 0)
      printf(" ");
    printf("%u", st[i]);
  }
  printf("\n");
  return 0;
}
