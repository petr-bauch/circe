// Differential-test driver for `chacha20_block`: args are the 16 state
// words (as unsigned 32-bit), prints the blocked state by calling the
// real function (so tampering the C under test is caught). Only
// in-range (16-word) states are exercised here (short states are UB
// in C — those cases assert Lean-Lean `OOB` only).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void chacha20_block(uint32_t *state);

int main(int argc, char **argv) {
  if (argc != 17)
    return 2;
  uint32_t state[16];
  for (int i = 0; i < 16; i++) {
    unsigned long v = strtoul(argv[1 + i], 0, 0);
    if (v > (unsigned long)UINT32_MAX)
      return 2;
    state[i] = (uint32_t)v;
  }
  chacha20_block(state);
  for (int i = 0; i < 16; i++) {
    if (i > 0)
      printf(" ");
    printf("%u", state[i]);
  }
  printf("\n");
  return 0;
}
