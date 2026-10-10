// Differential-test driver for the ChaCha20 quarter round (K3).
// NOTE: the `quarter_round` below is test-only scaffolding for the
// KAT leg — it is NOT corpus (never admitted: a 4-word QR leaves
// four live words that no pair shape discharges, so K4 inlines the
// round into the block function instead). Args are `a b c d` (as
// unsigned 32-bit), prints the rounded words by calling the real
// function (so tampering is caught). Addition wraps (unsigned, no
// UB in C); rotates are shift-or.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint32_t rotl32(uint32_t x, unsigned n) {
  return (uint32_t)((x << n) | (x >> (32 - n)));
}

static void quarter_round(uint32_t *a, uint32_t *b, uint32_t *c,
                          uint32_t *d) {
  *a += *b;
  *d = rotl32(*d ^ *a, 16);
  *c += *d;
  *b = rotl32(*b ^ *c, 12);
  *a += *b;
  *d = rotl32(*d ^ *a, 8);
  *c += *d;
  *b = rotl32(*b ^ *c, 7);
}

int main(int argc, char **argv) {
  if (argc != 5)
    return 2;
  uint32_t w[4];
  for (int i = 0; i < 4; i++) {
    unsigned long v = strtoul(argv[1 + i], 0, 10);
    if (v > (unsigned long)UINT32_MAX)
      return 2;
    w[i] = (uint32_t)v;
  }
  quarter_round(&w[0], &w[1], &w[2], &w[3]);
  printf("%u %u %u %u\n", w[0], w[1], w[2], w[3]);
  return 0;
}
