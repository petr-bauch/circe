// Differential-test driver for `chacha20_encrypt`: args are the 8 key
// words, the counter, the 3 nonce words, the word count, and the
// message words; prints the encrypted message by calling the real
// function (so tampering the C under test is caught). Only in-range
// inputs are exercised here (short inputs are UB in C — those cases
// assert Lean-Lean `OOB` only).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void chacha20_encrypt(const uint32_t *key, uint32_t counter,
                      const uint32_t *nonce, uint32_t *msg,
                      uint32_t nwords);

int main(int argc, char **argv) {
  if (argc < 14)
    return 2;
  uint32_t key[8];
  for (int i = 0; i < 8; i++) {
    unsigned long v = strtoul(argv[1 + i], 0, 0);
    if (v > (unsigned long)UINT32_MAX)
      return 2;
    key[i] = (uint32_t)v;
  }
  unsigned long c = strtoul(argv[9], 0, 0);
  if (c > (unsigned long)UINT32_MAX)
    return 2;
  uint32_t nonce[3];
  for (int i = 0; i < 3; i++) {
    unsigned long v = strtoul(argv[10 + i], 0, 0);
    if (v > (unsigned long)UINT32_MAX)
      return 2;
    nonce[i] = (uint32_t)v;
  }
  unsigned long nw = strtoul(argv[13], 0, 0);
  if (nw > (unsigned long)UINT32_MAX || argc != 14 + (int)nw)
    return 2;
  uint32_t nwords = (uint32_t)nw;
  uint32_t msg[4096];
  if (nwords > 4096)
    return 2;
  for (uint32_t i = 0; i < nwords; i++) {
    unsigned long v = strtoul(argv[14 + i], 0, 0);
    if (v > (unsigned long)UINT32_MAX)
      return 2;
    msg[i] = (uint32_t)v;
  }
  chacha20_encrypt(key, (uint32_t)c, nonce, msg, nwords);
  for (uint32_t i = 0; i < nwords; i++) {
    if (i > 0)
      printf(" ");
    printf("%u", msg[i]);
  }
  printf("\n");
  return 0;
}
