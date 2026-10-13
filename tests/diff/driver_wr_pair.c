// Differential-test driver for `wr_pair` (two-writer admission): reads
// two int32 words (decimal), runs `wr_pair(&p, &q)` on disjoint cells,
// prints the updated pair.
//
// Only exercised on in-range inputs by the `DiffWrPair` suite
// (`p = INT_MAX` would overflow in C, which is UB; overflow is asserted
// on the Lean side only, eval-vs-forward). Aliased callers are
// caller-UB under the `noalias` verdict: documented, never fuzzed.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void wr_pair(int32_t *__restrict p, int32_t *__restrict q);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  int32_t p = (int32_t)strtol(argv[1], 0, 10);
  int32_t q = (int32_t)strtol(argv[2], 0, 10);
  wr_pair(&p, &q);
  printf("%ld %ld\n", (long)p, (long)q);
  return 0;
}
