// Differential-test driver for `cond_pair` (branch-writer admission):
// reads two int32 words (decimal) plus a `0`/`1` condition, runs
// `cond_pair(&p, &q, c)` on disjoint cells, prints the updated pair.
//
// Only exercised on in-range inputs by the `DiffCondPair` suite
// (`INT32_MAX` would overflow in C, which is UB; overflow is asserted
// on the Lean side only, eval-vs-forward). The `c = false` leg masks
// the first add: native never computes it. Aliased callers are
// caller-UB under the `noalias` verdict: documented, never fuzzed.
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void cond_pair(int32_t *__restrict p, int32_t *__restrict q, bool c);

int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  int32_t p = (int32_t)strtol(argv[1], 0, 10);
  int32_t q = (int32_t)strtol(argv[2], 0, 10);
  bool c = (bool)strtol(argv[3], 0, 10);
  cond_pair(&p, &q, c);
  printf("%ld %ld\n", (long)p, (long)q);
  return 0;
}
