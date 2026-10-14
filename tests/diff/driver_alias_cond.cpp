// Differential-test driver for `alias_cond` (G3/S3 open contract):
// reads two int32 words (decimal) plus a `0`/`1` condition and a
// `0`/`1` aliased flag, runs `alias_cond(p, q, c)` on two cells — or
// twice on ONE shared cell when `aliased` is set — prints both words.
//
// Only exercised on in-range inputs by the `DiffAliasCond` suite
// (`INT32_MAX` would overflow in C++, which is UB; overflow is
// asserted on the Lean side only, spec-vs-recomputation). The
// `c = false` leg masks the first add: native never computes it.
// Unlike the `noalias` `cond_pair` driver, aliasing is the point:
// `aliased=1` passes the same cell twice, exercising the re-read.
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void alias_cond(int &p, int &q, bool c);

int main(int argc, char **argv) {
  if (argc != 5)
    return 2;
  int32_t p = (int32_t)strtol(argv[1], 0, 10);
  int32_t q = (int32_t)strtol(argv[2], 0, 10);
  bool c = (bool)strtol(argv[3], 0, 10);
  bool aliased = (bool)strtol(argv[4], 0, 10);
  if (aliased) {
    alias_cond(p, p, c);
    printf("%ld %ld\n", (long)p, (long)p);
  } else {
    alias_cond(p, q, c);
    printf("%ld %ld\n", (long)p, (long)q);
  }
  return 0;
}
