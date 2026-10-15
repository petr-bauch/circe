// Differential-test driver for brute-force two-sum over `const std::vector<int>&`:
// args are `n v0 ... v(n-1) target` (values as signed 64-bit,
// range-checked to `int32_t`), prints `vec_two_sum` (the nested-loop
// search: the first `(i, j)` with `v[i] + v[j] == target`, miss
// returns `(n, n)`) as `a b` on one line by calling the real entry
// (so tampering the C++ under test is caught). The vector is built
// locally (the entry takes it by `const&`; the caller owns
// construction — growth paths never run here). The arg count is exact
// (`argc == 3 + n`): the Lean fuzzer sends exactly the vector words
// plus the target. Overflow leg: the `i32` element add may overflow —
// native agrees only on non-overflowing inputs; the Lean side asserts
// eval/fwd agreement everywhere (the `nsw` loud leg, Lean-Lean only
// on overflow). Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

struct IPair {
  int a;
  int b;
};

IPair vec_two_sum(const std::vector<int> &v, int target);

int main(int argc, char **argv) {
  if (argc < 3)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc != 3 + n)
    return 2;
  std::vector<int32_t> v;
  for (long i = 0; i < n; i++) {
    long long x = strtoll(argv[2 + i], 0, 10);
    if (x < INT32_MIN || x > INT32_MAX)
      return 3;
    v.push_back((int32_t)x);
  }
  long long t = strtoll(argv[2 + n], 0, 10);
  if (t < INT32_MIN || t > INT32_MAX)
    return 3;
  IPair p = vec_two_sum(v, (int)t);
  printf("%d %d\n", p.a, p.b);
  return 0;
}
