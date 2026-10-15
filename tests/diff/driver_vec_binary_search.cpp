// Differential-test driver for binary search over `const std::vector<int>&`:
// args are `n v0 ... v(n-1) target` (values as signed 64-bit,
// range-checked to `int32_t`), prints `vec_binary_search` (the half-open
// `[lo, hi)` search with the safe midpoint, miss forwards to `v.size()`)
// on one line by calling the real entry (so tampering the C++ under
// test is caught). The vector is built locally (the entry takes it
// by `const&`; the caller owns construction — growth paths never run
// here). The arg count is exact (`argc == 3 + n`): the Lean fuzzer
// sends exactly the vector words plus the target. No UB leg: the
// search performs no arithmetic that can overflow (`lo + (hi - lo)/2`
// with `lo <= hi`), and every element goes through the checked `at()`;
// native agrees on every input, sorted or not (sortedness is caller
// debt for the functional spec, not for entry/native agreement).
// Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

unsigned long vec_binary_search(const std::vector<int> &v, int target);

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
  printf("%lu\n", vec_binary_search(v, (int)t));
  return 0;
}
