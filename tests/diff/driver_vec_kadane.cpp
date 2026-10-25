// Differential-test driver for Kadane maximum subarray:
// args are `n v0 ... v(n-1)` (values as signed 64-bit, range-checked
// to `int32_t`), prints `max_subarray` (the `v.at(i)` Kadane fold)
// on one line by calling the real entry (so tampering the C++ under
// test is caught). The vector is built locally (the entry takes it
// by `const&`; the caller owns construction — growth paths never run
// here). The arg count is exact (`argc == 2 + n`): the Lean fuzzer
// sends exactly the vector words (the N2d window-shift lesson).
// Overflow and empty inputs never reach this binary: the Lean fuzzer
// only calls it when the Kadane fold is `.ok` (signed overflow is
// UB and empty input throws in C++, so native has nothing to compare
// there — those legs assert Lean-Lean agreement only).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

int32_t max_subarray(const std::vector<int32_t> &v);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 16 || argc != 2 + n)
    return 2;
  std::vector<int32_t> v;
  for (long i = 0; i < n; i++) {
    long long x = strtoll(argv[2 + i], 0, 10);
    if (x < INT32_MIN || x > INT32_MAX)
      return 3;
    v.push_back((int32_t)x);
  }
  printf("%d\n", (int)max_subarray(v));
  return 0;
}
