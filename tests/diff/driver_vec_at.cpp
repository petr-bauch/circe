// Differential-test driver for the `std::vector::at` checked read:
// args are `n v0 ... v(n-1)` (values as signed 64-bit, range-checked
// to `int32_t`), prints `vec_at_one` (the `v.at(0)` read) on one line
// by calling the real entry (so tampering the C++ under test is
// caught). The vector is built locally (the entry takes it by
// `const&`; the caller owns construction — growth paths never run
// here). The arg count is exact (`argc == 2 + n`): the Lean fuzzer
// sends exactly the vector words (the N2d window-shift lesson —
// over-long tails would shift reads). Empty vectors never reach this
// binary: `at(0)` throws (`std::out_of_range`), so the OOB leg
// asserts Lean-Lean `AssertFail` agreement plus the native-abort leg
// (this binary exits nonzero on empty).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

int32_t vec_at_one(const std::vector<int32_t> &v);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc != 2 + n)
    return 2;
  std::vector<int32_t> v;
  for (long i = 0; i < n; i++) {
    long long x = strtoll(argv[2 + i], 0, 10);
    if (x < INT32_MIN || x > INT32_MAX)
      return 3;
    v.push_back((int32_t)x);
  }
  printf("%d\n", (int)vec_at_one(v));
  return 0;
}
