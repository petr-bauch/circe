// Differential-test driver for the N4d-iv-a `std::vector` reads:
// args are `n v0 ... v(n-1)` (values as signed 64-bit, range-checked
// to `int32_t`), prints `vec_read_sum` over the vector on one line by
// calling the real `vec_read_sum` (so tampering the C++ under test is
// caught). The vector is built locally (the entry takes it by
// `const&`; the caller owns construction — growth paths never run
// here). Overflow inputs never reach this binary: the Lean fuzzer
// only calls it when the checked-add fold is `.ok` (all adds in
// range — signed overflow is UB, so native has nothing to compare
// there; OOB indices likewise never reach native).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

int32_t vec_read_sum(const std::vector<int32_t> &v);

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
  printf("%d\n", (int)vec_read_sum(v));
  return 0;
}
