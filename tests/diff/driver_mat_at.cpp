// Differential-test driver for the flat-2D index read: args are
// `n v0 ... v(n-1) ncols i j` (values as signed 64-bit,
// range-checked to `int32_t`; dims/indices as unsigned 64-bit),
// applies `mat_at(m, ncols, i, j)` to a locally built vector (the
// entry takes it by `const&`; the caller owns construction — growth
// paths never run here) and prints the result on one line by calling
// the real entry (so tampering the C++ under test is caught). Any
// `at()` miss throws `std::out_of_range` natively: the driver
// catches it and exits 4 (the Lean side expects loud `.error`
// there — the `vec_at_one` empty-read precedent). The index
// computation wraps natively exactly as the model predicts (C++
// unsigned arithmetic — no UB anywhere, so the native leg runs on
// every trial including misses and wraps). The arg count is exact
// (`argc == 5 + n`). Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

int32_t mat_at(const std::vector<int> &m, unsigned long ncols,
               unsigned long i, unsigned long j);

int main(int argc, char **argv) {
  if (argc < 5)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc != 5 + n)
    return 2;
  std::vector<int32_t> v;
  for (long k = 0; k < n; k++) {
    long long w = strtoll(argv[2 + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    v.push_back((int32_t)w);
  }
  unsigned long ncols = strtoul(argv[2 + n], 0, 10);
  unsigned long i = strtoul(argv[3 + n], 0, 10);
  unsigned long j = strtoul(argv[4 + n], 0, 10);
  int got = 0;
  try {
    got = mat_at(v, ncols, i, j);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%d\n", got);
  return 0;
}
