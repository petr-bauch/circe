// Differential-test driver for in-place `std::vector<int>` segment
// reverse: args are `n w0 ... w(n-1) lo hi` (values as signed 64-bit,
// range-checked to `int32_t`; length capped small). Applies the real
// `vec_seg_reverse(v, lo, hi)` entry (so tampering the C++ under test
// is caught) and prints the resulting `v` as `m w0 ... w(m-1)` on one
// line (`m == n` always — segment reversal preserves length).
// Bad usage (arity, out-of-range window) exits 2, out-of-`int32`
// words exit 3. Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

void vec_seg_reverse(std::vector<int32_t> &v, uint64_t lo, uint64_t hi);

int main(int argc, char **argv) {
  if (argc < 4)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 10 || argc != 4 + n)
    return 2;
  std::vector<int32_t> v;
  for (long k = 0; k < n; k++) {
    long long w = strtoll(argv[2 + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    v.push_back((int32_t)w);
  }
  long lo = strtol(argv[2 + n], 0, 10);
  long hi = strtol(argv[3 + n], 0, 10);
  if (lo < 0 || hi < lo || hi > n)
    return 2;
  vec_seg_reverse(v, (size_t)lo, (size_t)hi);
  printf("%lu", (unsigned long)v.size());
  for (size_t k = 0; k < v.size(); k++)
    printf(" %d", v[k]);
  printf("\n");
  return 0;
}
