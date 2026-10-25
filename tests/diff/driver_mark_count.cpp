// Differential-test driver for the visited-mark idiom: args are
// `nm m0 ... m(nm-1) nv v0 ... v(nv-1) u` (values as signed 64-bit,
// range-checked to `int32_t`; `u` as unsigned 64-bit), applies
// `mark_count(m, vis, u)` to locally built vectors (the entry takes
// the mask by `const&` and the visited vector by mutable `&`; the
// caller owns construction — growth paths never run here) and prints
// the resulting count on one line by calling the real entry (so
// tampering the C++ under test is caught). Any `at()` miss throws
// `std::out_of_range` natively: the driver catches it and exits 4
// (the Lean side expects loud `.error` there — the `vec_at_one`
// empty-read precedent). Overflow inputs never reach this binary:
// the Lean fuzzer only calls it when the gated fold is `.ok`
// (signed overflow is UB, so native has nothing to compare there —
// the `nsw` error leg asserts Lean-Lean agreement only). The arg
// count is exact (`argc == 4 + nm + nv`). Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

int mark_count(const std::vector<int> &m, std::vector<int> &vis,
               unsigned long u);

int main(int argc, char **argv) {
  if (argc < 4)
    return 2;
  long nm = strtol(argv[1], 0, 10);
  if (nm < 0 || nm > 8)
    return 2;
  std::vector<int32_t> m;
  for (long k = 0; k < nm; k++) {
    long long w = strtoll(argv[2 + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    m.push_back((int32_t)w);
  }
  long nv = strtol(argv[2 + nm], 0, 10);
  if (nv < 0 || nv > 8 || argc != 4 + nm + nv)
    return 2;
  std::vector<int32_t> vis;
  for (long k = 0; k < nv; k++) {
    long long w = strtoll(argv[3 + nm + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    vis.push_back((int32_t)w);
  }
  unsigned long u = strtoul(argv[3 + nm + nv], 0, 10);
  int got = 0;
  try {
    got = mark_count(m, vis, u);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%d\n", got);
  return 0;
}
