// Differential-test driver for the char-width visited-mark idiom:
// args are `nm m0 ... m(nm-1) nv v0 ... v(nv-1) u` (values as signed
// 64-bit, range-checked to `char`; `u` as unsigned 64-bit), applies
// `mark_count_c(m, vis, u)` to locally built `vector<char>`s (the
// entry takes the mask by `const&` and the visited vector by mutable
// `&`; the caller owns construction — growth paths never run here)
// and prints the resulting count on one line by calling the real
// entry (so tampering the C++ under test is caught). Any `at()`
// miss throws `std::out_of_range` natively: the driver catches it
// and exits 4 (the Lean side expects loud `.error` there — the
// `vec_at_one` empty-read precedent). Promotion is the C++ integer
// promotion (`char` to `int`); values outside `char` range never
// reach this binary (the driver range-checks, exit 3). Overflow
// inputs never reach this binary either: the Lean fuzzer only calls
// it when the gated fold is `.ok` (signed overflow is UB, so native
// has nothing to compare — the `nsw` error leg asserts Lean-Lean
// agreement only). The arg count is exact (`argc == 4 + nm + nv`).
// Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

int mark_count_c(const std::vector<char> &m, std::vector<char> &vis,
                 unsigned long u);

int main(int argc, char **argv) {
  if (argc < 4)
    return 2;
  long nm = strtol(argv[1], 0, 10);
  if (nm < 0 || nm > 8)
    return 2;
  std::vector<char> m;
  for (long k = 0; k < nm; k++) {
    long long w = strtoll(argv[2 + k], 0, 10);
    if (w < CHAR_MIN || w > CHAR_MAX)
      return 3;
    m.push_back((char)w);
  }
  long nv = strtol(argv[2 + nm], 0, 10);
  if (nv < 0 || nv > 8 || argc != 4 + nm + nv)
    return 2;
  std::vector<char> vis;
  for (long k = 0; k < nv; k++) {
    long long w = strtoll(argv[3 + nm + k], 0, 10);
    if (w < CHAR_MIN || w > CHAR_MAX)
      return 3;
    vis.push_back((char)w);
  }
  unsigned long u = strtoul(argv[3 + nm + nv], 0, 10);
  int got = 0;
  try {
    got = mark_count_c(m, vis, u);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%d\n", got);
  return 0;
}
