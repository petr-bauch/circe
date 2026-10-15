// vec_merge_into: out-of-place two-pointer merge over readonly vectors.
// Discipline: `a`/`b` are `const&` (single-reference triple each,
// oracle governance vacuous, verdict honestly `unknown`); `out` is a
// mutable borrow pre-sized by the caller to at least
// `a.size() + b.size()` (the entry never grows — indexed writes only).
// Every read goes through the const `at()` checked read, every write
// through the non-const `at()` checked path (both over frozen
// leaves). The comparison is strict `<` (existing `slt`; the `b`
// branch takes equal elements — still a correct merge). Miss legs:
// input overrun is impossible (guards); short `out` throws
// `std::out_of_range` natively, loud `AssertFail` in the model (the
// `vec_at_set` precedent). Sortedness is caller debt (brute-force
// agreement holds regardless, the V1 `vec_binary_search` precedent).
#include <vector>

void vec_merge_into(const std::vector<int> &a, const std::vector<int> &b,
                    std::vector<int> &out) {
  unsigned long i = 0, j = 0, k = 0;
  while (i < a.size() && j < b.size()) {
    if (a.at(i) < b.at(j)) {
      out.at(k) = a.at(i);
      i = i + 1;
    } else {
      out.at(k) = b.at(j);
      j = j + 1;
    }
    k = k + 1;
  }
  while (i < a.size()) {
    out.at(k) = a.at(i);
    i = i + 1;
    k = k + 1;
  }
  while (j < b.size()) {
    out.at(k) = b.at(j);
    j = j + 1;
    k = k + 1;
  }
}
