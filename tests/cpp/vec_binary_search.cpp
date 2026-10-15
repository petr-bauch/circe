// vec_binary_search: binary search over a readonly sorted vector via `at()`.
// Discipline: `v` is `const&` (single-reference triple, oracle
// governance vacuous, verdict honestly `unknown`); every element
// goes through the const `at()` checked read (`_M_range_check`
// guard + `operator[]` read, both over frozen leaves). The loop
// maintains the half-open interval `[lo, hi)`; the midpoint uses
// `lo + ((hi - lo) >> 1)` so no overflow debt arises. Miss returns
// `v.size()` (find_eq house style); an `i32` index-or-`-1` return
// would need small-width casts, still deferred. Sortedness over
// the signed interpretation is caller debt.
#include <vector>

unsigned long vec_binary_search(const std::vector<int> &v, int target) {
  unsigned long lo = 0, hi = v.size();
  while (lo < hi) {
    unsigned long mid = lo + ((hi - lo) >> 1);
    int m = v.at(mid);
    if (m == target) return mid;
    else if (m < target) lo = mid + 1;
    else hi = mid;
  }
  return v.size();
}
