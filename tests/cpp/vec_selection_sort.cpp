// vec_selection_sort: iterative selection sort over a mutable vector.
// Discipline: `v` is a mutable borrow sorted in place; the inner
// min-scan is a call-free leaf over a read-only borrow (the M1
// `merge_runs` precedent: the entry passes its mutable borrow where
// a `const&` is expected); every access goes through the const /
// borrowed `at()` checked paths; all indices stay below `v.size()`
// (the loop guards), so the model is total. The outer scan always
// swaps (possibly self-swaps on the last iteration) — no branch,
// one loop shape per function.
#include <vector>

unsigned long min_index(const std::vector<int> &a, unsigned long lo) {
  unsigned long m = lo;
  unsigned long j = lo + 1;
  while (j < a.size()) {
    if (a.at(j) < a.at(m)) {
      m = j;
    }
    j = j + 1;
  }
  return m;
}

void vec_selection_sort(std::vector<int> &v) {
  unsigned long n = v.size();
  unsigned long i = 0;
  while (i < n) {
    unsigned long m = min_index(v, i);
    int t = v.at(i);
    v.at(i) = v.at(m);
    v.at(m) = t;
    i = i + 1;
  }
}
