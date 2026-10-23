// vec_quicksort: in-place recursive quicksort over a mutable vector.
// Discipline: `v` is a mutable borrow; the range `[lo, hi)` is sorted in
// place with `hi <= v.size()` (caller debt — every index stays below
// `v.size()`, the `vec_at_set` precedent). Lomuto partition with the last
// element as pivot and strict `<` (existing `slt`); the two recursive
// calls sort strictly smaller ranges, so the model terminates by fuel
// (each `callProg` steps it down). An empty or singleton range returns
// immediately; `hi <= lo` is the loud-miss guard (no wrapping).
#include <vector>

void vec_quicksort(std::vector<int> &v, unsigned long lo, unsigned long hi) {
  if (hi <= lo) {
    return;
  }
  if (hi - lo < 2) {
    return;
  }
  int pivot = v.at(hi - 1);
  unsigned long s = lo;
  unsigned long i = lo;
  while (i < hi - 1) {
    if (v.at(i) < pivot) {
      int t = v.at(i);
      v.at(i) = v.at(s);
      v.at(s) = t;
      s = s + 1;
    }
    i = i + 1;
  }
  v.at(hi - 1) = v.at(s);
  v.at(s) = pivot;
  vec_quicksort(v, lo, s);
  vec_quicksort(v, s + 1, hi);
}
