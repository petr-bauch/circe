// vec_merge_sort: bottom-up merge sort over a mutable vector.
// Discipline: `a` is a mutable borrow sorted in place; `tmp` is a
// second mutable borrow pre-sized by the caller to at least
// `a.size()` (the entry never grows — indexed writes only, the
// `merge_into` caller discipline). The ranged `merge_runs` callee
// merges the segments `[lo,mid)` and `[mid,hi)` ofreadonly `a`
// into `tmp` at `[lo..]` through the const `at()` checked read and
// the borrowed `at()` checked write; the entry copies each merged
// run back into `a`. The comparison is strict `<` (existing `slt`;
// the right run takes equal elements — still a correct sort). The
// `mid`/`hi` clamps use `<`-form conditions (like every u64 guard,
// they fuse to Nat propositions downstream). Miss legs: input
// overrun is impossible (guards); short `tmp` throws
// `std::out_of_range` natively, loud `AssertFail` in the model (the
// `vec_at_set` precedent). Sortedness is caller debt (brute-force
// agreement holds regardless, the V1 `vec_binary_search`
// precedent).
#include <vector>

void merge_runs(const std::vector<int> &a, std::vector<int> &tmp,
               unsigned long lo, unsigned long mid, unsigned long hi) {
  unsigned long i = lo, j = mid, k = lo;
  while (i < mid && j < hi) {
    if (a.at(i) < a.at(j)) {
      tmp.at(k) = a.at(i);
      i = i + 1;
    } else {
      tmp.at(k) = a.at(j);
      j = j + 1;
    }
    k = k + 1;
  }
  while (i < mid) {
    tmp.at(k) = a.at(i);
    i = i + 1;
    k = k + 1;
  }
  while (j < hi) {
    tmp.at(k) = a.at(j);
    j = j + 1;
    k = k + 1;
  }
}

void vec_merge_sort(std::vector<int> &a, std::vector<int> &tmp) {
  unsigned long n = a.size();
  unsigned long width = 1;
  while (width < n) {
    unsigned long lo = 0;
    while (lo < n) {
      unsigned long mid = lo + width;
      if (n < mid) {
        mid = n;
      }
      unsigned long hi = lo + width + width;
      if (n < hi) {
        hi = n;
      }
      merge_runs(a, tmp, lo, mid, hi);
      unsigned long t = lo;
      while (t < hi) {
        a.at(t) = tmp.at(t);
        t = t + 1;
      }
      lo = lo + width + width;
    }
    width = width + width;
  }
}
