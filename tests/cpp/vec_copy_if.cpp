// vec_copy_if: out-of-place filter (the `std::copy_if` idiom) over a
// read-only vector — the P2-M9 compaction scan writing into a
// caller-sized output. Discipline: `a` is a read-only borrow, `out`
// is a caller-sized mutable borrow, `x` is an owned `i32`.
// Read cursor `r` scans; keep predicate `a.at(r) != x` (the M9 scan);
// write cursor `w` records into `out`. Every access goes through the
// checked `at()` path; `w` counts the kept elements, returned at the
// end. Miss legs: short `out` throws `std::out_of_range` natively on
// the non-const `at()` write, loud `AssertFail` in the model (the
// M2 `vec_at_set` precedent). Kept elements keep their original
// order; the caller owes no resize (out is only ever prefix-written,
// suffix untouched).
#include <vector>

unsigned long vec_copy_if(const std::vector<int> &a, std::vector<int> &out,
                          int x) {
  unsigned long r = 0, w = 0;
  while (r < a.size()) {
    if (a.at(r) != x) {
      out.at(w) = a.at(r);
      w = w + 1;
    }
    r = r + 1;
  }
  return w;
}
