// vec_partition_copy: out-of-place Lomuto predicate split
// (the `std::partition_copy` idiom) over a read-only vector into
// two caller-sized records — the P2-M3 predicate test writing
// out of place, P2-M12's out-borrow discipline composed twice.
// Discipline: `a` is a read-only borrow, `yes`/`no` are
// caller-sized mutable borrows, `pivot` is an owned `i32`.
// Read cursor `r` scans; keep predicate `a.at(r) < pivot`
// (the P2-M3 Lomuto test, signed); write cursors `wYes`/`wNo`
// record into `yes`/`no`. Every access goes through the
// checked `at()` path; `wYes` counts the keepers, returned at
// the end (`wYes + wNo = a.size()` at exit, so the dropper
// count is implied). Miss legs: a short `yes`/`no` throws
// `std::out_of_range` natively on the non-const `at()` write,
// loud `AssertFail` in the model (the M2 `vec_at_set`
// precedent). Kept and dropped elements keep their original
// order; the caller owes both resizes (both records are only
// ever prefix-written, suffixes untouched).
#include <vector>

unsigned long vec_partition_copy(const std::vector<int> &a,
                                 std::vector<int> &yes,
                                 std::vector<int> &no, int pivot) {
  unsigned long r = 0, wYes = 0, wNo = 0;
  while (r < a.size()) {
    if (a.at(r) < pivot) {
      yes.at(wYes) = a.at(r);
      wYes = wYes + 1;
    } else {
      no.at(wNo) = a.at(r);
      wNo = wNo + 1;
    }
    r = r + 1;
  }
  return wYes;
}
