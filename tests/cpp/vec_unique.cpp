// vec_unique: adjacent-duplicate squeeze (the `std::unique` idiom) over a
// mutable vector — the P2-M13 length-changing compaction with an equality
// test against the previous survivor. Discipline: `v` is a mutable borrow.
// Empty vectors return 0 up front; otherwise write cursor `w` and read
// cursor `r` both start at 1 (the first element is the implicit first
// survivor, so the `w - 1` predecessor read is always in bounds). Keep
// predicate `v.at(r) != v.at(w - 1)` (the P2-M9 scan with the P2-M10
// read-after-write predecessor read); every access goes through the
// checked `at()` path; `w <= r < v.size()` (the loop guard plus the
// survivor count) keeps every access in bounds, so the model is total.
// Returns the new logical length `w` (length out <= length in); the
// caller owes the actual `erase`/`resize` (caller-debt):
// `v[0..w)` holds one copy per equal run in original order, the tail
// past `w` is don't-care — exactly `std::unique` semantics.
#include <vector>

unsigned long vec_unique(std::vector<int> &v) {
  if (v.size() == 0) {
    return 0;
  }
  unsigned long w = 1;
  unsigned long r = 1;
  while (r < v.size()) {
    if (v.at(r) != v.at(w - 1)) {
      v.at(w) = v.at(r);
      w = w + 1;
    }
    r = r + 1;
  }
  return w;
}
