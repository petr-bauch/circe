// vec_remove: erase-compress (the `std::remove` idiom) over a
// mutable vector — the first length-changing write. Discipline:
// `v` is a mutable borrow; `x` is an owned `i32`. Two-cursor
// compaction: `w` counts the survivors written to the front,
// `r` scans. Every read goes through the const `at()` checked
// read, every write through the non-const `at()` checked path;
// `w <= r < v.size()` (the loop guard plus the survivor count)
// keeps every access in bounds, so the model is total. Returns
// the new logical length `w` (length out <= length in); the
// caller owes the actual `erase`/`resize` (caller-debt):
// `v[0..w)` holds the survivors in original order, the tail
// past `w` is don't-care — exactly `std::remove` semantics.
#include <vector>

unsigned long vec_remove(std::vector<int> &v, int x) {
  unsigned long w = 0;
  unsigned long r = 0;
  while (r < v.size()) {
    if (v.at(r) != x) {
      v.at(w) = v.at(r);
      w = w + 1;
    }
    r = r + 1;
  }
  return w;
}
