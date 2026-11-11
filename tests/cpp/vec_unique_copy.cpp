// vec_unique_copy: adjacent-duplicate squeeze (the `std::unique_copy`
// idiom) over a read-only vector into a caller-sized record — the P2-M13
// predecessor-kept scan writing out of place, P2-M12's out-borrow
// discipline composed with the P2-M13 squeeze. Discipline: `a` is a
// read-only borrow, `out` is a caller-sized mutable borrow. Empty
// vectors return 0 up front; otherwise the seed store `out.at(0) =
// a.at(0)` plants the first survivor (loud when `out` is empty), and
// write cursor `w` and read cursor `r` both start at 1 (the seed is the
// implicit first survivor, so the `w - 1` predecessor read against
// `out` is always in bounds). Keep predicate `a.at(r) !=
// out.at(w - 1)` (the P2-M13 squeeze test against the last recorded
// survivor); every access goes through the checked `at()` path;
// `w <= r < a.size()` (the loop guard plus the survivor count) keeps
// every `a` access in bounds, so the model is total on the input side.
// Returns the survivor count `w` (count out <= count in); the caller
// owes `dedupAdj(a).length <= out.size()` and the actual `resize`
// (caller-debt): `out[0..w)` holds one copy per equal run in original
// order, the input `a` and the `out` suffix past `w` are untouched —
// exactly `std::unique_copy` semantics with short `out` loud.
#include <vector>

unsigned long vec_unique_copy(const std::vector<int> &a,
                             std::vector<int> &out) {
  if (a.size() == 0) {
    return 0;
  }
  out.at(0) = a.at(0);
  unsigned long w = 1;
  unsigned long r = 1;
  while (r < a.size()) {
    if (a.at(r) != out.at(w - 1)) {
      out.at(w) = a.at(r);
      w = w + 1;
    }
    r = r + 1;
  }
  return w;
}
