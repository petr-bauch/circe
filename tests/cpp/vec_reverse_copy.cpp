// vec_reverse_copy: out-of-place reverse (the `std::reverse_copy`
// idiom) over a read-only vector into a caller-sized record — the
// delivered `vec_reverse` countdown scan writing out of place,
// M12's out-borrow composed with the R reverse scan. Discipline:
// `a` is a read-only borrow, `out` is a caller-sized mutable
// borrow. The read cursor `j` counts down from `a.size()` (the
// R `j`-discipline: `0 < j` in the guard means the `j - 1`
// predecessor read never underflows); the write cursor `w`
// counts up from 0 (every M12-family write). Body: `out.at(w) =
// a.at(j - 1)` (the reversed element) then `w = w + 1`.
// Empty vectors return 0 up front (M12 idiom); every access
// goes through the checked `at()` path; `w < out.size()` (the
// record bound) keeps every `out` access in bounds, so the
// model is total on the input side. Returns the element count
// `w` (count out = count in); the caller owes
// `a.size() <= out.size()` (caller-debt): `out[0..w)` holds
// `a` reversed in original order, the input `a` and the `out`
// suffix past `w` are untouched — exactly `std::reverse_copy`
// semantics with short `out` loud.
#include <vector>

unsigned long vec_reverse_copy(const std::vector<int> &a,
                              std::vector<int> &out) {
  if (a.size() == 0) {
    return 0;
  }
  unsigned long w = 0;
  unsigned long j = a.size();
  while (0 < j) {
    j = j - 1;
    out.at(w) = a.at(j);
    w = w + 1;
  }
  return w;
}
