// vec_intersect: two-cursor sorted-range intersection over mutable
// vectors. Discipline: `a` and `b` are read-only borrows, `out` is
// a caller-sized mutable borrow. Every access goes through the
// checked `at()` path; the guards `i < a.size()` and
// `j < b.size()` keep all indices in bounds. Both inputs are
// sorted (caller debt). Common elements are written once each
// (min-count multiplicity for duplicates); `w` counts the
// survivors and the caller owes the resize past `w`.
#include <vector>

unsigned long vec_intersect(std::vector<int> &a, std::vector<int> &b,
                            std::vector<int> &out) {
  unsigned long i = 0, j = 0, w = 0;
  while (i < a.size() && j < b.size()) {
    if (a.at(i) < b.at(j)) {
      i = i + 1;
    } else if (b.at(j) < a.at(i)) {
      j = j + 1;
    } else {
      out.at(w) = a.at(i);
      i = i + 1;
      j = j + 1;
      w = w + 1;
    }
  }
  return w;
}
