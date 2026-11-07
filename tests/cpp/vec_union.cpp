// vec_union: two-cursor sorted-range union over mutable
// vectors. Discipline: `a` and `b` are read-only borrows, `out` is
// a caller-sized mutable borrow (the caller owes
// a.size() + b.size()). Every access goes through the
// checked `at()` path; the guards `i < a.size()` and
// `j < b.size()` keep all indices in bounds. Both inputs are
// sorted (caller debt). Heads record in order (max-count
// multiplicity for duplicates: equal heads record once and
// advance both); each drain copies the survivor suffix; `w`
// counts the records and the caller owes the resize past `w`.
#include <vector>

unsigned long vec_union(std::vector<int> &a, std::vector<int> &b,
                        std::vector<int> &out) {
  unsigned long i = 0, j = 0, w = 0;
  while (i < a.size() && j < b.size()) {
    if (a.at(i) < b.at(j)) {
      out.at(w) = a.at(i);
      i = i + 1;
      w = w + 1;
    } else if (b.at(j) < a.at(i)) {
      out.at(w) = b.at(j);
      j = j + 1;
      w = w + 1;
    } else {
      out.at(w) = a.at(i);
      i = i + 1;
      j = j + 1;
      w = w + 1;
    }
  }
  while (i < a.size()) {
    out.at(w) = a.at(i);
    i = i + 1;
    w = w + 1;
  }
  while (j < b.size()) {
    out.at(w) = b.at(j);
    j = j + 1;
    w = w + 1;
  }
  return w;
}
