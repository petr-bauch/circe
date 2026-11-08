// vec_difference: two-cursor sorted-range difference over mutable
// vectors. Discipline: `a` and `b` are read-only borrows, `out` is
// a caller-sized mutable borrow (the caller owes a.size()).
// Every access goes through the checked `at()` path; the guards
// `i < a.size()` and `j < b.size()` keep all indices in bounds.
// Both inputs are sorted (caller debt). Left-only heads record
// in order (a strictly smaller left head records and advances;
// a strictly smaller right head advances only the right cursor;
// equal heads advance both and record nothing); the drain copies
// the surviving left suffix; `w` counts the records and the
// caller owes the resize past `w`.
#include <vector>

unsigned long vec_difference(std::vector<int> &a, std::vector<int> &b,
                             std::vector<int> &out) {
  unsigned long i = 0, j = 0, w = 0;
  while (i < a.size() && j < b.size()) {
    if (a.at(i) < b.at(j)) {
      out.at(w) = a.at(i);
      i = i + 1;
      w = w + 1;
    } else if (b.at(j) < a.at(i)) {
      j = j + 1;
    } else {
      i = i + 1;
      j = j + 1;
    }
  }
  while (i < a.size()) {
    out.at(w) = a.at(i);
    i = i + 1;
    w = w + 1;
  }
  return w;
}
