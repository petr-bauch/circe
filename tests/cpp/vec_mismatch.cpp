// vec_mismatch: first-index-of-difference query over two read-only
// vectors. Discipline: `a` and `b` are read-only borrows; every
// access goes through the checked `at()` path; the guards
// `i < a.size()` and `i < b.size()` keep all indices in bounds.
// Returns the first index where the elements differ, or the
// shorter length when one input is a prefix of the other.
// A single cursor (no writes, no records, no loud leg).
#include <vector>

unsigned long vec_mismatch(const std::vector<int> &a,
                           const std::vector<int> &b) {
  unsigned long i = 0;
  while (i < a.size() && i < b.size()) {
    if (a.at(i) != b.at(i)) {
      return i;
    }
    i = i + 1;
  }
  return i;
}
