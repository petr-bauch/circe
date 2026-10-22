// vec_partition: in-place Lomuto partition over a mutable vector.
// Discipline: `v` is a mutable borrow; `pivot` is an owned `i32`.
// Forward scan with store bound `s`: elements `< pivot` swap to the
// front. Every read goes through the const `at()` checked read,
// every write through the non-const `at()` checked path; all indices
// stay below `v.size()` (the loop guard), so the model is total.
#include <vector>

void vec_partition(std::vector<int> &v, int pivot) {
  unsigned long s = 0;
  unsigned long i = 0;
  while (i < v.size()) {
    if (v.at(i) < pivot) {
      int t = v.at(i);
      v.at(i) = v.at(s);
      v.at(s) = t;
      s = s + 1;
    }
    i = i + 1;
  }
}
