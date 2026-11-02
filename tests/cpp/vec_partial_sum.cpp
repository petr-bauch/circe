// vec_partial_sum: in-place prefix-sum scan over a mutable vector.
// Discipline: `v` is a mutable borrow. Each output (for `i >= 1`)
// reads the previous output: `v.at(i)` reads the current element
// before it is overwritten, while `v.at(i - 1)` reads the already
// computed prefix sum. Every access goes through the checked
// `at()` path; `1 <= i < v.size()` keeps both indices in bounds.
// Checked `i32` addition is loud (`Overflow` aborts the scan and
// matches the V2/transform checked-add precedent). Empty and
// singleton vectors are identity because the loop starts at 1.
#include <vector>

void vec_partial_sum(std::vector<int> &v) {
  unsigned long i = 1;
  while (i < v.size()) {
    v.at(i) = v.at(i) + v.at(i - 1);
    i = i + 1;
  }
}
