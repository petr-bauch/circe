// vec_transform_add: out-of-place checked transform over a readonly vector.
// Discipline: `in` is `const&` (single-reference triple, read-only);
// `out` is a mutable borrow pre-sized by the caller to at least
// `in.size()` (the entry never grows — indexed writes only). Every
// read goes through the const `at()` checked read, every write adds
// the constant `c` with the checked `i32` add (overflow is loud) and
// stores through the non-const `at()` checked path. Miss legs: input
// overrun is impossible (guard); short `out` throws
// `std::out_of_range` natively, loud `AssertFail` in the model (the
// `vec_at_set` precedent).
#include <vector>

void vec_transform_add(const std::vector<int> &in, std::vector<int> &out,
                       int c) {
  unsigned long i = 0;
  while (i < in.size()) {
    out.at(i) = in.at(i) + c;
    i = i + 1;
  }
}
