// vec_at_set: single bounds-checked element store through non-const `at()`.
// Discipline: `v` is a mutable borrow (single-reference triple, oracle
// governance vacuous, verdict honestly `unknown`); the write goes through
// the non-const `at()` checked path (`_M_range_check` guard +
// `operator[]` read for the address, both over frozen leaves). Out-of-range
// throws `std::out_of_range` natively; the model treats it as a loud
// `AssertFail` leg (the `vec_at_one` empty-read precedent).
#include <vector>

void vec_at_set(std::vector<int> &v, unsigned long i, int x) {
  v.at(i) = x;
}
