// vec_at_sum: checked sum over a readonly vector via `at()`.
// Discipline: `v` is `const&` (single-reference triple, oracle
// governance vacuous, verdict honestly `unknown`); every element
// goes through the const `at()` checked read (`_M_range_check`
// guard + `operator[]` read, both over frozen leaves), accumulated
// with `nsw` adds (signed overflow is UB in C++ — loud in the
// model). Readers never write.
// Aeneas analogue: vec_at_sum_fwd (v : List BV32).
// Spec: return = checked-add fold of the words; `nsw` overflow
// aborts the fold; the `AssertFail` OOB leg is unreachable (the loop
// bound `i < size` subsumes the guard) but propagates loudly.
#include <vector>

int vec_at_sum(const std::vector<int> &v) {
  int s = 0;
  for (unsigned long i = 0; i < v.size(); i++)
    s += v.at(i);
  return s;
}
