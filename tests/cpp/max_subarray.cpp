// max_subarray: Kadane maximum-subarray over a readonly vector via `at()`.
// Discipline: `v` is `const&` (single-reference triple, oracle
// governance vacuous, verdict honestly `unknown`); every element
// goes through the const `at()` checked read (`_M_range_check`
// guard + `operator[]` read, both over frozen leaves). The running
// (`cur`) and best-so-far (`best`) accumulators seed from `at(0)`
// (all-negative inputs are the point — no zero seed); the update
// is written with explicit comparisons (no `std::max` call — calls
// cannot appear inside loop bodies), accumulated with `nsw` adds
// (signed overflow is UB in C++ — loud in the model). Readers
// never write.
// Aeneas analogue: max_subarray_fwd (v : List BV32).
// Spec: return = maximum subarray sum; `nsw` overflow aborts the
// fold; empty input throws on the `at(0)` seed (fused `fail` leg,
// the `at()` precedent); the `AssertFail` OOB leg is unreachable
// (the loop bound `i < size` subsumes the guard) but propagates
// loudly.
#include <vector>

int max_subarray(const std::vector<int> &v) {
  int cur = v.at(0);
  int best = v.at(0);
  for (unsigned long i = 1; i < v.size(); i++) {
    int x = v.at(i);
    int sum = cur + x;
    if (x > sum)
      sum = x;
    cur = sum;
    if (cur > best)
      best = cur;
  }
  return best;
}
