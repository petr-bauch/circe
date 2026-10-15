// vec_two_sum: brute-force two-sum over a readonly vector via `at()`.
// Discipline: `v` is `const&` (single-reference triple, oracle
// governance vacuous, verdict honestly `unknown`); every element
// goes through the const `at()` checked read (`_M_range_check`
// guard + `operator[]` read, both over frozen leaves). The outer
// loop runs `i` over `[0, n)`, the inner loop runs `j` over
// `(i, n)`; on `v[i] + v[j] == target` the index pair returns
// early (indices narrow to `int`, exact for all realistic
// lengths). Miss returns `{(int)n, (int)n}` (find_eq house style
// generalized to pairs); the `i32` add may wrap — the model treats
// it as loud overflow (the `nsw` precedent), so overflow inputs
// assert Lean-Lean agreement only. Sortedness is irrelevant (brute
// force examines every pair).
#include <vector>

struct IPair {
  int a;
  int b;
};

IPair vec_two_sum(const std::vector<int> &v, int target) {
  unsigned long n = v.size();
  unsigned long i = 0;
  while (i < n) {
    unsigned long j = i + 1;
    while (j < n) {
      if (v.at(i) + v.at(j) == target) return {(int)i, (int)j};
      j = j + 1;
    }
    i = i + 1;
  }
  return {(int)n, (int)n};
}
