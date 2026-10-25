// mark_count_c: char-width visited-mark idiom over two live vectors
// (G1b corpus). Discipline: `m` is `const&`, `vis` is `&`
// (single-reference triple each, oracle governance vacuous, verdict
// honestly `unknown`); the seed mark goes through the mut `at()`
// checked write, every read through the const `at()` checked read,
// accumulated with `nsw` adds (signed overflow is UB in C++ — loud
// in the model). The element width is `char` (`s8i` loads, integer
// promotion to `int` at the gate compare and the accumulation —
// the char-width conditional): same gated fold shape as `mark_count`
// (G1), one width down.
// Spec: return = gated checked-add fold of the promoted `vis` words
// (gated by `m.at(v) != 0`); `nsw` overflow aborts; OOB is loud. The
// vertex arrives as `u64` (callers narrow; indices are `u64`
// house-wide, the `vec_at_set` precedent).
#include <vector>

int mark_count_c(const std::vector<char> &m, std::vector<char> &vis, unsigned long u) {
  vis.at(u) = 1;
  int t = 0;
  for (unsigned long v = 0; v < vis.size(); v++)
    if (m.at(v) != 0)
      t += vis.at(v);
  return t;
}
