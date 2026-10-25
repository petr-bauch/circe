// mark_count: visited-mark idiom over two live vectors (G1 corpus).
// Discipline: `m` is `const&`, `vis` is `&` (single-reference triple
// each, oracle governance vacuous, verdict honestly `unknown`);
// the seed mark goes through the mut `at()` checked write, every
// read through the const `at()` checked read, accumulated with
// `nsw` adds (signed overflow is UB in C++ — loud in the model).
// Aeneas analogue: mark_count_fwd (m vis : List BV32).
// Spec: return = gated checked-add fold of the `vis` words (gated by
// `m.at(v) != 0`); `nsw` overflow aborts; OOB is loud. The vertex
// arrives as `u64` (callers narrow; indices are `u64` house-wide,
// the `vec_at_set` precedent).
#include <vector>

int mark_count(const std::vector<int> &m, std::vector<int> &vis, unsigned long u) {
  vis.at(u) = 1;
  int t = 0;
  for (unsigned long v = 0; v < vis.size(); v++)
    if (m.at(v) != 0)
      t += vis.at(v);
  return t;
}
