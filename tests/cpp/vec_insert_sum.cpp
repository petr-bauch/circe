#include <cstdint>
#include <vector>
// N7c: `std::vector<int32_t>` single-element `insert` — `reserve(10)`
// takes the N7b reallocation path, the two pushes hit the fast path
// (capacity 10), and `insert(begin() + 1, 2)` runs the in-capacity
// fast path (shift right + construct); the reads pin the words
// (`1 + 2 + 3 = 6`). The slow arm (`_M_realloc_insert`) reuses the
// admitted N4d-iv-b2 machinery; the only new defs over the N4d+N7b
// core are the shift leaves, `insert` itself, and the entry.
int32_t vec_insert_sum() {
  std::vector<int32_t> v;
  v.reserve(10);
  v.push_back(1);
  v.push_back(3);
  v.insert(v.begin() + 1, 2);
  return v[0] + v[1] + v[2];
}
