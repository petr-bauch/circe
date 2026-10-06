#include <cstdint>
#include <vector>
// N7b: `std::vector<int32_t>` `reserve` — pre-grow capacity, then
// push + indexed read. `reserve(10)` takes the reallocation path
// (capacity 0 < 10) through the admitted `_M_realloc_insert`
// machinery with NO element to insert; the two pushes then hit
// the fast path (capacity 10), and the reads pin the words. The
// only new defs over the N4d core are `reserve` itself plus the
// entry; everything else reuses admitted names.
int32_t vec_reserve_sum() {
  std::vector<int32_t> v;
  v.reserve(10);
  v.push_back(1);
  v.push_back(2);
  return v[0] + v[1];
}
