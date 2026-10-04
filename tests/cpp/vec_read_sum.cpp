#include <cstdint>
#include <vector>
// N4d-iv-a: indexed reads through a `const&` entry — `operator[]`
// through `v.size()` / `v[i]` (no iterators,
// no push, no growth: the entry takes the vector by const reference
// and the caller owns construction, so no ctor/dtor/push/realloc
// `cir.func` defs reach the gate; growth is N4d-iv-b).
// `size()` is exercised in the loop condition (dynamic length, the
// span-slice precedent generalized to the heap triple).
int32_t vec_read_sum(const std::vector<int32_t> &v) {
  int32_t t = 0;
  for (uint64_t i = 0; i < v.size(); i++)
    t += v[i];
  return t;
}
