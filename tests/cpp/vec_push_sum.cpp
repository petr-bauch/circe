#include <cstdint>
#include <vector>
// N4d-iv-b: `std::vector<int32_t>` growth — push + indexed read
// (reallocation moves values; admitted only if the lowering stays
// value-faithful). Three pushes force the fast path and the
// `_M_realloc_insert` slow path; the reads pin the moved words and
// the dtor closes the lifetime. N4d-iv-b1 admits the growth leaves
// (ctor, `back`/`begin`/`end`, iterator `minus`/`base`,
// `get_Tp_allocator`, `construct`, `destroy`, `_Destroy`,
// `_M_allocate`/`_M_deallocate`, the `_M_check_len` arithmetic
// chain); the composers (`_M_realloc_insert`, `emplace_back`,
// `push_back`, the entry) are N4d-iv-b2.
int32_t vec_push_sum() {
  std::vector<int32_t> v;
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  return v[0] + v[1] + v[2];
}
