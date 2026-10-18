#include <cstdint>
#include <vector>
// R0: in-place left rotation by `k` via three segment reversals over
// the admitted `vec_seg_reverse` entry (triple entry-over-entry
// composition, no loop): reverse `[0, k)`, then `[k, n)`, then
// `[0, n)`. Caller debt: `k <= size` (out-of-range is a loud
// `AssertFail` leg inside the callee, unreachable under the
// contract).
void vec_seg_reverse(std::vector<int32_t> &v, uint64_t lo, uint64_t hi);
void vec_rotate(std::vector<int32_t> &v, uint64_t k) {
  uint64_t n = v.size();
  vec_seg_reverse(v, 0, k);
  vec_seg_reverse(v, k, n);
  vec_seg_reverse(v, 0, n);
}
