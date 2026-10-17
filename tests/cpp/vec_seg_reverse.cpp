#include <cstdint>
#include <vector>
// S0: in-place segment reverse via countdown two-pointer swaps over
// the half-open range `[lo, hi)`. Same countdown skeleton as
// `vec_reverse` (`while (i < j)`, `--j` first, checked non-const
// `at()` for all four accesses, spill temporary), but the window
// opens at `i = lo`, `j = hi` instead of `0`/`size`. Caller debt:
// `lo <= hi <= size` (out-of-range is a loud `AssertFail` leg,
// unreachable under the contract). Invariant: segments
// `[lo, i)` and `[j, hi)` are mirrored about `lo + hi - 1`, the
// window `[i, j]` is untouched.
void vec_seg_reverse(std::vector<int32_t> &v, uint64_t lo, uint64_t hi) {
  uint64_t i = lo;
  uint64_t j = hi;
  while (i < j) {
    --j;
    int32_t t = v.at(i);
    v.at(i) = v.at(j);
    v.at(j) = t;
    ++i;
  }
}
