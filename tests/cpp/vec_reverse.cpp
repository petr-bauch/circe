#include <cstdint>
#include <vector>
// R1: in-place reverse via countdown two-pointer swaps. The loop
// counts `j` down from `size` while `i` counts up (`while (i < j)`)
// to avoid the unsigned `n / 2` division (only signed `sdiv` on
// `i32` is admitted, N6a). All four element accesses go through
// the checked non-const `at()` (`_M_range_check` guard +
// `operator[]` address, the `vec_at_set` discipline — out-of-range
// is a loud `AssertFail` leg, unreachable here since both indices
// stay below `size`). Each iteration swaps `v[i]` and `v[j]`
// through a spill temporary. Invariant: segments `[0, i)` and
// `(j, n)` are mirrored, the window `[i, j]` is untouched; `--j`
// cannot underflow since the guard gives `j >= i + 1 >= 1`.
void vec_reverse(std::vector<int32_t> &v) {
  uint64_t i = 0;
  uint64_t j = v.size();
  while (i < j) {
    --j;
    int32_t t = v.at(i);
    v.at(i) = v.at(j);
    v.at(j) = t;
    ++i;
  }
}
