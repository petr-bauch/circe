#include <array>
#include <cstdint>
// N9b: insertion sort over `std::array<uint32_t, 8>` — second monomorph
// through the pipeline (each monomorph is its own shape, the N4c
// precedent; see docs/SUBSET.md item 33). Same algorithm as
// `array_sort_sum.cpp`, extended init (N4 prefix + reversed tail).
// Unsigned elements keep the element comparison inside the existing
// `ult` core support; indices are `uint64_t` (positions erase to `u64`
// per the N4d-i precedent). The entry sorts `{3, 1, 2, 0, 7, 5, 6, 4}`
// and returns the sum (`28`, permutation-invariant); sortedness itself
// is pinned by the `Sorted`/`Permutation` spec over the forward plus
// Lean-Lean fuzz, not by the entry value.
void insertion_sort8(std::array<uint32_t, 8>& a) {
  for (uint64_t i = 1; i < 8; ++i) {
    uint64_t j = i;
    while (j > 0 && a[j - 1] > a[j]) {
      uint32_t t = a[j];
      a[j] = a[j - 1];
      a[j - 1] = t;
      --j;
    }
  }
}

uint32_t array_sort_sum8() {
  std::array<uint32_t, 8> a = {3, 1, 2, 0, 7, 5, 6, 4};
  insertion_sort8(a);
  return a[0] + a[1] + a[2] + a[3] + a[4] + a[5] + a[6] + a[7];
}
