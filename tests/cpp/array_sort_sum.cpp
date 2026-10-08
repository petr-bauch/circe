#include <array>
#include <cstdint>
// N9: insertion sort over `std::array<uint32_t, 4>` — the user-proof
// case study (one specific algorithm). Unsigned elements keep the
// element comparison inside the existing `ult` core support;
// indices are `uint64_t` (positions erase to `u64` per the N4d-i
// precedent). The entry sorts `{3, 1, 2, 0}` and returns the sum
// (`6`, permutation-invariant); sortedness itself is pinned by the
// `Sorted`/`Permutation` spec over the forward plus Lean-Lean fuzz,
// not by the entry value.
void insertion_sort(std::array<uint32_t, 4>& a) {
  for (uint64_t i = 1; i < 4; ++i) {
    uint64_t j = i;
    while (j > 0 && a[j - 1] > a[j]) {
      uint32_t t = a[j];
      a[j] = a[j - 1];
      a[j - 1] = t;
      --j;
    }
  }
}

uint32_t array_sort_sum() {
  std::array<uint32_t, 4> a = {3, 1, 2, 0};
  insertion_sort(a);
  return a[0] + a[1] + a[2] + a[3];
}
