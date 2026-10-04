#include <array>
#include <cstdint>
// N4d-i: `std::array` fixed-size value semantics — the entry reads all
// four elements through `operator[]` (unchecked, const indices) and
// threads three `nsw` adds. Each monomorph is its own shape:
// `_S_ref` (the `get_element` leaf), `operator[]` (single delegation),
// `array_sum` (the 4-call entry).
int32_t array_sum(const std::array<int32_t, 4> &a) {
  return a[0] + a[1] + a[2] + a[3];
}
