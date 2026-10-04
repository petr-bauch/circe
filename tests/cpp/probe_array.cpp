#include <array>
#include <cstdint>
// N4d probe: `std::array` fixed-size value semantics — sum 4 elements,
// bounds-checked access via `.at()` pins the abort path shape.
int32_t array_sum(const std::array<int32_t, 4> &a) {
  return a[0] + a[1] + a[2] + a[3];
}
