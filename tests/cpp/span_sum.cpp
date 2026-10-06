#include <cstdint>
#include <span>
// N4d-iii: `std::span<const int32_t>` borrow + length — index-based
// sum through `size()` / `operator[]` (no iterators: range-for over
// a span lowers to naked-iterator pointer-chasing, out of subset —
// see the `GoldenSpan` range-for pin. Range-for over
// `string_view` is admitted separately (N7a `view_sum`: the exact
// `begin`/`end` + chase-loop shape). The entry takes the
// span by value (`{ptr, extent}` in regs); the model reifies the
// viewed bytes (`sharedBorrow` pure-copy semantics, the S1
// `sum_array` precedent bundled into one value).
// Captured with `-std=c++20` (see `tools/emit-cir.sh`).
int32_t span_sum(std::span<const int32_t> s) {
  int32_t t = 0;
  for (uint64_t i = 0; i < s.size(); i++)
    t += s[i];
  return t;
}
