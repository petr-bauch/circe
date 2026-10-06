#include <cstdint>
#include <string_view>
// N7a: `std::string_view` borrow + length — range-for over the viewed
// characters. Unlike the N4d-iii span slice (index-based
// `size()`/`operator[]`), range-for lowers to `begin()`/`end` plus a
// pointer-chase loop (`cir.ptr_stride` + `deref`/`eq` while-cond) over
// `!s8i` cells with an `s8i -> s32i` sext before the `nsw` add.
// Captured with `-std=c++17` (see `tools/emit-cir.sh`).
int32_t view_sum(std::string_view s) {
  int32_t t = 0;
  for (char c : s)
    t += c;
  return t;
}
