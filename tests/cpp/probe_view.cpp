#include <cstdint>
#include <string_view>
// N4d probe (iii): `string_view` borrow + length — range-for over the
// viewed characters (the `sharedBorrow` story if lowering is clean).
// (`std::span` needs `-std=c++20`, off the pinned capture flags:
/// deferred, see ROADMAP N4d.)
int32_t view_sum(std::string_view s) {
  int32_t t = 0;
  for (char c : s)
    t += c;
  return t;
}
