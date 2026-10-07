#include <cstdint>
#include <vector>
// N7d: `std::vector<int32_t>` single-element `erase` — `reserve(10)`
// takes the N7b reallocation path, the three pushes hit the fast path
// (capacity 10), and `erase(begin() + 1)` runs the in-capacity path
// (shift left + destroy); the reads pin the words (`1 + 3 = 4`).
int32_t vec_erase_sum() {
  std::vector<int32_t> v;
  v.reserve(10);
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  v.erase(v.begin() + 1);
  return v[0] + v[1];
}
