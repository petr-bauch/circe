#include <cstdint>
#include <vector>
// N4d probe: `std::vector` — push + indexed read (reallocation moves
// values; admitted only if the lowering stays value-faithful).
int32_t vec_push_sum() {
  std::vector<int32_t> v;
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  return v[0] + v[1] + v[2];
}
