#include <cstdint>
struct Point {
  int32_t x;
  int32_t y;
  int32_t sum() const { return x + y; }
};
int32_t point_sum_ref(const Point &p) { return p.sum(); }
