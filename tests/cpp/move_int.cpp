#include <cstdint>
#include <utility>
int32_t move_int(int32_t a, int32_t b) {
  int32_t x = a;
  int32_t y = std::move(x);
  return y + b;
}
