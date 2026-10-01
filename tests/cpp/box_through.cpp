#include <cstdint>
struct Box {
  int32_t x;
};
int32_t box_through(int32_t x) {
  Box* p = new Box{x};
  int32_t r = p->x;
  delete p;
  return r;
}
