#include <cstdint>
#include <utility>
struct Acc {
  int32_t s;
  Acc() : s(0) {}
  Acc(Acc &&o) : s(o.s) { o.s = 0; }
  Acc &operator=(Acc &&o) {
    s = o.s;
    o.s = 0;
    return *this;
  }
  ~Acc() {}
  void add(int32_t v) { s += v; }
  int32_t get() const { return s; }
};
int32_t move_acc(int32_t a, int32_t b) {
  Acc src;
  src.add(a);
  Acc dst = std::move(src);
  dst.add(b);
  return dst.get();
}
