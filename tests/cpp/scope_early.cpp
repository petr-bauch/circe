#include <cstdint>
struct Acc {
  int32_t s;
  Acc() : s(0) {}
  ~Acc() {}
  void add(int32_t v) { s += v; }
  int32_t get() const { return s; }
};
int32_t scope_early(int32_t a, int32_t b) {
  Acc acc;
  acc.add(a);
  if (a == b) {
    return acc.get();
  }
  acc.add(b);
  return acc.get();
}
