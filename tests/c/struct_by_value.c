// struct_by_value: pure struct handling, no pointers.
// Proves struct mapping (Lean structure) before pointer discipline.
// Spec: make/translate round-trips field-wise.
#include <stdint.h>

struct Point {
  int32_t x;
  int32_t y;
};

struct Point translate(struct Point p, int32_t dx, int32_t dy) {
  struct Point q;
  q.x = p.x + dx;
  q.y = p.y + dy;
  return q;
}
