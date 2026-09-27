// add_caller: DAG call into by-value add (S1).
// Discipline: pure by-value ints, single call to add, return its result.
// Spec: add_caller(x,y,z) = (x + y) + z with nsw-checked add.
#include <stdint.h>

int32_t add(int32_t a, int32_t b);

int32_t add_caller(int32_t x, int32_t y, int32_t z) {
  int32_t t = add(x, y);
  return add(t, z);
}
