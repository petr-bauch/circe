// add: pure by-value baseline. No pointers.
// Spec: add(a,b) = a + b (wrapping u32 not exercised; signed overflow UB).
#include <stdint.h>

int32_t add(int32_t a, int32_t b) {
  return a + b;
}
