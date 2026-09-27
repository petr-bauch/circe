// add64: pure by-value baseline at width 64 (S3b: first width
// generalization past i32/u32). No pointers.
// Spec: add64(a,b) = a + b with signed-overflow UB (nsw); the Lean
// side reports out-of-range sums as Overflow.
#include <stdint.h>

int64_t add64(int64_t a, int64_t b) {
  return a + b;
}
