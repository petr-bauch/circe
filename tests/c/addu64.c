// addu64: wrapping unsigned addition at width 64 (S3b). No pointers.
// Spec: addu64(a,b) = (a + b) mod 2^64, never fails.
#include <stdint.h>

uint64_t addu64(uint64_t a, uint64_t b) {
  return a + b;
}
