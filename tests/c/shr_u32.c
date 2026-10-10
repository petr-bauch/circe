// shr_u32: pure by-value u32 logical right-shift leaf (K1).
#include <stdint.h>

uint32_t shr_u32(uint32_t a, uint32_t b) {
  return a >> b;
}
