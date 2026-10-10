// shl_u32: pure by-value u32 left-shift leaf (K1 crypto need: rot parts).
#include <stdint.h>

uint32_t shl_u32(uint32_t a, uint32_t b) {
  return a << b;
}
