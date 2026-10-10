// xor_u32: pure by-value u32 xor leaf (K1 crypto need: ARX xor).
#include <stdint.h>

uint32_t xor_u32(uint32_t a, uint32_t b) {
  return a ^ b;
}
