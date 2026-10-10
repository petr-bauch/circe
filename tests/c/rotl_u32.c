// rotl_u32: rotate-left composite (K1 inspection only, NOT admitted).
// Documents why rotl is not a single-op leaf: the body is three ops
// (shl + sub + shr + or), so it trips the multi-op rejection and the
// quarter round composes the shifts explicitly instead.
#include <stdint.h>

uint32_t rotl_u32(uint32_t x, uint32_t n) {
  return (x << n) | (x >> (32 - n));
}
