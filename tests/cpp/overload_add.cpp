#include <cstdint>
// N4a: overload set — same body shape under distinct mangled names
// (`_Z3addii` is the `add` body; `_Z3addiii` threads two `nsw` adds).
int32_t add(int32_t a, int32_t b) { return a + b; }
int32_t add(int32_t a, int32_t b, int32_t c) { return a + b + c; }
// Call site pins overload resolution: `add(x, y)` targets `_Z3addii`.
int32_t use_add(int32_t x, int32_t y) { return add(x, y); }
