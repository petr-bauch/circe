#include <cstdint>
// N4c: function template on value types — each instantiation is its own
// monomorphized def (Itanium: `_Z4taddIiET_S0_S0_` for `int32_t`,
// `_Z4taddIlET_S0_S0_` for `int64_t` (aka `long`). No generic reasoning:
// the gate
// admits each instantiation as its value-type shape (the Vec32/Vec64
// monomorphization precedent).
template <typename T> T tadd(T a, T b) { return a + b; }
// Explicit instantiation definitions: the monomorphs exist as strong
// symbols (so the native diff driver can call them directly), not just
// as inlineable implicit instantiations inside the entries below.
template int32_t tadd<int32_t>(int32_t, int32_t);
template int64_t tadd<int64_t>(int64_t, int64_t);
// Call sites pin each instantiation: 32-bit and 64-bit entries.
int32_t use_tadd32(int32_t x, int32_t y) { return tadd<int32_t>(x, y); }
int64_t use_tadd64(int64_t x, int64_t y) { return tadd<int64_t>(x, y); }
