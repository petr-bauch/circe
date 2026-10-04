#include <cstdint>
#include <optional>
// N4d probe (ii): `std::optional` via `operator*` — dereference of a
// disengaged optional is UB (no throw path), so the lowering stays
// branch-free when the caller guards with `has_value()`.
int32_t opt_deref(const std::optional<int32_t> &o) {
  if (o.has_value())
    return *o;
  return -1;
}
