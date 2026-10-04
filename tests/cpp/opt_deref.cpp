#include <cstdint>
#include <optional>
// N4d-ii: `std::optional` guarded dereference — the entry checks
// `has_value()`, dereferences through `operator*` on engaged, and
// returns the `-1` sentinel on disengaged. Dereferencing a
// disengaged optional is UB (no throw path: `operator*`, not
// `.value()`), so the lowering stays `cir.try`-free; the
// `_M_get` assert (`cir.ternary` + `cir.unreachable`) is the loud
// disengaged guard the model reports as `AssertFail`.
int32_t opt_deref(const std::optional<int32_t> &o) {
  if (o.has_value())
    return *o;
  return -1;
}
