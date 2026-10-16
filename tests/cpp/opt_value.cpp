#include <cstdint>
#include <optional>
// O1/O2: `std::optional::value` guarded + unguarded entries. Unlike
// `operator*` (N4d-ii, UB on disengaged), `.value()` checks engagement
// itself: the `value() const&` callee holds an engaged-check `cir.if`
// whose taken arm is the `_M_get` return, with the disengaged
// fallthrough calling `__throw_bad_optional_access` (`noreturn`,
// lowers to `abort()` under `-fno-exceptions`) followed by `cir.trap`.
// No EH ops anywhere (`cir.try`-free); the trap is unreachable by
// construction. The guarded entry admits (engaged `.value()` ≡
// `operator*` path, disengaged → sentinel); the unguarded entry keeps
// the live throw path and stays rejected with the dedicated message.
int32_t opt_val_guarded(const std::optional<int32_t> &o) {
  if (o.has_value())
    return o.value();
  return -1;
}
int32_t opt_val_unguarded(const std::optional<int32_t> &o) {
  return o.value();
}
