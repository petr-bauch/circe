#include <cstdint>
#include <optional>
// N4d probe: `std::optional` nullable value — engaged check + value,
// disengaged sentinel.
int32_t opt_get(const std::optional<int32_t> &o) {
  if (o.has_value())
    return o.value();
  return -1;
}
