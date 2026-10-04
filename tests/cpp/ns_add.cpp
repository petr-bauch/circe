#include <cstdint>
// N4a: namespaced leaf — the `add` body under a mangled namespace name
// (`_ZN2ns3addEii`).
namespace ns {
int32_t add(int32_t a, int32_t b) { return a + b; }
}
// Call site pins qualified resolution: `ns::add(x, y)` targets `_ZN2ns3addEii`.
int32_t use_ns_add(int32_t x, int32_t y) { return ns::add(x, y); }
