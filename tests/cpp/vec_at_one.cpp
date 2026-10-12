// vec_at_one: single checked read over a readonly vector.
// Discipline: `v` is `const&` (single-reference triple, C++ untouched
// by N2c — oracle governance is vacuous, verdict honestly `unknown`),
// the only access is `v.at(0)` (const `at()`: `_M_range_check` guard
// + `operator[]` read, both over frozen leaves). Readers never write.
// Aeneas analogue: vec_at_one_fwd (v : List BV32).
// Spec: return = first word; empty vector aborts (noreturn throw,
// fused to `fail`, i.e. loud `AssertFail` — never silent).
#include <vector>

int vec_at_one(const std::vector<int> &v) { return v.at(0); }
