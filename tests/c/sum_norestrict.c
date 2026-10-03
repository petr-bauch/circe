// sum_norestrict: bounded array traversal WITHOUT `__restrict__` (N2c).
// Discipline: identical to `sum_array` (length-paired `a`/`n`, only
// `a[i]` for `0 <= i < n`), but CIRGen emits no `llvm.noalias` evidence
// for `a` — the source-level `const` reader discipline plus the
// singleton footprint + read-only CoreIR (no array-write primitive)
// recover noalias from construction instead of demanding attr text.
// Spec: return = sum of first n elements (same `sumFwd` as `sum_array`).
#include <stddef.h>
#include <stdint.h>

uint32_t sum_norestrict(const uint32_t *a, size_t n) {
  uint32_t s = 0;
  for (size_t i = 0; i < n; i++) {
    s += a[i];
  }
  return s;
}
