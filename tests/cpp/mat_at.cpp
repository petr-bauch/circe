// mat_at: flat-2D index read over a row-major matrix (G2 corpus).
// Discipline: `m` is `const&` (single-reference triple, oracle
// governance vacuous, verdict honestly `unknown`); the single read
// goes through the const `at()` checked read. The 2D index is the
// unsigned computation `i * ncols + j` (`cir.mul` + `cir.add` on
// `u64`, both wrapping — C++ unsigned arithmetic; no `nsw`
// marker, so no UB to model, the S3b wrapping precedent). The
// bounds check is the `at()`-fused `_M_range_check` on the linear
// index — out-of-range `(i, j)` pairs, including wrapping index
// computations, are loud. This is the read idiom the G5a flat-matrix
// DFS will loop over (caller-provided stack, G0 decision).
// Spec: return = `m.at(i * ncols + j)`; OOB is loud.
#include <vector>

int mat_at(const std::vector<int> &m, unsigned long ncols, unsigned long i, unsigned long j) {
  return m.at(i * ncols + j);
}
