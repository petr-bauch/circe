// stack_push: cursor-stack push kernel (G3 corpus). Discipline:
// `st` is the caller-provided workspace (`&`, single-reference
// triple, oracle governance vacuous, verdict honestly `unknown`);
// the push stores through the mut `at()` checked write at the
// cursor `top` and returns the advanced cursor `top + 1` (wrapping
// `u64` add — the S3b precedent; reserve-upfront keeps the cursor
// in bounds, the G0 decision — growth itself is G4). Pop is the
// caller-side dual (`top - 1`, the N4d-iv-b1 `usub` precedent, then
// a const `at()` read, the G2 precedent); the empty test is
// `top == 0` (composable in the G5a entry). So this kernel admits
// the one genuinely new piece — the guarded workspace store
// returning the advanced cursor — while pop/read/empty reuse
// admitted machinery. This keeps the G5a iterative DFS on
// admitted ground with no iterator values in CoreIR (the
// `__gnu_cxx` iterator closure behind `empty()` / `back()` /
// `pop_back()` stays deferred).
// Spec: store `x` at `st.at(top)`, return `top + 1`; seed-miss is
// the `at()`-throw `AssertFail`. The loan story is the G1 `vecSet`
// precedent (in-env update, no heap identity).
#include <vector>

unsigned long stack_push(std::vector<int> &st, unsigned long top, int x) {
  st.at(top) = x;
  return top + 1;
}
