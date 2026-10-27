// dfs_grow: iterative DFS over a flat row-major adjacency matrix
// (G4 growth slice). Discipline: `m` is `const&`, `vis` and the
// caller-provided stack `st` are `&` (single-reference triple each,
// oracle governance vacuous, verdict honestly `unknown`); the seed
// marks `src` visited and pushes it, then the outer `while`
// drains the stack: pop the top, scan the row `v * n + u` (the G2
// index computation), and push every unvisited non-zero neighbor
// (the G1 gated idiom — gate one `m.at(v*n+u) != 0`, gate two
// `vis.at(u) == 0`), counting each first visit. Unlike G5a, the
// stack grows by `push_back` — the caller passes it empty (the G0
// caller-reserves-upfront decision lifted: no upfront sizing, the
// `_M_realloc_insert` slow path relocates as needed, the N4d-iv-b2
// growth composers). Popping the empty stack, reading past any
// vector, and `nsw` overflow are all loud (the bound checks live
// in the `at()` callees; the cursor arithmetic is wrapping `u64`).
// Spec: return = number of vertices reachable from `src`
// (including `src`); OOB is loud.
#include <vector>

unsigned long dfs_grow(const std::vector<int> &m, std::vector<int> &vis, std::vector<int> &st, unsigned long n, unsigned long src) {
  vis.at(src) = 1;
  st.push_back((int)src);
  // `top` is the live-stack count: elements `[0, top)` are live, and
  // `len >= top` always. The pop (`top - 1`, then `st.at(top)`) reads
  // the most recently pushed live element; a push reuses the popped
  // slot when one is free (`top < st.size()`, a guarded `at()` store)
  // and grows through `push_back` past the high-water mark, advancing
  // the live count by exactly one either way. (An earlier revision
  // used unconditional `push_back` with `top = top + 1`, which desyncs
  // after any pop-then-push — the popped slot's stale data is re-read
  // — and undercounts chained graphs, e.g. line-3 returned 2 instead
  // of 3. Slot reuse keeps the append-only growth while restoring
  // LIFO; the count is exact for a caller-passed-empty stack.)
  unsigned long top = 1;
  unsigned long count = 1;
  while (top != 0) {
    top = top - 1;
    unsigned long v = st.at(top);
    for (unsigned long u = 0; u < n; u++) {
      if (m.at(v * n + u) != 0 && vis.at(u) == 0) {
        vis.at(u) = 1;
        if (top < st.size()) st.at(top) = (int)u;
        else st.push_back((int)u);
        top = top + 1;
        count = count + 1;
      }
    }
  }
  return count;
}
