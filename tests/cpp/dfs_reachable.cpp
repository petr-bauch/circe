// dfs_reachable: iterative DFS over a flat row-major adjacency
// matrix (G5a corpus). Discipline: `m` is `const&`, `vis` and the
// caller-provided stack `st` are `&` (single-reference triple each,
// oracle governance vacuous, verdict honestly `unknown`); the seed
// marks `src` visited and pushes it, then the outer `while`
// drains the stack: pop the top, scan the row `v * n + u` (the G2
// index computation), and push every unvisited non-zero neighbor
// (the G1 gated idiom — gate one `m.at(v*n+u) != 0`, gate two
// `vis.at(u) == 0`), counting each first visit. The stack never
// grows beyond `n` (each vertex is pushed at most once — the
// visited gate; the caller sizes `st` accordingly, the G0
// caller-reserves-upfront decision, keeping G5a independent of
// growth, which is G4). Popping the empty stack, reading past any
// vector, and `nsw` overflow are all loud (the bound checks live
// in the `at()` callees; the cursor arithmetic is wrapping `u64`).
// Spec: return = number of vertices reachable from `src`
// (including `src`); OOB is loud.
#include <vector>

unsigned long dfs_reachable(const std::vector<int> &m, std::vector<int> &vis, std::vector<int> &st, unsigned long n, unsigned long src) {
  vis.at(src) = 1;
  st.at(0) = (int)src;
  unsigned long top = 1;
  unsigned long count = 1;
  while (top != 0) {
    top = top - 1;
    unsigned long v = st.at(top);
    for (unsigned long u = 0; u < n; u++) {
      if (m.at(v * n + u) != 0 && vis.at(u) == 0) {
        vis.at(u) = 1;
        st.at(top) = (int)u;
        top = top + 1;
        count = count + 1;
      }
    }
  }
  return count;
}
