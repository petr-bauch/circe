// bfs_order: breadth-first traversal over a flat row-major adjacency
// matrix (B-slice corpus). Discipline: `m` is `const&`, `vis`, the
// caller-provided queue `q`, and the caller-provided `order` are `&`
// (single-reference triples each, oracle governance vacuous, verdict
// honestly `unknown`); the seed marks `src` visited and enqueues it,
// then the outer `while` drains the queue: read `q[head]`, record the
// visit in `order[head]` (`head` already counts drained vertices, so no
// extra cursor), advance head, scan the row `v * n + u` (the G2 index
// computation), and enqueue every unvisited non-zero neighbor (the G1
// gated idiom — gate one `m.at(v*n+u) != 0`, gate two `vis.at(u) == 0`),
// counting each first visit. The queue never grows beyond `n` (each
// vertex is enqueued at most once — the visited gate; the caller sizes
// `q` and `order` accordingly, the G0 caller-reserves-upfront decision,
// keeping BFS independent of growth, exactly like G5a). Visiting the
// empty queue, reading past any vector, and `nsw` overflow are all loud
// (the bound checks live in the `at()` callees; the cursor arithmetic
// is wrapping `u64`). Visit order (the dequeue sequence) is what
// distinguishes BFS from DFS: on the diamond 0->1, 0->2, 1->3, 2->3,
// BFS visits 0,1,2,3 while the G5a DFS visits 0,2,3,1 (discovery order
// coincides at 0,1,2,3 — recorded at enqueue time it would not
// distinguish, hence the dequeue-time record).
// Spec: return = number of vertices reachable from `src` (including
// `src`); `order[k]` = k-th dequeued vertex for k < return. OOB is loud.
#include <vector>

unsigned long bfs_order(const std::vector<int> &m, std::vector<int> &vis, std::vector<int> &q, std::vector<int> &order, unsigned long n, unsigned long src) {
  vis.at(src) = 1;
  q.at(0) = (int)src;
  unsigned long head = 0;
  unsigned long tail = 1;
  unsigned long count = 1;
  while (head != tail) {
    unsigned long v = q.at(head);
    order.at(head) = (int)v;
    head = head + 1;
    for (unsigned long u = 0; u < n; u++) {
      if (m.at(v * n + u) != 0 && vis.at(u) == 0) {
        vis.at(u) = 1;
        q.at(tail) = (int)u;
        tail = tail + 1;
        count = count + 1;
      }
    }
  }
  return count;
}
