// Differential-test driver for breadth-first traversal over a flat
// row-major adjacency matrix: args are `nm m0 ... nv v0 ... nq q0 ...
// no o0 ... n src` (matrix/visited/queue/order values as signed
// 64-bit, range-checked to `int32_t`; `n`/`src` as unsigned 64-bit),
// applies `bfs_order(m, vis, q, order, n, src)` to locally built
// vectors (the entry takes the matrix by `const&` and visited, queue,
// and order by mutable `&`; the caller owns construction — growth
// paths never run here) and prints the resulting count on the first
// line and the order words on the second line by calling the real
// entry (so tampering the C++ under test is caught). Any `at()`
// miss throws `std::out_of_range` natively: the driver catches it
// and exits 4 (the Lean side expects loud `.error` there — the
// `vec_at_one` empty-read precedent). The arg count is exact
// (`argc == 7 + nm + nv + nq + no`: `argv[0]` plus the six header
// words). Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

unsigned long bfs_order(const std::vector<int> &m, std::vector<int> &vis,
                        std::vector<int> &q, std::vector<int> &order,
                        unsigned long n, unsigned long src);

int main(int argc, char **argv) {
  if (argc < 6)
    return 2;
  long nm = strtol(argv[1], 0, 10);
  if (nm < 0 || nm > 32)
    return 2;
  std::vector<int32_t> m;
  for (long k = 0; k < nm; k++) {
    long long w = strtoll(argv[2 + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    m.push_back((int32_t)w);
  }
  long nv = strtol(argv[2 + nm], 0, 10);
  if (nv < 0 || nv > 32)
    return 2;
  std::vector<int32_t> vis;
  for (long k = 0; k < nv; k++) {
    long long w = strtoll(argv[3 + nm + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    vis.push_back((int32_t)w);
  }
  long nq = strtol(argv[3 + nm + nv], 0, 10);
  if (nq < 0 || nq > 32)
    return 2;
  std::vector<int32_t> q;
  for (long k = 0; k < nq; k++) {
    long long w = strtoll(argv[4 + nm + nv + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    q.push_back((int32_t)w);
  }
  long no = strtol(argv[4 + nm + nv + nq], 0, 10);
  if (no < 0 || no > 32 || argc != 7 + nm + nv + nq + no)
    return 2;
  std::vector<int32_t> order;
  for (long k = 0; k < no; k++) {
    long long w = strtoll(argv[5 + nm + nv + nq + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    order.push_back((int32_t)w);
  }
  unsigned long n = strtoul(argv[5 + nm + nv + nq + no], 0, 10);
  unsigned long src = strtoul(argv[6 + nm + nv + nq + no], 0, 10);
  unsigned long got = 0;
  try {
    got = bfs_order(m, vis, q, order, n, src);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%lu\n", got);
  for (long k = 0; k < no; k++) {
    if (k)
      printf(" ");
    printf("%d", order[k]);
  }
  printf("\n");
  return 0;
}
