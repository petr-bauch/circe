// Differential-test driver for iterative DFS over a flat row-major
// adjacency matrix with a caller-grown stack: args are `nm m0 ...
// nv v0 ... ns s0 ... n src` (matrix/visited/stack values as signed
// 64-bit, range-checked to `int32_t`; `n`/`src` as unsigned 64-bit),
// applies `dfs_grow(m, vis, st, n, src)` to locally built vectors
// (the entry takes the matrix by `const&` and visited + stack by
// mutable `&`; the differential suite passes the stack empty —
// growth paths run here, unlike the reserve-upfront G5a driver) and
// prints the resulting count on one line by calling the real
// entry (so tampering the C++ under test is caught). Any `at()`
// miss throws `std::out_of_range` natively: the driver catches it
// and exits 4 (the Lean side expects loud `.error` there — the
// `vec_at_one` empty-read precedent). The arg count is exact
// (`argc == 6 + nm + nv + ns`: `argv[0]` plus the five header
// words). Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

unsigned long dfs_grow(const std::vector<int> &m, std::vector<int> &vis,
                       std::vector<int> &st, unsigned long n,
                       unsigned long src);

int main(int argc, char **argv) {
  if (argc < 5)
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
  long ns = strtol(argv[3 + nm + nv], 0, 10);
  if (ns < 0 || ns > 32 || argc != 6 + nm + nv + ns)
    return 2;
  std::vector<int32_t> st;
  for (long k = 0; k < ns; k++) {
    long long w = strtoll(argv[4 + nm + nv + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    st.push_back((int32_t)w);
  }
  unsigned long n = strtoul(argv[4 + nm + nv + ns], 0, 10);
  unsigned long src = strtoul(argv[5 + nm + nv + ns], 0, 10);
  unsigned long got = 0;
  try {
    got = dfs_grow(m, vis, st, n, src);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%lu\n", got);
  return 0;
}
