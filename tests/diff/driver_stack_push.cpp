// Differential-test driver for the cursor-stack push kernel: args
// are `n v0 ... v(n-1) top x` (values as signed 64-bit,
// range-checked to `int32_t`; `top` as unsigned 64-bit), applies
// `stack_push(st, top, x)` to a locally built vector (the entry
// takes the workspace by mutable `&`; the caller owns construction
// — growth paths never run here) and prints the updated vector as
// `m w0 ... w(m-1)` plus the returned cursor `top + 1` on one line
// by calling the real entry (so tampering the C++ under test is
// caught). Any `at()` miss throws `std::out_of_range` natively: the
// driver catches it and exits 4 (the Lean side expects loud
// `.error` there — the `vec_at_one` empty-read precedent). The
// cursor advance wraps natively exactly as the model predicts (C++
// unsigned arithmetic — no UB anywhere, so the cursor leg always
// runs). The arg count is exact (`argc == 4 + n`). Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

unsigned long stack_push(std::vector<int> &st, unsigned long top, int x);

int main(int argc, char **argv) {
  if (argc < 4)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc != 4 + n)
    return 2;
  std::vector<int32_t> v;
  for (long k = 0; k < n; k++) {
    long long w = strtoll(argv[2 + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    v.push_back((int32_t)w);
  }
  unsigned long top = strtoul(argv[2 + n], 0, 10);
  long long xv = strtoll(argv[3 + n], 0, 10);
  if (xv < INT32_MIN || xv > INT32_MAX)
    return 3;
  unsigned long ntop = 0;
  try {
    ntop = stack_push(v, top, (int)xv);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%lu %lu", (unsigned long)v.size(), ntop);
  for (size_t k = 0; k < v.size(); k++)
    printf(" %d", v[k]);
  printf("\n");
  return 0;
}
