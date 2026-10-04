// Differential-test driver for the N4d-iii `std::span` index sum:
// args are `n v0 ... v(n-1)` (values as signed 64-bit, range-checked
// to `int32_t`), prints `span_sum` over the span of the vector on one
// line by calling the real `span_sum` (so tampering the C++ under
// test is caught). The span is built from a `vector` (never from a
// raw pointer: an empty vector still yields a valid empty span).
// Overflow inputs never reach this binary: the Lean fuzzer only calls
// it when the checked-add fold is `.ok` (all adds in range — signed
// overflow is UB, so native has nothing to compare there; OOB indices
// likewise never reach native).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <span>
#include <vector>

int32_t span_sum(std::span<const int32_t> s);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc != 2 + n)
    return 2;
  std::vector<int32_t> v;
  for (long i = 0; i < n; i++) {
    long long x = strtoll(argv[2 + i], 0, 10);
    if (x < INT32_MIN || x > INT32_MAX)
      return 3;
    v.push_back((int32_t)x);
  }
  std::span<const int32_t> s(v);
  printf("%d\n", (int)span_sum(s));
  return 0;
}
