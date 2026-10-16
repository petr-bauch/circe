// Differential-test driver for the second sequential-writer admission:
// the arg is `x` (signed 64-bit, range-checked to `int32_t`), prints
// the post-call word by calling the real entry (so tampering the C++
// under test is caught). Overflow inputs never reach this binary:
// the Lean fuzzer only calls it when the checked-add pair is `.ok`
// (signed overflow is UB, so native has nothing to compare there —
// the `nsw` error legs assert Lean-Lean agreement only).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

void alias_reborrow34(int &x);

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  long long v = strtoll(argv[1], 0, 10);
  if (v < INT32_MIN || v > INT32_MAX)
    return 3;
  int32_t x = (int32_t)v;
  alias_reborrow34(x);
  printf("%d\n", (int)x);
  return 0;
}
