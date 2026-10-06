// Differential-test driver for the N7a `std::string_view`
// range-for sum: args are `n b0 ... b(n-1)` (bytes as signed
// 64-bit, range-checked to `[-128, 127]`), prints `view_sum` over
// a `string_view` of those bytes on one line by calling the real
// `view_sum` (so tampering the C++ under test is caught). Bytes
// travel as numbers (argv cannot carry NUL); the `std::string`
// is built byte-by-byte so embedded zeroes work. Overflow inputs
// never reach this binary: with `n ≤ 8` every checked-add fold is
// `.ok` (signed overflow is UB, so native has nothing to compare
// there; the overflow path is proof-covered only).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <string_view>

int32_t view_sum(std::string_view s);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc != 2 + n)
    return 2;
  std::string buf;
  for (long i = 0; i < n; i++) {
    long long x = strtoll(argv[2 + i], 0, 10);
    if (x < -128 || x > 127)
      return 3;
    buf.push_back((char)x);
  }
  std::string_view s(buf);
  printf("%d\n", (int)view_sum(s));
  return 0;
}
