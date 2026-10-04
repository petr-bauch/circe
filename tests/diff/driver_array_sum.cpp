// Differential-test driver for the N4d-i `std::array` reads: args are
// `a b c d` (as signed 64-bit), prints `array_sum` on one line by
// calling the real `array_sum` (so tampering the C++ under test is
// caught). Every intermediate sum must be in range (left-associated
// `nsw` adds); out-of-range results exit 3 (signed overflow is UB; the
// Lean fuzzer only feeds in-range values to native and asserts
// Lean-Lean agreement on overflow).
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

int32_t array_sum(const std::array<int32_t, 4> &a);

int main(int argc, char **argv) {
  if (argc != 5)
    return 2;
  long long v[4];
  for (int i = 0; i < 4; i++) {
    v[i] = strtoll(argv[1 + i], 0, 10);
    if (v[i] < INT32_MIN || v[i] > INT32_MAX)
      return 3;
  }
  // Stay in range (`nsw` discipline at each of the three add sites);
  // out-of-range is driver misuse.
  __int128 t = (__int128)v[0] + (__int128)v[1];
  __int128 u = t + (__int128)v[2];
  __int128 s = u + (__int128)v[3];
  if (t < INT32_MIN || t > INT32_MAX || u < INT32_MIN || u > INT32_MAX ||
      s < INT32_MIN || s > INT32_MAX)
    return 3;
  std::array<int32_t, 4> a = {(int32_t)v[0], (int32_t)v[1], (int32_t)v[2],
                              (int32_t)v[3]};
  printf("%d\n", (int)array_sum(a));
  return 0;
}
