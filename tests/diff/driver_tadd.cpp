// Differential-test driver for the N4c template instantiations: args are
// `x y` (as signed 64-bit), prints `tadd32 tadd64 use32 use64` on one line
// by calling the real instantiations (so tampering the C++ under test is
// caught). Out-of-range results exit 3 (signed overflow is UB; the Lean
// fuzzer only feeds in-range values to native and asserts Lean-Lean
// agreement on overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

template <typename T> T tadd(T a, T b);
int32_t use_tadd32(int32_t x, int32_t y);
int64_t use_tadd64(int64_t x, int64_t y);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long long x = strtoll(argv[1], 0, 10);
  long long y = strtoll(argv[2], 0, 10);
  long long s32 = x + y;
  __int128 s64 = (__int128)x + (__int128)y;
  // Stay in range (nsw discipline); out-of-range is driver misuse.
  if (x < INT32_MIN || x > INT32_MAX || y < INT32_MIN || y > INT32_MAX ||
      s32 < INT32_MIN || s32 > INT32_MAX)
    return 3;
  if (s64 < (__int128)INT64_MIN || s64 > (__int128)INT64_MAX)
    return 3;
  int32_t t32 = tadd<int32_t>((int32_t)x, (int32_t)y);
  int64_t t64 = tadd<int64_t>((int64_t)x, (int64_t)y);
  int32_t u32 = use_tadd32((int32_t)x, (int32_t)y);
  int64_t u64 = use_tadd64((int64_t)x, (int64_t)y);
  printf("%d %lld %d %lld\n", (int)t32, (long long)t64, (int)u32,
         (long long)u64);
  return 0;
}
