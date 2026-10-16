// Differential-test driver for the O2 `std::optional::value`
// guarded entry: args are `value engaged` (value as signed 64-bit,
// engaged as 0/1), prints `opt_val_guarded` on one line by calling
// the real `opt_val_guarded` (so tampering the C++ under test is
// caught). Engaged goes through the real checked `.value()` leaf;
// disengaged returns the `-1` sentinel without touching the leaf
// (calling `.value()` disengaged would throw `bad_optional_access`,
// so the fuzzer never sends that path to native — it asserts
// Lean-Lean `AssertFail` agreement there instead).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <optional>

int32_t opt_val_guarded(const std::optional<int32_t> &o);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long long v = strtoll(argv[1], 0, 10);
  if (v < INT32_MIN || v > INT32_MAX)
    return 3;
  int eng = atoi(argv[2]);
  std::optional<int32_t> o =
      eng ? std::optional<int32_t>((int32_t)v) : std::nullopt;
  printf("%d\n", (int)opt_val_guarded(o));
  return 0;
}
