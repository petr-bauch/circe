// Differential-test driver for the N4d-ii `std::optional` guarded
// deref: args are `value engaged` (value as signed 64-bit, engaged
// as 0/1), prints `opt_deref` on one line by calling the real
// `opt_deref` (so tampering the C++ under test is caught). Engaged
// returns the word; disengaged returns the `-1` sentinel (the
// disengaged payload is never read: the guard lives inside
// `opt_deref`, and dereferencing a disengaged optional directly
// would be UB, so the Lean fuzzer never feeds disengaged to the
// deref path — it asserts Lean-Lean agreement there instead).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <optional>

int32_t opt_deref(const std::optional<int32_t> &o);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long long v = strtoll(argv[1], 0, 10);
  if (v < INT32_MIN || v > INT32_MAX)
    return 3;
  int eng = atoi(argv[2]);
  std::optional<int32_t> o =
      eng ? std::optional<int32_t>((int32_t)v) : std::nullopt;
  printf("%d\n", (int)opt_deref(o));
  return 0;
}
