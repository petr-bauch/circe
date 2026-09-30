// Differential-test driver for `point_sum_ref`: args are `x y`
// (as signed ints), prints `s` by calling the real function (so
// tampering the C++ under test is caught). Out-of-range results exit 3
// (signed overflow is UB; the Lean fuzzer only feeds in-range values
// to native and asserts Lean-Lean agreement on overflow).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>

struct Point {
  int32_t x;
  int32_t y;
  int32_t sum() const { return x + y; }
};

int32_t point_sum_ref(const Point &p);

int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  long px = strtol(argv[1], 0, 10);
  long py = strtol(argv[2], 0, 10);
  long s = px + py;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (s < INT32_MIN || s > INT32_MAX)
    return 3;
  struct Point p = {(int32_t)px, (int32_t)py};
  int32_t r = point_sum_ref(p);
  printf("%ld\n", (long)r);
  return 0;
}
