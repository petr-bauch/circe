// Differential-test driver for `translate`: args are `px py dx dy`
// (as signed ints), prints `qx qy` by calling the real function (so
// tampering the C under test is caught). Out-of-range results exit 3
// (signed overflow is UB; the Lean fuzzer only feeds in-range values
// to native and asserts Lean-Lean agreement on overflow).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

struct Point {
  int32_t x;
  int32_t y;
};

struct Point translate(struct Point p, int32_t dx, int32_t dy);

int main(int argc, char **argv) {
  if (argc != 5)
    return 2;
  long px = strtol(argv[1], 0, 10);
  long py = strtol(argv[2], 0, 10);
  long dx = strtol(argv[3], 0, 10);
  long dy = strtol(argv[4], 0, 10);
  long qx = px + dx;
  long qy = py + dy;
  // Stay in int32 range (nsw discipline); out-of-range is driver misuse.
  if (qx < INT32_MIN || qx > INT32_MAX || qy < INT32_MIN || qy > INT32_MAX)
    return 3;
  struct Point p = {(int32_t)px, (int32_t)py};
  struct Point q = translate(p, (int32_t)dx, (int32_t)dy);
  printf("%ld %ld\n", (long)q.x, (long)q.y);
  return 0;
}
