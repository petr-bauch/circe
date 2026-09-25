// Differential-test driver for `choose`: two modes.
//   sel b x y   -> prints *choose(b, &x, &y)   (forward selection)
//   wb  b x y v -> writes v through the return, prints "x y" (backward write-back)
//
// All inputs are in-range by construction (selection never overflows;
// write-back is a plain store). No UB exercised.
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int32_t *choose(bool b, int32_t *__restrict x, int32_t *__restrict y);

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  if (strcmp(argv[1], "sel") == 0 && argc == 5) {
    bool b = (bool)strtol(argv[2], 0, 10);
    int32_t x = (int32_t)strtol(argv[3], 0, 10);
    int32_t y = (int32_t)strtol(argv[4], 0, 10);
    int32_t *r = choose(b, &x, &y);
    printf("%ld\n", (long)*r);
    return 0;
  }
  if (strcmp(argv[1], "wb") == 0 && argc == 6) {
    bool b = (bool)strtol(argv[2], 0, 10);
    int32_t x = (int32_t)strtol(argv[3], 0, 10);
    int32_t y = (int32_t)strtol(argv[4], 0, 10);
    int32_t v = (int32_t)strtol(argv[5], 0, 10);
    int32_t *r = choose(b, &x, &y);
    *r = v;
    printf("%ld %ld\n", (long)x, (long)y);
    return 0;
  }
  return 2;
}
