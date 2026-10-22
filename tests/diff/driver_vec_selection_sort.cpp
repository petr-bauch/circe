// Differential-test driver for iterative selection sort over
// `std::vector<int>`: args are `mode na a0 ... [lo]` (`int32`
// words; the `lo` bound only for mode 0). Mode 0 applies the real
// `min_index(a, lo)` leaf and prints the minimum index; mode 1
// applies the real `vec_selection_sort(v)` entry and prints the
// sorted words (`k w...`, `k` = `v` length, unchanged). Lengths
// capped at 8 (the outer scan is quadratic). Bad usage exits 2,
// out-of-`int32` words exit 3. Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

unsigned long min_index(const std::vector<int> &a, unsigned long lo);

void vec_selection_sort(std::vector<int> &v);

static int parse_word(const char *s, int32_t *w) {
  long long v = strtoll(s, 0, 10);
  if (v < INT32_MIN || v > INT32_MAX)
    return 3;
  *w = (int32_t)v;
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 3)
    return 2;
  long mode = strtol(argv[1], 0, 10);
  if (mode != 0 && mode != 1)
    return 2;
  long n = strtol(argv[2], 0, 10);
  if (n < 0 || n > 8 || argc < 3 + n)
    return 2;
  std::vector<int32_t> v;
  for (long k = 0; k < n; k++) {
    int32_t w;
    int rc = parse_word(argv[3 + k], &w);
    if (rc)
      return rc;
    v.push_back(w);
  }
  if (mode == 0) {
    if (argc < 4 + n)
      return 2;
    unsigned long lo = (unsigned long)strtoul(argv[3 + n], 0, 10);
    if (lo >= v.size())
      return 2;
    printf("%lu\n", min_index(v, lo));
    return 0;
  }
  vec_selection_sort(v);
  printf("%lu", (unsigned long)v.size());
  for (size_t k = 0; k < v.size(); k++)
    printf(" %d", v[k]);
  printf("\n");
  return 0;
}
