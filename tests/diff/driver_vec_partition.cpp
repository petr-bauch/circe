// Differential driver for `vec_partition`: argv is
//   n w... pivot
// (`int32` words, then the pivot); runs the in-place Lomuto
// partition and prints `k w...` (`k` = `v` length, unchanged).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

void vec_partition(std::vector<int> &v, int pivot);

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
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc < 3 + n)
    return 2;
  std::vector<int32_t> v;
  for (long k = 0; k < n; k++) {
    int32_t w;
    int rc = parse_word(argv[2 + k], &w);
    if (rc)
      return rc;
    v.push_back(w);
  }
  int32_t pivot;
  if (parse_word(argv[2 + n], &pivot))
    return 3;
  vec_partition(v, pivot);
  printf("%lu", (unsigned long)v.size());
  for (size_t k = 0; k < v.size(); k++)
    printf(" %d", v[k]);
  printf("\n");
  return 0;
}
