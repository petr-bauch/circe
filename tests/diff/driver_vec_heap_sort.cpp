// Differential driver for `heap_sort`: argv is
//   n w...
// (`int32` words); sorts `v[0..n)` in place and prints `k w...`
// (`k` = `v` length, unchanged).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>

void heap_sort(std::vector<int> &v, unsigned long n);

static int parse_word(const char *s, int32_t *w) {
  long long v = strtoll(s, 0, 10);
  if (v < INT32_MIN || v > INT32_MAX)
    return 3;
  *w = (int32_t)v;
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2)
    return 2;
  long n = strtol(argv[1], 0, 10);
  if (n < 0 || n > 8 || argc < 2 + n)
    return 2;
  std::vector<int32_t> v;
  for (long k = 0; k < n; k++) {
    int32_t w;
    int rc = parse_word(argv[2 + k], &w);
    if (rc)
      return rc;
    v.push_back(w);
  }
  heap_sort(v, (unsigned long)n);
  printf("%lu", (unsigned long)v.size());
  for (size_t k = 0; k < v.size(); k++)
    printf(" %d", v[k]);
  printf("\n");
  return 0;
}
