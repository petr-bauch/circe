// Differential driver for `vec_transform_add`: reads
//   n in... m out... c
// (`int32` words, then the constant), runs
// `vec_transform_add(in, out, c)`, and prints `k w...` (`k` = `out`
// length). Short `out` throws `std::out_of_range` natively → exit 4
// (the `vec_at_set` miss precedent).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

void vec_transform_add(const std::vector<int> &in, std::vector<int> &out,
                       int c);

static int parse_word(const char *s, int32_t *w) {
  long long v = strtoll(s, 0, 10);
  if (v < INT32_MIN || v > INT32_MAX)
    return 3;
  *w = (int32_t)v;
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 4)
    return 2;
  long na = strtol(argv[1], 0, 10);
  if (na < 0 || na > 8 || argc < 4 + na)
    return 2;
  std::vector<int32_t> a;
  for (long k = 0; k < na; k++) {
    int32_t w;
    int rc = parse_word(argv[2 + k], &w);
    if (rc)
      return rc;
    a.push_back(w);
  }
  long nb = strtol(argv[2 + na], 0, 10);
  if (nb < 0 || nb > 8 || argc != 4 + na)
    return 2;
  std::vector<int32_t> b((size_t)nb, 0);
  int32_t c;
  if (parse_word(argv[3 + na], &c))
    return 3;
  try {
    vec_transform_add(a, b, c);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%lu", (unsigned long)b.size());
  for (size_t k = 0; k < b.size(); k++)
    printf(" %d", b[k]);
  printf("\n");
  return 0;
}
