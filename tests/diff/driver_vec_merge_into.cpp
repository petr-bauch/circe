// Differential-test driver for the out-of-place two-pointer merge
// over `std::vector<int>`: args are `na a0 ... a(na-1) nb b0 ...
// b(nb-1) nout` (values as signed 64-bit, range-checked to
// `int32_t`; lengths capped small), builds the two readonly inputs
// plus a zeroed `out` of exactly `nout` words, applies the real
// `vec_merge_into(a, b, out)` entry (so tampering the C++ under test
// is caught) and prints the resulting `out` as `m w0 ... w(m-1)` on
// one line. Short `out` throws `std::out_of_range` natively: the
// driver catches it and exits 4 (the Lean side expects loud
// `.error` there — the `vec_at_set` miss precedent). Bad usage
// exits 2, out-of-`int32` words exit 3. Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

void vec_merge_into(const std::vector<int> &a, const std::vector<int> &b,
                    std::vector<int> &out);

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
  if (na < 0 || na > 8 || argc < 3 + na)
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
  if (nb < 0 || nb > 8 || argc != 4 + na + nb)
    return 2;
  std::vector<int32_t> b;
  for (long k = 0; k < nb; k++) {
    int32_t w;
    int rc = parse_word(argv[3 + na + k], &w);
    if (rc)
      return rc;
    b.push_back(w);
  }
  long nout = strtol(argv[3 + na + nb], 0, 10);
  if (nout < 0 || nout > 16)
    return 2;
  std::vector<int32_t> out((size_t)nout, 0);
  try {
    vec_merge_into(a, b, out);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%lu", (unsigned long)out.size());
  for (size_t k = 0; k < out.size(); k++)
    printf(" %d", out[k]);
  printf("\n");
  return 0;
}
