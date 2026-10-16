// Differential-test driver for bottom-up merge sort over
// `std::vector<int>`: args are `mode na a0 ... a(na-1) nt t0 ...
// t(nt-1) [lo mid hi]` (values as signed 64-bit, range-checked to
// `int32_t`; lengths capped small). Mode 0 applies the real ranged
// `merge_runs(a, tmp, lo, mid, hi)` and prints the resulting `tmp`;
// mode 1 applies the real `vec_merge_sort(a, tmp)` entry (so
// tampering the C++ under test is caught) and prints the resulting
// `a` — both as `m w0 ... w(m-1)` on one line. Short `tmp` throws
// `std::out_of_range` natively: the driver catches it and exits 4
// (the Lean side expects loud `.error` there — the `vec_at_set`
// miss precedent). Bad usage exits 2, out-of-`int32` words exit 3.
// Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

void merge_runs(const std::vector<int> &a, std::vector<int> &tmp,
               unsigned long lo, unsigned long mid, unsigned long hi);

void vec_merge_sort(std::vector<int> &a, std::vector<int> &tmp);

static int parse_word(const char *s, int32_t *w) {
  long long v = strtoll(s, 0, 10);
  if (v < INT32_MIN || v > INT32_MAX)
    return 3;
  *w = (int32_t)v;
  return 0;
}

static int parse_vec(char **argv, long nmax, long n, std::vector<int32_t> *out) {
  if (n < 0 || n > nmax)
    return 2;
  for (long k = 0; k < n; k++) {
    int32_t w;
    int rc = parse_word(argv[k], &w);
    if (rc)
      return rc;
    out->push_back(w);
  }
  return 0;
}

static void print_vec(const std::vector<int32_t> &v) {
  printf("%lu", (unsigned long)v.size());
  for (size_t k = 0; k < v.size(); k++)
    printf(" %d", v[k]);
  printf("\n");
}

int main(int argc, char **argv) {
  if (argc < 3)
    return 2;
  long mode = strtol(argv[1], 0, 10);
  if (mode != 0 && mode != 1)
    return 2;
  long na = strtol(argv[2], 0, 10);
  if (na < 0 || na > 10 || argc < 4 + na)
    return 2;
  std::vector<int32_t> a;
  int rc = parse_vec(argv + 3, 10, na, &a);
  if (rc)
    return rc;
  long nt = strtol(argv[3 + na], 0, 10);
  if (nt < 0 || nt > 10 || argc < 4 + na + nt)
    return 2;
  std::vector<int32_t> tmp;
  rc = parse_vec(argv + 4 + na, 10, nt, &tmp);
  if (rc)
    return rc;
  try {
    if (mode == 0) {
      if (argc != 7 + na + nt)
        return 2;
      unsigned long lo = strtoul(argv[4 + na + nt], 0, 10);
      unsigned long mid = strtoul(argv[5 + na + nt], 0, 10);
      unsigned long hi = strtoul(argv[6 + na + nt], 0, 10);
      merge_runs(a, tmp, lo, mid, hi);
      print_vec(tmp);
    } else {
      if (argc != 4 + na + nt)
        return 2;
      vec_merge_sort(a, tmp);
      print_vec(a);
    }
  } catch (const std::out_of_range &) {
    return 4;
  }
  return 0;
}
