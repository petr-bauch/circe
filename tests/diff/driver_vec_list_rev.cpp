// Differential-test driver for index-linked in-place reversal: args are
// `nd d0 ... nn n0 ... head n` (data/link values as signed 64-bit,
// range-checked to `int32_t`; `head`/`n` as unsigned 64-bit), applies
// `list_rev(data, nxt, head, n)` to locally built vectors (the entry
// takes both vectors by mutable `&`; the caller owns construction) and
// prints the new head on the first line and the final link words on the
// second line by calling the real entry (so tampering the C++ under
// test is caught). Any `at()` miss throws `std::out_of_range`
// natively: the driver catches it and exits 4 (the Lean side expects
// loud `.error` there — the `vec_at_one` empty-read precedent). The arg
// count is exact (`argc == 5 + nd + nn`: `argv[0]` plus the two header
// words plus `head`/`n`). Mismatch = P0.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <climits>
#include <vector>
#include <stdexcept>

unsigned long list_rev(std::vector<int> &data, std::vector<int> &nxt,
                       unsigned long head, unsigned long n);

int main(int argc, char **argv) {
  if (argc < 5)
    return 2;
  long nd = strtol(argv[1], 0, 10);
  if (nd < 0 || nd > 32)
    return 2;
  std::vector<int32_t> data;
  for (long k = 0; k < nd; k++) {
    long long w = strtoll(argv[2 + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    data.push_back((int32_t)w);
  }
  long nn = strtol(argv[2 + nd], 0, 10);
  if (nn < 0 || nn > 32 || argc != 5 + nd + nn)
    return 2;
  std::vector<int32_t> nxt;
  for (long k = 0; k < nn; k++) {
    long long w = strtoll(argv[3 + nd + k], 0, 10);
    if (w < INT32_MIN || w > INT32_MAX)
      return 3;
    nxt.push_back((int32_t)w);
  }
  unsigned long head = strtoul(argv[3 + nd + nn], 0, 10);
  unsigned long n = strtoul(argv[4 + nd + nn], 0, 10);
  unsigned long got = 0;
  try {
    got = list_rev(data, nxt, head, n);
  } catch (const std::out_of_range &) {
    return 4;
  }
  printf("%lu\n", got);
  for (long k = 0; k < nn; k++) {
    if (k)
      printf(" ");
    printf("%d", nxt[k]);
  }
  printf("\n");
  return 0;
}
