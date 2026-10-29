// heap_sort: iterative in-place ascending heapsort (H-slice corpus).
// Discipline: `v` is `&` (single-reference triple, oracle governance
// vacuous, verdict honestly `unknown`); `n` is the heap length
// (`u64`, the G-track cursor convention — no signed sentinel, no
// division: the subset has no unsigned div). Heapify counts down
// from `n` (`usub`): sift-down at every `i` (leaves are no-ops) —
// no `n/2`. Sift-down computes `child = 2*root+1` with wrapping
// `u64` arithmetic (`umul`/`uadd`); every element access goes
// through `at()` (loud misses); the swap is `at()`-ptr +
// store (the R/S pattern). Extract-max swaps the root with the
// last heap element and re-sifts the reduced heap. The two outer
// drains and the two inner sifts are `while` loops with `break`
// exits (S3a-native); `n == 0` and `n == 1` exit through the same
// loops with no work. A short `n` (past the vector length) aborts
// loud at the first out-of-range `at()`.
// Spec: on exit `v[0, n)` holds the ascending heap order; `v[n,
// ...)` is untouched.
#include <vector>

void heap_sort(std::vector<int> &v, unsigned long n) {
  unsigned long i = n;
  while (i != 0) {
    i = i - 1;
    unsigned long root = i;
    while (true) {
      unsigned long child = root * 2 + 1;
      if (child >= n)
        break;
      unsigned long other = child + 1;
      if (other < n && v.at(other) > v.at(child))
        child = other;
      if (v.at(root) >= v.at(child))
        break;
      int t = v.at(root);
      v.at(root) = v.at(child);
      v.at(child) = t;
      root = child;
    }
  }
  unsigned long last = n;
  while (last != 0) {
    last = last - 1;
    int t = v.at(0);
    v.at(0) = v.at(last);
    v.at(last) = t;
    unsigned long root = 0;
    while (true) {
      unsigned long child = root * 2 + 1;
      if (child >= last)
        break;
      unsigned long other = child + 1;
      if (other < last && v.at(other) > v.at(child))
        child = other;
      if (v.at(root) >= v.at(child))
        break;
      int t2 = v.at(root);
      v.at(root) = v.at(child);
      v.at(child) = t2;
      root = child;
    }
  }
}
