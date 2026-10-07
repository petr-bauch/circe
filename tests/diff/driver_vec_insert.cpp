// Differential-test driver for the N7c `std::vector<int32_t>`
// single-element `insert`: no fuzz args (the corpus entry is a closed
// script — `reserve(10)`, two pushes, `insert(begin() + 1, 2)`, three
// reads, add), prints `vec_insert_sum()` on one line by calling the
// real `vec_insert_sum` (so tampering the C++ under test is caught).
// The Lean fuzzer pins the closed entry against this binary and
// fuzzes the `insert`/`insert_aux`/`insert_rval`/shift leaves
// Lean-Lean (native has no entry point for bare leaves; the leaf
// paths are proof-covered and runtime cross-checked against the
// value forwards).
#include <cstdint>
#include <cstdio>

int32_t vec_insert_sum();

int main() {
  printf("%d\n", (int)vec_insert_sum());
  return 0;
}
