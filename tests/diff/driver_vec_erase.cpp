// Differential-test driver for the N7d `std::vector<int32_t>`
// single-element `erase`: no fuzz args (the corpus entry is a closed
// script — `reserve(10)`, three pushes, `erase(begin() + 1)`, two
// reads, add), prints `vec_erase_sum()` on one line by calling the
// real `vec_erase_sum` (so tampering the C++ under test is caught).
// The Lean fuzzer pins the closed entry against this binary and
// fuzzes the `erase`/`_M_erase`/shiftDown leaves Lean-Lean (native
// has no entry point for bare leaves; the leaf paths are
// proof-covered and runtime cross-checked against the value
// forwards).
#include <cstdint>
#include <cstdio>

int32_t vec_erase_sum();

int main() {
  printf("%d\n", (int)vec_erase_sum());
  return 0;
}
