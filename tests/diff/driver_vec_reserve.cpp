// Differential-test driver for the N7b `std::vector<int32_t>`
// `reserve`: no fuzz args (the corpus entry is a closed script —
// `reserve(10)`, two pushes, two reads, add), prints
// `vec_reserve_sum()` on one line by calling the real
// `vec_reserve_sum` (so tampering the C++ under test is caught).
// The Lean fuzzer pins the closed entry against this binary and
// fuzzes the `capacity`/`reserve` leaves Lean-Lean (native has no
// entry point for bare leaves; the leaf paths are proof-covered
// and runtime cross-checked against the value forwards).
#include <cstdint>
#include <cstdio>

int32_t vec_reserve_sum();

int main() {
  printf("%d\n", (int)vec_reserve_sum());
  return 0;
}
