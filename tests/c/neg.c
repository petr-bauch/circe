// neg: signed-32 negation leaf (N6a: `cir.minus nsw` on `!s32i`).
// Spec: neg(x) = -x; INT_MIN (`-(-2^31)`) overflows, reported loud
// as Overflow on the Lean side (checkedNegI32).
int neg(int x) {
  return -x;
}
