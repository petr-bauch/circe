// sdiv: signed-32 division leaf (N6a: `cir.div` on `!s32i`, signedness
// from the type, no flag). Spec: sdiv(a,b) = a/b truncated toward zero;
// division by zero reports DivZero, INT_MIN/-1 reports Overflow
// (checkedDivI32).
int sdiv(int a, int b) {
  return a / b;
}
