// alias_disjoint: two local arrays, provably disjoint by construction.
// Discipline: no params at all (`add`-style pure closed shape); `a` and
// `b` are distinct allocas, so noalias holds by construction — but the
// recovery precedent (N2c) covers single-pointer shapes only.
int alias_disjoint() {
  int a[2] = {1, 2};
  int b[2] = {3, 4};
  return a[0] + a[1] + b[0] + b[1];
}
