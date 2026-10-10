// alias_add_restrict: two live readers with `__restrict__` attr text.
// Discipline: `const` reads only, CIRGen lowers `__restrict__` to
// `{llvm.noalias, ...}` on both params (the `sum_array` C precedent,
// here in C++).
int alias_add_restrict(const int *__restrict__ a, const int *__restrict__ b) {
  return *a + *b;
}
