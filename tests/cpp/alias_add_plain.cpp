// alias_add_plain: two live readers WITHOUT attr text (boundary).
// Discipline: identical body to `alias_add_restrict`, but CIRGen emits
// no `llvm.noalias` evidence — the oracle cannot tell `a`/`b` apart,
// so policy must reject even though a disjoint caller would be valid.
int alias_add_plain(const int *a, const int *b) { return *a + *b; }
