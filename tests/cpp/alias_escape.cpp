// alias_escape: address-of-ref-param escapes as return (control).
// Discipline: `&x` feeds `return`, not a `restrict` call in the same
// scope (SUBSET rule 5) and not the borrow-return pattern — the
// escape-reject shape in real CIR instead of inline text.
int *alias_escape(int &x) { return &x; }
