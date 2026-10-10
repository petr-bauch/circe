// alias_readonly_pair: two live `const&` readers (boundary).
// Discipline: both params carry the single-reference triple, which
// `oracleParams` excludes from governance (C++ untouched by N2c) —
// the question is whether the pair needs any verdict at all.
int alias_readonly_pair(const int &a, const int &b) { return a + b; }
