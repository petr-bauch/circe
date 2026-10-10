// alias_cond: conditionally-live second writer (boundary).
// Discipline: `p` is written only under `c`, `q` always; whether they
// collide is caller-dependent, and the branch makes it invisible to
// purely textual reasoning.
void alias_cond(int &p, int &q, bool c) {
  if (c) {
    p += 1;
  }
  q += 2;
}
