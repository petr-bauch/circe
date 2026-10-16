// alias_reborrow34: sequential `&mut` live ranges over one object, second
// customer (L1a spike). Discipline: `r` is dead before `s` is born at
// source level, but raw CIRGen at this pin carries no lifetime markers,
// so both derived references look live in the `.cir` text. Different
// constants than `alias_reborrow` (`3`/`4` vs `1`/`2`) so the F1
// const-use pins do not fire while the sequential-writer skeleton
// (structural + L2-disjoint + F0 same-address) does.
void alias_reborrow34(int &x) {
  int &r = x;
  r += 3;
  int &s = x;
  s += 4;
}
