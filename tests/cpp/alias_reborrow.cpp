// alias_reborrow: sequential `&mut` live ranges over one object (boundary).
// Discipline: `r` is dead before `s` is born at source level, but raw
// CIRGen at this pin carries no lifetime markers, so both derived
// references look live in the `.cir` text.
void alias_reborrow(int &x) {
  int &r = x;
  r += 1;
  int &s = x;
  s += 2;
}
