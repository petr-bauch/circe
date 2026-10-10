// alias_incr_ref: single live `int&` writer (ADMIT control).
// Discipline: one mutating reference, the N9 single-`&mut` containment
// shape — no second reference can collide.
void alias_incr_ref(int &r) { ++r; }
