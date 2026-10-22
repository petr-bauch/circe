-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z9min_indexRKSt6vectorIiSaIiEEm(a, lo)` returns the index of the minimum of `a[lo..]`. Base body reference: the same forward scan on the reified words (cf. emitted `_Z9min_indexRKSt6vectorIiSaIiEEm_fwd`). Guard-justified, total. -/
def _Z9min_indexRKSt6vectorIiSaIiEEm_spec_fwd (l : List (BitVec 32)) (lo : Nat) : Result Nat :=
  match loop l l.length (lo + 1) lo with
  | .error e => .error e
  | .ok (m, _) => .ok m
where
  loop : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat)
  | l, 0, j, m => .ok (m, j)
  | l, fuel + 1, j, m =>
    if j < l.length then
      match l[j]? with
      | none => .error .AssertFail
      | some x =>
        match l[m]? with
        | none => .error .AssertFail
        | some y =>
          if x.slt y then loop l fuel (j + 1) j
          else loop l fuel (j + 1) m
    else .ok (m, j)

/-- Edge cases: singleton, head/tail minima, interior minimum. -/
def _Z9min_indexRKSt6vectorIiSaIiEEm_spec_edges : List ((List (BitVec 32) × Nat) × Result Nat) :=
  [(([5], 0), .ok 0),
   (([3, 1, 2], 0), .ok 1),
   (([7, 8], 1), .ok 1),
   (([3, 7, 1, 8, 2], 2), .ok 2)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z9min_indexRKSt6vectorIiSaIiEEm_spec_check : Bool :=
  _Z9min_indexRKSt6vectorIiSaIiEEm_spec_edges.all fun t =>
    (repr (_Z9min_indexRKSt6vectorIiSaIiEEm_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
