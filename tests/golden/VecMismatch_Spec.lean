-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z12vec_mismatchRKSt6vectorIiSaIiEES3_(a, b)` returns the first index where `a` and `b` differ, or the shorter length when one is a prefix of the other (`std::mismatch` idiom). Base body reference: the same scan on the reified words (cf. emitted `_Z12vec_mismatchRKSt6vectorIiSaIiEES3__fwd`). -/
def _Z12vec_mismatchRKSt6vectorIiSaIiEES3__spec_fwd (la lb : List (BitVec 32)) : Result Nat :=
  match loop la lb (la.length + lb.length + 1) 0 with
  | .error e => .error e
  | .ok r => .ok r
where
  loop : List (BitVec 32) → List (BitVec 32) → Nat → Nat → Result Nat
  | _, _, 0, i => .ok i
  | la, lb, fuel + 1, i =>
    if i < la.length then
      if i < lb.length then
        match la[i]?, lb[i]? with
        | some x, some y =>
          if x != y then .ok i else loop la lb fuel (i + 1)
        | _, _ => .error .AssertFail
      else .ok i
    else .ok i

/-- Edge cases: all-equal, early difference, late difference, prefix, empty, singleton hit/miss. -/
def _Z12vec_mismatchRKSt6vectorIiSaIiEES3__spec_edges : List ((List (BitVec 32) × List (BitVec 32)) × Result Nat) :=
  [(([1, 2, 3], [1, 2, 3]), .ok 3),
   (([1, 2, 3], [1, 9, 3]), .ok 1),
   (([1, 2, 3], [1, 2]), .ok 2),
   (([], [1]), .ok 0),
   (([7], [9]), .ok 0),
   (([7], [7]), .ok 1)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z12vec_mismatchRKSt6vectorIiSaIiEES3__spec_check : Bool :=
  _Z12vec_mismatchRKSt6vectorIiSaIiEES3__spec_edges.all fun t =>
    (repr (_Z12vec_mismatchRKSt6vectorIiSaIiEES3__spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
