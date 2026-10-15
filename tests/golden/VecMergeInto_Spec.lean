-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1_(a, b, out)` merges the sorted `a.at(i)`, `b.at(j)` into `out.at(k)`. Base body reference: the same merge on the reified words (cf. emitted `_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1__fwd`, `mergeMainFwd` + drains). Short `out` aborts loudly. -/
def _Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1__spec_fwd (la lb lo : List (BitVec 32)) : Result (List (BitVec 32)) :=
  match main la lb lo (la.length + lb.length) 0 0 0 with
  | .error e => .error e
  | .ok (i, j, k, lo') =>
    match drainA la lo' (la.length - i) i k with
    | .error e => .error e
    | .ok (_, k', lo'') =>
      match drainB lb lo'' (lb.length - j) j k' with
      | .error e => .error e
      | .ok (_, _, lo''') => .ok lo'''
where
  main (la lb : List (BitVec 32)) : List (BitVec 32) → Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | lo, 0, i, j, k => .ok (i, j, k, lo)
  | lo, fuel + 1, i, j, k =>
    if i < la.length then
      if j < lb.length then
        match lo[k]? with
        | none => .error .AssertFail
        | some _ =>
          match la[i]?, lb[j]? with
          | some x, some y =>
            if x.slt y then main la lb (lo.set k x) fuel (i + 1) j (k + 1)
            else main la lb (lo.set k y) fuel i (j + 1) (k + 1)
          | _, _ => .error .AssertFail
      else .ok (i, j, k, lo)
    else .ok (i, j, k, lo)
  drainA (la : List (BitVec 32)) : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lo, 0, i, k => .ok (i, k, lo)
  | lo, fuel + 1, i, k =>
    if i < la.length then
      match lo[k]? with
      | none => .error .AssertFail
      | some _ =>
        match la[i]? with
        | some x => drainA la (lo.set k x) fuel (i + 1) (k + 1)
        | none => .error .AssertFail
    else .ok (i, k, lo)
  drainB (lb : List (BitVec 32)) : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lo, 0, j, k => .ok (j, k, lo)
  | lo, fuel + 1, j, k =>
    if j < lb.length then
      match lo[k]? with
      | none => .error .AssertFail
      | some _ =>
        match lb[j]? with
        | some x => drainB lb (lo.set k x) fuel (j + 1) (k + 1)
        | none => .error .AssertFail
    else .ok (j, k, lo)

/-- Edge cases: interleave merges, empty-`a` drains `b`, short `out` aborts. -/
def _Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1__spec_edges : List (((List (BitVec 32) × List (BitVec 32)) × List (BitVec 32)) × Result (List (BitVec 32))) :=
  [((([1, 3, 5], [2, 4, 6]), [0, 0, 0, 0, 0, 0]), .ok [1, 2, 3, 4, 5, 6]),
   ((([], [1, 2]), [0, 0]), .ok [1, 2]),
   ((([1], [2]), [0]), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1__spec_check : Bool :=
  _Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1__spec_edges.all fun t =>
    (repr (_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1__spec_fwd t.1.1.1 t.1.1.2 t.1.2)).pretty == (repr t.2).pretty
