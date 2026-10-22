-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z18vec_selection_sortRSt6vectorIiSaIiEE(v)` selection-sorts `v` in place by repeated minimum scans and swaps. Base body reference: the same scan-and-swap on the reified words (cf. emitted `_Z18vec_selection_sortRSt6vectorIiSaIiEE_fwd`). Guard-justified, total. -/
def _Z18vec_selection_sortRSt6vectorIiSaIiEE_spec_fwd (l : List (BitVec 32)) : Result (List (BitVec 32)) :=
  match loop l l.length l.length 0 with
  | .error e => .error e
  | .ok (_, l') => .ok l'
where
  minLoop : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat)
  | l, 0, j, m => .ok (m, j)
  | l, fuel + 1, j, m =>
    if j < l.length then
      match l[j]? with
      | none => .error .AssertFail
      | some x =>
        match l[m]? with
        | none => .error .AssertFail
        | some y =>
          if x.slt y then minLoop l fuel (j + 1) j
          else minLoop l fuel (j + 1) m
    else .ok (m, j)
  loop : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × List (BitVec 32))
  | l, 0, _, i => .ok (i, l)
  | l, fuel + 1, inner, i =>
    if i < l.length then
      match minLoop l inner (i + 1) i with
      | .error e => .error e
      | .ok (m, _) =>
        match l[i]?, l[m]? with
        | some x, some y => loop ((l.set i y).set m x) fuel inner (i + 1)
        | _, _ => .error .AssertFail
    else .ok (i, l)

/-- Edge cases: empty is identity, sorted stays fixed, the swap trace sorts. -/
def _Z18vec_selection_sortRSt6vectorIiSaIiEE_spec_edges : List (List (BitVec 32) × Result (List (BitVec 32))) :=
  [([], .ok []),
   ([1, 2, 3], .ok [1, 2, 3]),
   ([3, 1, 2], .ok [1, 2, 3]),
   ([3, 7, 1, 8, 2], .ok [1, 2, 3, 7, 8]),
   ([5, 1], .ok [1, 5])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z18vec_selection_sortRSt6vectorIiSaIiEE_spec_check : Bool :=
  _Z18vec_selection_sortRSt6vectorIiSaIiEE_spec_edges.all fun t =>
    (repr (_Z18vec_selection_sortRSt6vectorIiSaIiEE_spec_fwd t.1)).pretty == (repr t.2).pretty
