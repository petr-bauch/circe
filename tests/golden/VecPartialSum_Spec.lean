-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z15vec_partial_sumRSt6vectorIiSaIiEE(v)` rewrites `v` to its prefix sums in place (`std::partial_sum` idiom). Base body reference: the same scan on the reified words (cf. emitted `_Z15vec_partial_sumRSt6vectorIiSaIiEE_fwd`). Returns the final cursor alongside the rewritten words; the checked add fails loudly (`Overflow`). -/
def _Z15vec_partial_sumRSt6vectorIiSaIiEE_spec_fwd (l : List (BitVec 32)) : Result (Nat × List (BitVec 32)) :=
  match loop l l.length 1 with
  | .error e => .error e
  | .ok (i, l') => .ok (i, l')
where
  loop : List (BitVec 32) → Nat → Nat → Result (Nat × List (BitVec 32))
  | l, 0, i => .ok (i, l)
  | l, fuel + 1, i =>
    if i < l.length then
      match l[i]?, l[i - 1]? with
      | some cur, some prev =>
        match checkedAddI32 cur prev with
        | .error e => .error e
        | .ok sum => loop (l.set i sum) fuel (i + 1)
      | _, _ => .error .AssertFail
    else .ok (i, l)

/-- Edge cases: four-element scan, singleton and empty identity, negative step, loud overflow, all-negative scan. -/
def _Z15vec_partial_sumRSt6vectorIiSaIiEE_spec_edges : List (List (BitVec 32) × Result (Nat × List (BitVec 32))) :=
  [([1, 2, 3, 4], .ok (4, [1, 3, 6, 10])),
   ([5], .ok (1, [5])),
   ([], .ok (1, [])),
   ([10, -3, 7], .ok (3, [10, 7, 14])),
   ([2147483647, 1], .error .Overflow),
   ([-1, -2, -3], .ok (3, [-1, -3, -6]))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z15vec_partial_sumRSt6vectorIiSaIiEE_spec_check : Bool :=
  _Z15vec_partial_sumRSt6vectorIiSaIiEE_spec_edges.all fun t =>
    (repr (_Z15vec_partial_sumRSt6vectorIiSaIiEE_spec_fwd t.1)).pretty == (repr t.2).pretty
