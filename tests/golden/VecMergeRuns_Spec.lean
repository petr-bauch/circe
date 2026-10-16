-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm(a, tmp, lo, mid, hi)` merges the sorted `a[lo,mid)`, `a[mid,hi)` into `tmp[lo,hi)`. Base body reference: the same ranged merge on the reified words (cf. emitted `_Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm_fwd`, `mergeRunsMainFwd` + drains). Short `tmp` aborts loudly. -/
def _Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm_spec_fwd (la lt : List (BitVec 32)) (lo mid hi : Nat) : Result (List (BitVec 32)) :=
  match main la lt lt ((mid - lo) + (hi - lo)) lo mid lo with
  | .error e => .error e
  | .ok (i, j, k, lt') =>
    match drainI la lt' (mid - i) i k with
    | .error e => .error e
    | .ok (_, k', lt'') =>
      match drainJ la lt'' (hi - j) j k' with
      | .error e => .error e
      | .ok (_, _, lt''') => .ok lt'''
where
  main (la lt : List (BitVec 32)) : List (BitVec 32) → Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | acc, 0, i, j, k => .ok (i, j, k, acc)
  | acc, fuel + 1, i, j, k =>
    if i < mid then
      if j < hi then
        match acc[k]? with
        | none => .error .AssertFail
        | some _ =>
          match la[i]?, la[j]? with
          | some x, some y =>
            if x.slt y then main la lt (acc.set k x) fuel (i + 1) j (k + 1)
            else main la lt (acc.set k y) fuel i (j + 1) (k + 1)
          | _, _ => .error .AssertFail
      else .ok (i, j, k, acc)
    else .ok (i, j, k, acc)
  drainI (la : List (BitVec 32)) : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | acc, 0, i, k => .ok (i, k, acc)
  | acc, fuel + 1, i, k =>
    if i < mid then
      match acc[k]? with
      | none => .error .AssertFail
      | some _ =>
        match la[i]? with
        | some x => drainI la (acc.set k x) fuel (i + 1) (k + 1)
        | none => .error .AssertFail
    else .ok (i, k, acc)
  drainJ (la : List (BitVec 32)) : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | acc, 0, j, k => .ok (j, k, acc)
  | acc, fuel + 1, j, k =>
    if j < hi then
      match acc[k]? with
      | none => .error .AssertFail
      | some _ =>
        match la[j]? with
        | some x => drainJ la (acc.set k x) fuel (j + 1) (k + 1)
        | none => .error .AssertFail
    else .ok (j, k, acc)

/-- Edge cases: interleave merges, empty-left drains right, short `tmp` aborts. -/
def _Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm_spec_edges : List (((List (BitVec 32) × List (BitVec 32)) × Nat × Nat × Nat) × Result (List (BitVec 32))) :=
  [((([1, 3, 5, 2, 4, 6], [0, 0, 0, 0, 0, 0]), 0, 3, 6), .ok [1, 2, 3, 4, 5, 6]),
   ((([], []), 0, 0, 0), .ok []),
   ((([1], []), 0, 0, 1), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm_spec_check : Bool :=
  _Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm_spec_edges.all fun t =>
    (repr (_Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm_spec_fwd t.1.1.1 t.1.1.2 t.1.2.1 t.1.2.2.1 t.1.2.2.2)).pretty == (repr t.2).pretty
