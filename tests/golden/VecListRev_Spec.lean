-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z8list_revRSt6vectorIiSaIiEES2_mm(data, nxt, head, n)` reverses the `head`-rooted chain in `nxt` in place, returning the new head. Base body reference: the link chase over the reified words (cf. emitted `_Z8list_revRSt6vectorIiSaIiEES2_mm_fwd`, `revFwd` for the entry leg). Read and rewire misses abort like `at()`-throw; cyclic input exhausts fuel. -/
def _Z8list_revRSt6vectorIiSaIiEES2_mm_spec_chase (F : Nat) (nxt : List (BitVec 32)) (n prev cur : BitVec 64) :
    Result (List (BitVec 32) × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if cur != n then .error .AssertFail
    else .ok (nxt, prev, cur)
  | F + 1 =>
    if cur != n then
      match nxt[cur.toNat]? with
      | none => .error .AssertFail
      | some w =>
        _Z8list_revRSt6vectorIiSaIiEES2_mm_spec_chase F (nxt.set cur.toNat (BitVec.ofNat 32 prev.toNat))
          n cur (w.signExtend 64)
    else .ok (nxt, prev, cur)

def _Z8list_revRSt6vectorIiSaIiEES2_mm_spec_fwd (F : Nat) (data nxt : List (BitVec 32)) (head n : BitVec 64) : Result (List (BitVec 32) × BitVec 64) :=
  match _Z8list_revRSt6vectorIiSaIiEES2_mm_spec_chase F nxt n n head with
  | .error e => .error e
  | .ok (nxt', prev, _) => .ok (nxt', prev)

/-- Edge cases: 3-node chase, singleton, empty, mid-list head, OOB head, short `nxt`. -/
def _Z8list_revRSt6vectorIiSaIiEES2_mm_spec_edges : List (((Nat × List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64)) × Result (List (BitVec 32) × BitVec 64)) :=
  [((100, [10, 20, 30], [1, 2, 3], 0, 3), .ok ([3, 0, 1], 2)),
   ((100, [7], [1], 0, 1), .ok ([1], 0)),
   ((100, [], [], 0, 0), .ok ([], 0)),
   ((100, [10, 20, 30], [1, 2, 3], 1, 3), .ok ([1, 3, 1], 2)),
   ((100, [10], [0], 5, 1), .error .AssertFail),
   ((100, [10, 20], [1], 0, 2), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z8list_revRSt6vectorIiSaIiEES2_mm_spec_check : Bool :=
  _Z8list_revRSt6vectorIiSaIiEES2_mm_spec_edges.all fun t =>
    (repr (_Z8list_revRSt6vectorIiSaIiEES2_mm_spec_fwd t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2)).pretty == (repr t.2).pretty
