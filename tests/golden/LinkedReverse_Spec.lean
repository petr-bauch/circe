-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z12list_reverseP4Node(head)` reverses the `head`-rooted chain in place, returning the new head. Base body reference: the same link chase (cf. emitted `_Z12list_reverseP4Node_fwd`, `linkRevFwd` for the entry leg). Misses abort loudly; cyclic input exhausts fuel. -/
def _Z12list_reverseP4Node_spec_chase (F : Nat) (m : Mem) (prev cur : Option Addr) :
    Result (Mem × Option Addr) :=
  match F with
  | 0 =>
    match cur with
    | none => .ok (m, prev)
    | some _ => .error .AssertFail
  | F + 1 =>
    match cur with
    | none => .ok (m, prev)
    | some a =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 1 with
        | .error e => .error e
        | .ok w =>
          match memStore m a b.tag 1 (linkWord prev) with
          | .error e => .error e
          | .ok m' => _Z12list_reverseP4Node_spec_chase F m' cur (addrOfWord w)

def _Z12list_reverseP4Node_spec_fwd (F : Nat) (m : Mem) (head : Option Addr) : Result (Mem × Option Addr) :=
  _Z12list_reverseP4Node_spec_chase F m none head

/-- Payloads chased from a head (fuel-bounded; link words decode through `addrOfWord`). -/
def _Z12list_reverseP4Node_chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
  match F with
  | 0 => []
  | F + 1 =>
    match head with
    | none => []
    | some a =>
      match memFind m a with
      | none => []
      | some b =>
        match b.data[0]? with
        | none => []
        | some v => v :: _Z12list_reverseP4Node_chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Edge cases: 3-node chase, singleton, empty, missing head, short block. -/
def _Z12list_reverseP4Node_spec_edges : List (Nat × Mem × Option Addr × Option (Option Addr × List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, some (some 0, [30, 20, 10])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, some (some 0, [7])),
   (10, emptyMem, none, some (none, [])),
   (10, emptyMem, some 5, none),
   (10, (memAllocData emptyMem [(7 : BitVec 32)]).1, some 0, none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z12list_reverseP4Node_spec_check : Bool :=
  _Z12list_reverseP4Node_spec_edges.all fun t =>
    match _Z12list_reverseP4Node_spec_fwd t.1 t.2.1 t.2.2.1, t.2.2.2 with
    | .ok (m', p'), some (q', vs) =>
      p' == q' && _Z12list_reverseP4Node_chainVals m' p' 32 == vs
    | .error _, none => true
    | _, _ => false
