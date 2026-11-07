-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z18list_sorted_insertP4Nodei(head, v)` inserts `v` into the sorted `head`-rooted chain, returning the (possibly new) head. Base body reference: the same chase plus allocate-store-swing (cf. emitted `_Z18list_sorted_insertP4Nodei_fwd`, `listSortedInsertFwd` for the entry leg). Misses abort loudly; cyclic input exhausts fuel. -/
def _Z18list_sorted_insertP4Nodei_spec_chase (F : Nat) (m : Mem) (prev cur : Option Addr)
    (v : BitVec 32) : Result (Option Addr × Option Addr) :=
  match cur with
  | none => .ok (prev, none)
  | some a =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 0 with
        | .error e => .error e
        | .ok w =>
          if (v.slt w) then .ok (prev, some a)
          else match memLoad m a b.tag 1 with
               | .error e => .error e
               | .ok w' =>
                 _Z18list_sorted_insertP4Nodei_spec_chase F m (some a) (addrOfWord w') v

def _Z18list_sorted_insertP4Nodei_spec_fwd (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) : Result (Mem × Option Addr) :=
  match _Z18list_sorted_insertP4Nodei_spec_chase F m none head v with
  | .error e => .error e
  | .ok (prev, cur) =>
    let (m1, a) := memAlloc m 2
    match memFind m1 a with
    | none => .error .AssertFail
    | some ba =>
      match memStore m1 a ba.tag 0 v with
      | .error e => .error e
      | .ok m2 =>
        match memFind m2 a with
        | none => .error .AssertFail
        | some ba2 =>
          match memStore m2 a ba2.tag 1 (linkWord cur) with
          | .error e => .error e
          | .ok m3 =>
            match prev with
            | none => .ok (m3, some a)
            | some p =>
              match memFind m3 p with
              | none => .error .AssertFail
              | some bp =>
                match memStore m3 p bp.tag 1 (linkWord (some a)) with
                | .error e => .error e
                | .ok m4 => .ok (m4, head)

/-- Payloads chased from a head (fuel-bounded; link words decode through `addrOfWord`). -/
def _Z18list_sorted_insertP4Nodei_chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
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
        | some v => v :: _Z18list_sorted_insertP4Nodei_chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Edge cases: middle landing, head landing, empty chain, singleton equal-payload append (upper bound), missing head, short block. -/
def _Z18list_sorted_insertP4Nodei_spec_edges : List (Nat × Mem × Option Addr × BitVec 32 × Option (Option Addr × List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(10 : BitVec 32), 2]).1 [(20 : BitVec 32), 3]).1 [(30 : BitVec 32), 0]).1, some 0, (25 : BitVec 32), some (some 0, [10, 20, 25, 30])),
   (10, (memAllocData (memAllocData emptyMem [(10 : BitVec 32), 2]).1 [(20 : BitVec 32), 0]).1, some 0, (5 : BitVec 32), some (some 2, [5, 10, 20])),
   (10, emptyMem, none, (7 : BitVec 32), some (some 0, [7])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, (7 : BitVec 32), some (some 0, [7, 7])),
   (10, emptyMem, some 5, (1 : BitVec 32), none),
   (10, (memAllocData emptyMem [(7 : BitVec 32)]).1, some 0, (9 : BitVec 32), none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z18list_sorted_insertP4Nodei_spec_check : Bool :=
  _Z18list_sorted_insertP4Nodei_spec_edges.all fun t =>
    match _Z18list_sorted_insertP4Nodei_spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok (m', p'), some (q', vs) =>
      p' == q' && _Z18list_sorted_insertP4Nodei_chainVals m' p' 32 == vs
    | .error _, none => true
    | _, _ => false
