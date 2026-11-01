-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z9list_findP4Nodei(head, v)` returns the first `Node` holding `v` in the `head`-rooted chain, or null if absent; the chain is never modified. Base body reference: the same payload chase (cf. emitted `_Z9list_findP4Nodei_fwd`, `listFindFwd` for the entry leg). Misses on a valid chain return null; dangling links abort loudly; cyclic input exhausts fuel. -/
def _Z9list_findP4Nodei_spec_find (F : Nat) (m : Mem) (cur : Option Addr)
    (v : BitVec 32) : Result (Option Addr) :=
  match cur with
  | none => .ok none
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
          if w == v then .ok (some a)
          else match memLoad m a b.tag 1 with
               | .error e => .error e
               | .ok w' => _Z9list_findP4Nodei_spec_find F m (addrOfWord w') v

def _Z9list_findP4Nodei_spec_fwd (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) : Result (Option Addr) :=
  _Z9list_findP4Nodei_spec_find F m head v

/-- Edge cases: head-hit, interior-hit, miss, empty, singleton-hit, singleton-miss, missing head. -/
def _Z9list_findP4Nodei_spec_edges : List (Nat × Mem × Option Addr × BitVec 32 × Option (Option Addr)) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, (10 : BitVec 32), some (some 2)),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, (20 : BitVec 32), some (some 1)),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, (99 : BitVec 32), some none),
   (10, emptyMem, none, (5 : BitVec 32), some none),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, (7 : BitVec 32), some (some 0)),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, (5 : BitVec 32), some none),
   (10, emptyMem, some 5, (5 : BitVec 32), none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (found address matches, and a hit points at the payload). -/
def _Z9list_findP4Nodei_spec_check : Bool :=
  _Z9list_findP4Nodei_spec_edges.all fun t =>
    match _Z9list_findP4Nodei_spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok p', some q' =>
      p' == q' && match p' with
        | none => true
        | some a =>
          match memFind t.2.1 a with
          | some b => b.data[0]? == some t.2.2.2.1
          | none => false
    | .error _, none => true
    | _, _ => false
