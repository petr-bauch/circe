-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z11list_lengthP4Node(head)` counts the `head`-rooted chain, returning `0` for the empty list. Base body reference: the same link chase (cf. emitted `_Z11list_lengthP4Node_fwd`, `listLengthFwd` for the entry leg). Misses abort loudly; cyclic input exhausts fuel. -/
def _Z11list_lengthP4Node_spec_len (F : Nat) (m : Mem) (cur : Option Addr) (n : Nat) :
    Result (Mem × Nat) :=
  match F with
  | 0 =>
    match cur with
    | none => .ok (m, n)
    | some _ => .error .AssertFail
  | F + 1 =>
    match cur with
    | none => .ok (m, n)
    | some a =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 1 with
        | .error e => .error e
        | .ok w => _Z11list_lengthP4Node_spec_len F m (addrOfWord w) (n + 1)

def _Z11list_lengthP4Node_spec_fwd (F : Nat) (m : Mem) (head : Option Addr) : Result (Mem × Nat) :=
  _Z11list_lengthP4Node_spec_len F m head 0

/-- Edge cases: 3-node chase, singleton, empty, missing head, short block. -/
def _Z11list_lengthP4Node_spec_edges : List (Nat × Mem × Option Addr × Option Nat) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, some 3),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, some 1),
   (10, emptyMem, none, some 0),
   (10, emptyMem, some 5, none),
   (10, (memAllocData emptyMem [(7 : BitVec 32)]).1, some 0, none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z11list_lengthP4Node_spec_check : Bool :=
  _Z11list_lengthP4Node_spec_edges.all fun t =>
    match _Z11list_lengthP4Node_spec_fwd t.1 t.2.1 t.2.2.1, t.2.2.2 with
    | .ok (_, k), some want => k == want
    | .error _, none => true
    | _, _ => false
