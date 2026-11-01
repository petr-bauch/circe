-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z10list_clearP4Node(head)` frees the whole `head`-rooted chain, returning null. Base body reference: the same free chase (cf. emitted `_Z10list_clearP4Node_fwd`, `listClearFwd` for the entry leg). Freed cells keep their words; dangling links abort loudly; cyclic input exhausts fuel. -/
def _Z10list_clearP4Node_spec_clear (F : Nat) (m : Mem) (cur : Option Addr) :
    Result Mem :=
  match cur with
  | none => .ok m
  | some a =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 1 with
        | .error e => .error e
        | .ok w' =>
          match memFree m a b.tag with
          | .error e => .error e
          | .ok m' => _Z10list_clearP4Node_spec_clear F m' (addrOfWord w')

def _Z10list_clearP4Node_spec_fwd (F : Nat) (m : Mem) (head : Option Addr) :
    Result Mem :=
  _Z10list_clearP4Node_spec_clear F m head

/-- Payloads chased from a head (fuel-bounded; freed cells keep their words, so the dead chain still reads back). -/
def _Z10list_clearP4Node_chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
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
        | some v => v :: _Z10list_clearP4Node_chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Every address in the list is present and dead. -/
def _Z10list_clearP4Node_chainDead (m : Mem) (addrs : List Addr) : Bool :=
  addrs.all fun a => ((memFind m a).map (fun b => !b.live)) == some true

/-- Edge cases: 3-node free, singleton, empty, missing head, short block. -/
def _Z10list_clearP4Node_spec_edges : List (Nat × Mem × Option Addr × Option (List Addr × List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, some ([0, 1, 2], [10, 20, 30])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, some ([0], [7])),
   (10, emptyMem, none, some ([], [])),
   (10, emptyMem, some 5, none),
   (10, (memAllocData emptyMem [(7 : BitVec 32)]).1, some 0, none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (every input node dead with its payload kept; loud legs loud). -/
def _Z10list_clearP4Node_spec_check : Bool :=
  _Z10list_clearP4Node_spec_edges.all fun t =>
    match _Z10list_clearP4Node_spec_fwd t.1 t.2.1 t.2.2.1, t.2.2.2 with
    | .ok m', some (addrs, vs) =>
      _Z10list_clearP4Node_chainDead m' addrs && _Z10list_clearP4Node_chainVals m' t.2.2.1 32 == vs
    | .error _, none => true
    | _, _ => false
