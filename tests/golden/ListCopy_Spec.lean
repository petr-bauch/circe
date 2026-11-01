-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z9list_copyP4Node(head)` deep-copies the `head`-rooted chain, returning the fresh head (null on empty input). Base body reference: the same allocate-and-chase (cf. emitted `_Z9list_copyP4Node_fwd`, `listCopyFwd` for the entry leg). The input chain is never written; dangling links abort loudly; cyclic input exhausts fuel. -/
def _Z9list_copyP4Node_spec_copy (F : Nat) (m : Mem) (cur nh tail : Option Addr) :
    Result (Mem × Option Addr × Option Addr) :=
  match cur with
  | none => .ok (m, nh, tail)
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
          match memLoad m a b.tag 1 with
          | .error e => .error e
          | .ok w' =>
            let (m1, nd) := memAlloc m 2
            match memStore m1 nd nd 0 w with
            | .error e => .error e
            | .ok m2 =>
              match memStore m2 nd nd 1 (linkWord none) with
              | .error e => .error e
              | .ok m3 =>
                match tail with
                | none =>
                  _Z9list_copyP4Node_spec_copy F m3 (addrOfWord w') (some nd) (some nd)
                | some p =>
                  match memFind m3 p with
                  | none => .error .AssertFail
                  | some bp =>
                    match memStore m3 p bp.tag 1 (linkWord (some nd)) with
                    | .error e => .error e
                    | .ok m4 =>
                      _Z9list_copyP4Node_spec_copy F m4 (addrOfWord w') nh (some nd)

def _Z9list_copyP4Node_spec_fwd (F : Nat) (m : Mem) (head : Option Addr) :
    Result (Mem × Option Addr) :=
  match _Z9list_copyP4Node_spec_copy F m head none none with
  | .error e => .error e
  | .ok (m', nh', _) => .ok (m', nh')

/-- Payloads chased from a head (fuel-bounded; link words decode through `addrOfWord`). -/
def _Z9list_copyP4Node_chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
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
        | some v => v :: _Z9list_copyP4Node_chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Edge cases: 3-node copy, singleton, empty, missing head, short block. -/
def _Z9list_copyP4Node_spec_edges : List (Nat × Mem × Option Addr × Option (List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, some [10, 20, 30]),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, some [7]),
   (10, emptyMem, none, some []),
   (10, emptyMem, some 5, none),
   (10, (memAllocData emptyMem [(7 : BitVec 32)]).1, some 0, none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (fresh-chain payloads and untouched-input payloads both match). -/
def _Z9list_copyP4Node_spec_check : Bool :=
  _Z9list_copyP4Node_spec_edges.all fun t =>
    match _Z9list_copyP4Node_spec_fwd t.1 t.2.1 t.2.2.1, t.2.2.2 with
    | .ok (m', nh'), some vs =>
      _Z9list_copyP4Node_chainVals m' nh' 32 == vs && _Z9list_copyP4Node_chainVals m' t.2.2.1 32 == vs
    | .error _, none => true
    | _, _ => false
