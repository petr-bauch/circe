-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z11list_filterP4Nodei(head, v)` erases every `Node` holding `v` from the `head`-rooted chain, freeing each victim and returning the (possibly new) head; survivors keep order and a miss returns the head untouched. Base body reference: the same sweep-unlink-free loop (cf. emitted `_Z11list_filterP4Nodei_fwd`, `listFilterFwd` for the entry leg). Misses on a valid chain succeed; dangling links abort loudly; cyclic input exhausts fuel. -/
def _Z11list_filterP4Nodei_spec_filter (F : Nat) (m : Mem) (head prev cur : Option Addr)
    (v : BitVec 32) : Result (Mem × Option Addr) :=
  match cur with
  | none => .ok (m, head)
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
          if w == v then
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' =>
              match prev with
              | none =>
                match memFree m a b.tag with
                | .error e => .error e
                | .ok m1 =>
                  _Z11list_filterP4Nodei_spec_filter F m1 (addrOfWord w') none (addrOfWord w') v
              | some p =>
                match memFind m p with
                | none => .error .AssertFail
                | some bp =>
                  match memStore m p bp.tag 1 w' with
                  | .error e => .error e
                  | .ok m1 =>
                    match memFree m1 a b.tag with
                    | .error e => .error e
                    | .ok m2 => _Z11list_filterP4Nodei_spec_filter F m2 head (some p) (addrOfWord w') v
          else
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' => _Z11list_filterP4Nodei_spec_filter F m head (some a) (addrOfWord w') v

def _Z11list_filterP4Nodei_spec_fwd (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) : Result (Mem × Option Addr) :=
  _Z11list_filterP4Nodei_spec_filter F m head none head v

/-- Payloads chased from a head (fuel-bounded; link words decode through `addrOfWord`). -/
def _Z11list_filterP4Nodei_chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
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
        | some v => v :: _Z11list_filterP4Nodei_chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Edge cases: head-hit, interior-hit, all-match, miss, empty, singleton-hit, singleton-miss, missing head. -/
def _Z11list_filterP4Nodei_spec_edges : List (Nat × Mem × Option Addr × BitVec 32 × Option (Option Addr × List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, (10 : BitVec 32), some (some 1, [20, 30])),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, (20 : BitVec 32), some (some 2, [10, 30])),
   (10, (memAllocData (memAllocData emptyMem [(7 : BitVec 32), 0]).1 [(7 : BitVec 32), 1]).1, some 1, (7 : BitVec 32), some (none, [])),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(20 : BitVec 32), 1]).1 [(10 : BitVec 32), 2]).1, some 2, (99 : BitVec 32), some (some 2, [10, 20, 30])),
   (10, emptyMem, none, (5 : BitVec 32), some (none, [])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, (7 : BitVec 32), some (none, [])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, (5 : BitVec 32), some (some 0, [7])),
   (10, emptyMem, some 5, (5 : BitVec 32), none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z11list_filterP4Nodei_spec_check : Bool :=
  _Z11list_filterP4Nodei_spec_edges.all fun t =>
    match _Z11list_filterP4Nodei_spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok (m', p'), some (q', vs) =>
      p' == q' && _Z11list_filterP4Nodei_chainVals m' p' 32 == vs
    | .error _, none => true
    | _, _ => false
