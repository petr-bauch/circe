-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z11list_appendP4NodeS0_(head, nd)` appends the caller-owned `nd` to the `head`-rooted chain, returning the head (`nd` for the empty list). Base body reference: the same normalize-then-swing insertion (cf. emitted `_Z11list_appendP4NodeS0__fwd`, `listAppendFwd` for the entry leg). Misses abort loudly; cyclic input exhausts fuel. -/
def _Z11list_appendP4NodeS0__spec_tail (F : Nat) (m : Mem) (cur : Option Addr) :
    Result (Mem × Option Addr) :=
  match cur with
  | none => .error .AssertFail
  | some a =>
    match memFind m a with
    | none => .error .AssertFail
    | some b =>
      match memLoad m a b.tag 1 with
      | .error e => .error e
      | .ok w =>
        match addrOfWord w with
        | none => .ok (m, some a)
        | some n =>
          match F with
          | 0 => .error .AssertFail
          | F + 1 => _Z11list_appendP4NodeS0__spec_tail F m (some n)

def _Z11list_appendP4NodeS0__spec_fwd (F : Nat) (m : Mem) (head nd : Option Addr) : Result (Mem × Option Addr) :=
  match nd with
  | none => .error .AssertFail
  | some d =>
    match memFind m d with
    | none => .error .AssertFail
    | some bd =>
      match memStore m d bd.tag 1 (linkWord none) with
      | .error e => .error e
      | .ok m1 =>
        match head with
        | none => .ok (m1, nd)
        | some _ =>
          match _Z11list_appendP4NodeS0__spec_tail F m1 head with
          | .error e => .error e
          | .ok (m2, tail) =>
            match tail with
            | none => .error .AssertFail
            | some t =>
              match memFind m2 t with
              | none => .error .AssertFail
              | some bt =>
                match memStore m2 t bt.tag 1 (linkWord nd) with
                | .error e => .error e
                | .ok m3 => .ok (m3, head)

/-- Payloads chased from a head (fuel-bounded; link words decode through `addrOfWord`). -/
def _Z11list_appendP4NodeS0__chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
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
        | some v => v :: _Z11list_appendP4NodeS0__chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Edge cases: 2-chain append, singleton append, empty-head append, null node, missing head, missing node, short node block. -/
def _Z11list_appendP4NodeS0__spec_edges : List (Nat × Mem × Option Addr × Option Addr × Option (Option Addr × List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(10 : BitVec 32), 2]).1 [(20 : BitVec 32), 0]).1 [(30 : BitVec 32), 0]).1, some 0, some 2, some (some 0, [10, 20, 30])),
   (10, (memAllocData (memAllocData emptyMem [(7 : BitVec 32), 0]).1 [(9 : BitVec 32), 0]).1, some 0, some 1, some (some 0, [7, 9])),
   (10, (memAllocData emptyMem [(5 : BitVec 32), 0]).1, none, some 0, some (some 0, [5])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, none, none),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 5, some 0, none),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, some 9, none),
   (10, (memAllocData emptyMem [(7 : BitVec 32)]).1, none, some 0, none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z11list_appendP4NodeS0__spec_check : Bool :=
  _Z11list_appendP4NodeS0__spec_edges.all fun t =>
    match _Z11list_appendP4NodeS0__spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok (m', p'), some (q', vs) =>
      p' == q' && _Z11list_appendP4NodeS0__chainVals m' p' 32 == vs
    | .error _, none => true
    | _, _ => false
