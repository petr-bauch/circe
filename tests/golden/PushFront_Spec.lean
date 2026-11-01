-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z10push_frontP4Nodei(head, v)` prepends a fresh `Node` holding `v` to the `head`-rooted chain, returning the fresh cell. Base body reference: the same allocate-store-store-return (cf. emitted `_Z10push_frontP4Nodei_fwd`, `pushFrontFwd` for the entry leg). Allocation is infallible; the old list is never read. -/
def _Z10push_frontP4Nodei_spec_fwd (m : Mem) (head : Option Addr) (v : BitVec 32) :
    Result (Mem × Option Addr) :=
  match memStore (memAlloc m 2).1 (memAlloc m 2).2
      (memAlloc m 2).2 0 v with
  | .error e => .error e
  | .ok m2 =>
    match memStore m2 (memAlloc m 2).2 (memAlloc m 2).2 1
        (linkWord head) with
    | .error e => .error e
    | .ok m3 => .ok (m3, some (memAlloc m 2).2)

/-- Payloads chased from a head (fuel-bounded; link words decode through `addrOfWord`). -/
def _Z10push_frontP4Nodei_chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
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
        | some v => v :: _Z10push_frontP4Nodei_chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Edge cases: 2-chain prepend, singleton prepend, empty-head prepend, dangling-head prepend (never dereferenced), zero payload. -/
def _Z10push_frontP4Nodei_spec_edges : List (Nat × Mem × Option Addr × BitVec 32 × Option (Option Addr × List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData emptyMem [(10 : BitVec 32), 2]).1 [(20 : BitVec 32), 0]).1, some 0, (7 : BitVec 32), some (some 2, [7, 10, 20])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 0, (5 : BitVec 32), some (some 1, [5, 7])),
   (10, emptyMem, none, (9 : BitVec 32), some (some 0, [9])),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, some 5, (5 : BitVec 32), some (some 1, [5])),
   (10, emptyMem, none, (0 : BitVec 32), some (some 0, [0]))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (the fuel slot is unused: the total mirror takes no fuel). -/
def _Z10push_frontP4Nodei_spec_check : Bool :=
  _Z10push_frontP4Nodei_spec_edges.all fun t =>
    match _Z10push_frontP4Nodei_spec_fwd t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok (m', p'), some (q', vs) =>
      p' == q' && _Z10push_frontP4Nodei_chainVals m' p' 32 == vs
    | .error _, none => true
    | _, _ => false
