-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.LinkedList

/-- C++ signature: `_Z10list_mergeP4NodeS0_(a, b)` splices the `a`- and `b`-rooted ascending chains into one ascending chain by relinking, returning the merged head (null only when both inputs are null; the live side otherwise). Base body reference: the seed pick plus the two-cursor chase (cf. emitted `_Z10list_mergeP4NodeS0__fwd`, `listMergeFwd` for the entry leg). Both inputs are ascending and disjoint; the output reuses exactly the input cells (no allocation); dangling links abort loudly; cyclic input exhausts fuel. -/
def _Z10list_mergeP4NodeS0__spec_merge_chase (F : Nat) (m : Mem) (a b : Option Addr)
    (tail : Addr) : Result (Mem × Addr × Option Addr × Option Addr) :=
  match a, b with
  | none, _ => .ok (m, tail, a, b)
  | _, none => .ok (m, tail, a, b)
  | some av, some bv =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      match memFind m av, memFind m bv with
      | some ba, some bb =>
        match memLoad m av ba.tag 0, memLoad m bv bb.tag 0 with
        | .ok va, .ok vb =>
          if vb.slt va then
            match memLoad m bv bb.tag 1 with
            | .error e => .error e
            | .ok wb =>
              match memFind m tail with
              | none => .error .AssertFail
              | some bt =>
                match memStore m tail bt.tag 1 (linkWord (some bv)) with
                | .error e => .error e
                | .ok m' =>
                  _Z10list_mergeP4NodeS0__spec_merge_chase F m' (some av) (addrOfWord wb) bv
          else
            match memLoad m av ba.tag 1 with
            | .error e => .error e
            | .ok wa =>
              match memFind m tail with
              | none => .error .AssertFail
              | some bt =>
                match memStore m tail bt.tag 1 (linkWord (some av)) with
                | .error e => .error e
                | .ok m' =>
                  _Z10list_mergeP4NodeS0__spec_merge_chase F m' (addrOfWord wa) (some bv) av
        | _, _ => .error .AssertFail
      | _, _ => .error .AssertFail

def _Z10list_mergeP4NodeS0__spec_fwd (F : Nat) (m : Mem) (a b : Option Addr) :
    Result (Mem × Option Addr) :=
  match a, b with
  | none, _ => .ok (m, b)
  | _, none => .ok (m, a)
  | some av, some bv =>
    match memFind m av, memFind m bv with
    | some ba, some bb =>
      match memLoad m av ba.tag 0, memLoad m bv bb.tag 0 with
      | .ok va, .ok vb =>
        if vb.slt va then
          match memLoad m bv bb.tag 1 with
          | .error e => .error e
          | .ok wb =>
            match _Z10list_mergeP4NodeS0__spec_merge_chase F m (some av) (addrOfWord wb) bv with
            | .error e => .error e
            | .ok (m', tail', a', b') =>
              match memFind m' tail' with
              | none => .error .AssertFail
              | some bt =>
                match a' with
                | some _ =>
                  match memStore m' tail' bt.tag 1 (linkWord a') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some bv)
                | none =>
                  match memStore m' tail' bt.tag 1 (linkWord b') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some bv)
        else
          match memLoad m av ba.tag 1 with
          | .error e => .error e
          | .ok wa =>
            match _Z10list_mergeP4NodeS0__spec_merge_chase F m (addrOfWord wa) (some bv) av with
            | .error e => .error e
            | .ok (m', tail', a', b') =>
              match memFind m' tail' with
              | none => .error .AssertFail
              | some bt =>
                match a' with
                | some _ =>
                  match memStore m' tail' bt.tag 1 (linkWord a') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some av)
                | none =>
                  match memStore m' tail' bt.tag 1 (linkWord b') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some av)
      | _, _ => .error .AssertFail
    | _, _ => .error .AssertFail

/-- Payloads chased from a head (fuel-bounded; link words decode through `addrOfWord`). -/
def _Z10list_mergeP4NodeS0__chainVals (m : Mem) (head : Option Addr) (F : Nat) : List (BitVec 32) :=
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
        | some v => v :: _Z10list_mergeP4NodeS0__chainVals m (addrOfWord ((b.data[1]?.getD 0))) F

/-- Edge cases: two-chain merge, null side, both null, missing head. -/
def _Z10list_mergeP4NodeS0__spec_edges : List (Nat × Mem × Option Addr × Option Addr × Option (List (BitVec 32))) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(30 : BitVec 32), 0]).1 [(10 : BitVec 32), 1]).1 [(20 : BitVec 32), 0]).1, some 1, some 2, some [10, 20, 30]),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0]).1, none, some 0, some [7]),
   (10, emptyMem, none, none, some []),
   (10, emptyMem, some 5, some 2, none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (merged payloads match). -/
def _Z10list_mergeP4NodeS0__spec_check : Bool :=
  _Z10list_mergeP4NodeS0__spec_edges.all fun t =>
    match _Z10list_mergeP4NodeS0__spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok (m', h'), some vs =>
      _Z10list_mergeP4NodeS0__chainVals m' h' 32 == vs
    | .error _, none => true
    | _, _ => false
