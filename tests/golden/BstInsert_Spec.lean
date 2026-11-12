-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.BinaryTree

/-- C signature: `bst_insert(root, key)` inserts `key` into the `root`-rooted BST (signed key order), returning the (possibly new) root. Base body reference: the same descend-and-attach on the reified three-word nodes (cf. emitted `bst_insert_fwd`). Dangling links abort loudly; cyclic trees exhaust fuel. -/
def bst_insert_spec_insert (F : Nat) (m : Mem) (cur : Option Addr)
    (key : BitVec 32) (parent : Option Addr)
    (wentLeft : Bool) : Result (Option (Option Addr × Bool)) :=
  match cur with
  | none => .ok (some (parent, wentLeft))
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
          if w == key then .ok none
          else if key.slt w then
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' => bst_insert_spec_insert F m (addrOfWord w') key (some a) true
          else
            match memLoad m a b.tag 2 with
            | .error e => .error e
            | .ok w' => bst_insert_spec_insert F m (addrOfWord w') key (some a) false

def bst_insert_spec (F : Nat) (m : Mem) (root : Option Addr)
    (key : BitVec 32) : Result (Option Addr × Mem) :=
  match bst_insert_spec_insert F m root key none false with
  | .error e => .error e
  | .ok none => .ok (root, m)
  | .ok (some (parent, side)) =>
    let (m1, a) := memAlloc m 3
    match memStore m1 a a 0 key with
    | .error e => .error e
    | .ok m2 =>
      match memStore m2 a a 1 (linkWord none) with
      | .error e => .error e
      | .ok m3 =>
        match memStore m3 a a 2 (linkWord none) with
        | .error e => .error e
        | .ok m4 =>
          match parent with
          | none => .ok (some a, m4)
          | some p =>
            match memFind m4 p with
            | none => .error .AssertFail
            | some b =>
              match memStore m4 p b.tag (if side then 1 else 2)
                  (linkWord (some a)) with
              | .error e => .error e
              | .ok m5 => .ok (root, m5)

/-- Fuel-guarded inorder keys (missing blocks read as empty). -/
def bst_insert_spec_keys (F : Nat) (m : Mem) (cur : Option Addr) : List (BitVec 32) :=
  match cur with
  | none => []
  | some a =>
    match F with
    | 0 => []
    | F + 1 =>
      match memFind m a with
      | none => []
      | some b =>
        match memLoad m a b.tag 0, memLoad m a b.tag 1, memLoad m a b.tag 2 with
        | .ok w, .ok l, .ok r =>
          bst_insert_spec_keys F m (addrOfWord l) ++ [w] ++ bst_insert_spec_keys F m (addrOfWord r)
        | _, _, _ => []

/-- Edge cases: empty insert, dup, attach left/right, missing root. -/
def bst_insert_spec_edges : List (Nat × Mem × Option Addr × BitVec 32 × Option (Option Addr × List (BitVec 32))) :=
  [(10, emptyMem, none, (5 : BitVec 32), some (some 0, [(5 : BitVec 32)])),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(3 : BitVec 32), 0, 0]).1 [(7 : BitVec 32), 0, 0]).1 [(5 : BitVec 32), 1, 2]).1, some 2, (5 : BitVec 32), some (some 2, [(3 : BitVec 32), (5 : BitVec 32), (7 : BitVec 32)])),
   (10, (memAllocData emptyMem [(5 : BitVec 32), 0, 0]).1, some 0, (3 : BitVec 32), some (some 0, [(3 : BitVec 32), (5 : BitVec 32)])),
   (10, (memAllocData emptyMem [(5 : BitVec 32), 0, 0]).1, some 0, (7 : BitVec 32), some (some 0, [(5 : BitVec 32), (7 : BitVec 32)])),
   (10, emptyMem, some 5, (5 : BitVec 32), none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (root identity plus inorder keys; the missing-root leg fails loud). -/
def bst_insert_spec_check : Bool :=
  bst_insert_spec_edges.all fun t =>
    match bst_insert_spec t.1 t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok (r', m'), some (wr, wks) =>
      r' == wr && bst_insert_spec_keys 32 m' r' == wks
    | .error _, none => true
    | _, _ => false
