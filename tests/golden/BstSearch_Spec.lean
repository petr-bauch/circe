-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.BinaryTree

/-- C signature: `bst_search(root, key)` returns 1 iff `key` occurs in the `root`-rooted BST (signed key order), else 0; the tree is never modified. Base body reference: the same read-cursor descent on the reified three-word nodes (cf. emitted `bst_search_fwd`). Dangling links abort loudly; cyclic trees exhaust fuel. -/
def bst_search_spec_search (F : Nat) (m : Mem) (cur : Option Addr)
    (key : BitVec 32) : Result (Option Addr) :=
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
          if w == key then .ok (some a)
          else if key.slt w then
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' => bst_search_spec_search F m (addrOfWord w') key
          else
            match memLoad m a b.tag 2 with
            | .error e => .error e
            | .ok w' => bst_search_spec_search F m (addrOfWord w') key

def bst_search_spec_fwd (F : Nat) (m : Mem) (root : Option Addr)
    (key : BitVec 32) : Result Nat :=
  match bst_search_spec_search F m root key with
  | .error e => .error e
  | .ok (some _) => .ok 1
  | .ok none => .ok 0

/-- Edge cases: root/left/right hits, left/right misses, empty input, singleton hit/miss, missing root. -/
def bst_search_spec_edges : List (Nat × Mem × Option Addr × BitVec 32 × Result Nat) :=
  [(10, (memAllocData (memAllocData (memAllocData emptyMem [(3 : BitVec 32), 0, 0]).1 [(7 : BitVec 32), 0, 0]).1 [(5 : BitVec 32), 1, 2]).1, some 2, (5 : BitVec 32), .ok 1),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(3 : BitVec 32), 0, 0]).1 [(7 : BitVec 32), 0, 0]).1 [(5 : BitVec 32), 1, 2]).1, some 2, (3 : BitVec 32), .ok 1),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(3 : BitVec 32), 0, 0]).1 [(7 : BitVec 32), 0, 0]).1 [(5 : BitVec 32), 1, 2]).1, some 2, (7 : BitVec 32), .ok 1),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(3 : BitVec 32), 0, 0]).1 [(7 : BitVec 32), 0, 0]).1 [(5 : BitVec 32), 1, 2]).1, some 2, (9 : BitVec 32), .ok 0),
   (10, (memAllocData (memAllocData (memAllocData emptyMem [(3 : BitVec 32), 0, 0]).1 [(7 : BitVec 32), 0, 0]).1 [(5 : BitVec 32), 1, 2]).1, some 2, (1 : BitVec 32), .ok 0),
   (10, emptyMem, none, (5 : BitVec 32), .ok 0),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0, 0]).1, some 0, (7 : BitVec 32), .ok 1),
   (10, (memAllocData emptyMem [(7 : BitVec 32), 0, 0]).1, some 0, (5 : BitVec 32), .ok 0),
   (10, emptyMem, some 5, (5 : BitVec 32), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (hit returns 1, miss returns 0, missing root fails loud). -/
def bst_search_spec_check : Bool :=
  bst_search_spec_edges.all fun t =>
    match bst_search_spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1, t.2.2.2.2 with
    | .ok n, .ok m => n == m
    | .error _, .error _ => true
    | _, _ => false
