-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Mem.BinaryTree

/-- C signature: `bst_inorder(root, out, cap)` writes the inorder keys of the `root`-rooted BST into `out`, returning the count (or `-1` on stack/out overflow). Base body reference: the same push-pop-emit over the reified three-word nodes (cf. emitted `bst_inorder_fwd`). Dangling links abort loudly; cyclic trees exhaust fuel. -/
def bst_inorder_spec_spine (F : Nat) (m : Mem) (cur : Option Addr)
    (stk : List Addr) (stA : Addr) (stT : Nat) :
    Result (Option (Option Addr × List Addr × Mem)) :=
  match cur with
  | none => .ok (some (none, stk, m))
  | some a =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      if stk.length >= 64 then .ok none
      else
        match memFind m a with
        | none => .error .AssertFail
        | some b =>
          match memLoad m a b.tag 1 with
          | .error e => .error e
          | .ok l =>
            match memStore m stA stT stk.length
                (linkWord (some a)) with
            | .error e => .error e
            | .ok m' =>
              bst_inorder_spec_spine F m' (addrOfWord l)
                (stk ++ [a]) stA stT

def bst_inorder_spec_outer (F : Nat) (m : Mem) (cur : Option Addr)
    (stk : List Addr) (stA : Addr) (stT : Nat)
    (outA : Addr) (outT : Nat) (cap : BitVec 32) (n : BitVec 64) :
    Result (Option (BitVec 64) × Mem) :=
  match F with
  | 0 => .error .AssertFail
  | F + 1 =>
    match bst_inorder_spec_spine F m cur stk stA stT with
    | .error e => .error e
    | .ok none => .ok (none, m)
    | .ok (some (cur', stk', m')) =>
      match cur', stk' with
      | none, [] => .ok (some n, m')
      | _, _ =>
        match stk'.getLast? with
        | none => .error .AssertFail
        | some a =>
          match memFind m' a with
          | none => .error .AssertFail
          | some b =>
            match memLoad m' a b.tag 0, memLoad m' a b.tag 2 with
            | .ok k, .ok r =>
              if n.toNat < (cap.signExtend 64).toNat then
                match memStore m' outA outT n.toNat k with
                | .error e => .error e
                | .ok m'' =>
                  bst_inorder_spec_outer F m'' (addrOfWord r)
                    stk'.dropLast stA stT outA outT cap (n + 1)
              else .ok (none, m')
            | .error e, _ => .error e
            | _, .error e => .error e

def bst_inorder_spec (F : Nat) (m : Mem) (root : Option Addr)
    (outA : Addr) (outT : Nat) (cap : BitVec 32) :
    Result (Option (BitVec 64) × Mem) :=
  let (m1, stA) := memAllocData m (List.replicate 64 0)
  bst_inorder_spec_outer F m1 root [] stA stA outA outT cap 0

/-- Edge cases: empty tree, single node, missing root. -/
def bst_inorder_spec_edges : List (Nat × Mem × Option Addr × Addr × Nat × BitVec 32 × Option (BitVec 64)) :=
  [(10, (memAllocData emptyMem (List.replicate 10 0)).1, none, 0, 0, (10 : BitVec 32), some 0),
   (10, (memAllocData (memAllocData emptyMem [(7 : BitVec 32), 0, 0]).1 (List.replicate 10 0)).1, some 0, 1, 1, (10 : BitVec 32), some 1),
   (10, (memAllocData emptyMem (List.replicate 10 0)).1, some 5, 0, 0, (10 : BitVec 32), none)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge (count only; the missing-root leg fails loud). -/
def bst_inorder_spec_check : Bool :=
  bst_inorder_spec_edges.all fun t =>
    match bst_inorder_spec t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1, t.2.2.2.2.2.2 with
    | .ok (r', _), some wr => r' == wr
    | .error _, none => true
    | _, _ => false

