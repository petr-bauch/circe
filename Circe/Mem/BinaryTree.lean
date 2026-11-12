/-
Circe.Mem.BinaryTree — dynamic-tree memory vocabulary (P1 tree kit):
per-node points-to over the `Model` link codec, the tree-segment
predicate, load/store triples, and the store-outside-footprint
frame lemma.

A `Node = { key : i32, left : Node *, right : Node * }` is one
3-word block: payload at index 0, encoded left link at index 1,
encoded right link at index 2. Null is word `0`; a live link `a`
is word `a + 1` (bump addresses never wrap in the test heaps;
exactness is an explicit side condition, the L-ptr precedent).
-/
import Circe.Mem.Model
import Circe.Mem.Agree

/-! ## Pure model (BTree, shared by the Emit layer) -/

/-- Pure binary tree over 32-bit keys (the search/insert/inorder
    oracle vocabulary). -/
inductive BTree : Type
  | leaf : BTree
  | node : BitVec 32 → BTree → BTree → BTree

/-- Inorder flatten (the traversal oracle). -/
def BTree.flatten : BTree → List (BitVec 32)
  | .leaf => []
  | .node k l r => l.flatten ++ [k] ++ r.flatten

/-- Node count (the descent-fuel measure). -/
def BTree.bsize : BTree → Nat
  | .leaf => 0
  | .node _ l r => l.bsize + r.bsize + 1

/-- BST descent membership test (mirrors the C loop: `==` hit,
    `slt` chooses the side). -/
def BTree.contains : BTree → BitVec 32 → Bool
  | .leaf, _ => false
  | .node k l r, x =>
    if x == k then true else if x.slt k then l.contains x else r.contains x

/-- Functional insert, set semantics (duplicate key is a no-op,
    never allocates — the corpus contract). -/
def BTree.binsert : BTree → BitVec 32 → BTree
  | .leaf, x => .node x .leaf .leaf
  | .node k l r, x =>
    if x == k then .node k l r
    else if x.slt k then .node k (l.binsert x) r
    else .node k l (r.binsert x)

/-- Lower-bound fact: everything below `k` starts above `lo`
    (`none` is unbounded). -/
def boundLo (lo : Option (BitVec 32)) (k : BitVec 32) : Prop :=
  match lo with
  | none => True
  | some b => (b.slt k) = true

/-- Upper-bound fact: everything below `k` stays below `hi`. -/
def boundHi (k : BitVec 32) (hi : Option (BitVec 32)) : Prop :=
  match hi with
  | none => True
  | some b => (k.slt b) = true

/-- BST invariant with exclusive `slt` bounds (duplicates go
    nowhere: a key already present is found by descent, so
    insert is the identity on it). -/
inductive Bst : Option (BitVec 32) → Option (BitVec 32) → BTree → Prop
  | leaf (lo hi) : Bst lo hi .leaf
  | node {lo hi k l r} : boundLo lo k → boundHi k hi →
      Bst lo (some k) l → Bst (some k) hi r →
      Bst lo hi (.node k l r)

/-- Sortedness over `slt` (the inorder contract vocabulary). -/
def BTree.Sorted : List (BitVec 32) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => (a.slt b) = true ∧ BTree.Sorted (b :: rest)

/-- `slt` transitivity (via `toInt` + `omega`, the
    `sortedInsert_slt_trans` precedent restated locally to avoid
    a new import). -/
theorem bst_slt_trans {x y z : BitVec 32}
    (hxy : (x.slt y) = true) (hyz : (y.slt z) = true) :
    (x.slt z) = true := by
  rw [BitVec.slt_eq_decide] at hxy hyz ⊢
  simp only [decide_eq_true_eq] at hxy hyz ⊢
  omega

/-- `slt` asymmetry (via `toInt` + `omega`, restated locally). -/
theorem bst_slt_asymm {x y : BitVec 32}
    (h : (x.slt y) = true) : (y.slt x) = false := by
  rw [BitVec.slt_eq_decide] at h ⊢
  simp only [decide_eq_true_eq] at h
  simp only [decide_eq_false_iff_not]
  omega

/-- `slt` irreflexivity (via `toInt`, restated locally). -/
theorem bst_slt_irrefl (x : BitVec 32) : (x.slt x) = false := by
  rw [BitVec.slt_eq_decide]
  simp

/-- Sorted lists append: every head element below every tail
    element (the inorder concatenation step). -/
theorem BTree.Sorted.append {l r : List (BitVec 32)}
    (hl : BTree.Sorted l) (hr : BTree.Sorted r)
    (hlt : ∀ a ∈ l, ∀ b ∈ r, (a.slt b) = true) :
    BTree.Sorted (l ++ r) := by
  induction l with
  | nil =>
    simpa using hr
  | cons a l' ih =>
    cases l' with
    | nil =>
      cases r with
      | nil => exact True.intro
      | cons b r' =>
        have hab : (a.slt b) = true :=
          hlt a (List.mem_cons.mpr (Or.inl rfl)) b
            (List.mem_cons.mpr (Or.inl rfl))
        exact ⟨hab, hr⟩
    | cons b l'' =>
      obtain ⟨hab, hl'⟩ := hl
      have hlt' : ∀ x ∈ b :: l'', ∀ y ∈ r, (x.slt y) = true := by
        intro x hx y hy
        exact hlt x (List.mem_cons.mpr (Or.inr hx)) y hy
      exact ⟨hab, ih hl' hlt'⟩

/-- Flatten elements respect the subtree bounds (the bound
    half of the search correctness argument). -/
theorem BTree.mem_flatten_bounds {t : BTree} {lo hi x}
    (hmem : x ∈ t.flatten) (h : Bst lo hi t) :
    boundLo lo x ∧ boundHi x hi := by
  induction t generalizing lo hi with
  | leaf =>
    cases h
    rw [BTree.flatten] at hmem
    exact False.elim (List.not_mem_nil hmem)
  | node k l r ihl ihr =>
    cases h with
    | node hloB hhiB hl hr =>
      rw [BTree.flatten, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · rw [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | rfl
        · obtain ⟨hlo, hhi⟩ := ihl hmem hl
          refine ⟨hlo, ?_⟩
          cases hi with
          | none => exact True.intro
          | some b =>
            simp only [boundHi] at hhiB ⊢
            exact bst_slt_trans hhi hhiB
        · exact ⟨hloB, hhiB⟩
      · obtain ⟨hlo, hhi⟩ := ihr hmem hr
        refine ⟨?_, hhi⟩
        cases lo with
        | none => exact True.intro
        | some b =>
          simp only [boundLo] at hloB ⊢
          exact bst_slt_trans hloB hlo

/-- Descent membership agrees with flatten membership inside
    the bounds (the search oracle equation). -/
theorem BTree.contains_iff_mem_flatten {t : BTree} {lo hi x}
    (h : Bst lo hi t) (hlo : boundLo lo x) (hhi : boundHi x hi) :
    (t.contains x) = (x ∈ t.flatten) := by
  induction t generalizing lo hi with
  | leaf =>
    cases h
    simp [BTree.contains, BTree.flatten]
  | node k l r ihl ihr =>
    cases h with
    | node hloB hhiB hl hr =>
      simp only [BTree.contains, BTree.flatten, List.mem_append,
        List.mem_singleton]
      by_cases heq : (x == k) = true
      · have hxk : x = k := beq_iff_eq.mp heq
        simp [hxk]
      · have hne : x ≠ k := fun hcon => heq (by rw [hcon]; simp)
        simp only [heq, hne, Bool.false_eq_true, or_false]
        by_cases hslt : (x.slt k) = true
        · simp only [hslt, ite_true, ite_false]
          rw [ihl hl hlo (by simpa [boundHi] using hslt)]
          apply propext
          constructor
          · intro hmem
            exact Or.inl hmem
          · intro hmem
            rcases hmem with hmem | hmem
            · exact hmem
            · obtain ⟨hlo', _⟩ := BTree.mem_flatten_bounds hmem hr
              simp only [boundLo] at hlo'
              have hcon : (k.slt x) = false := bst_slt_asymm hslt
              rw [hcon] at hlo'
              exact absurd hlo' (by simp)
        · have hsltF : (x.slt k) = false := by
            cases h : (x.slt k) with
            | true => exact absurd h hslt
            | false => rfl
          have hgt : (k.slt x) = true := by
            by_cases hcon : (k.slt x) = true
            · exact hcon
            · have hconF : (k.slt x) = false := by
                cases h : (k.slt x) with
                | true => exact absurd h hcon
                | false => rfl
              have hkx : k = x := by
                rw [BitVec.slt_eq_decide] at hsltF hconF
                simp only [decide_eq_false_iff_not] at hsltF hconF
                have : k.toInt = x.toInt := by omega
                exact BitVec.eq_of_toInt_eq this
              exact absurd hkx.symm hne
          simp only [hsltF, Bool.false_eq_true, ite_false]
          rw [ihr hr (by simpa [boundLo] using hgt) hhi]
          apply propext
          constructor
          · intro hmem
            exact Or.inr hmem
          · intro hmem
            rcases hmem with hmem | hmem
            · obtain ⟨_, hhi'⟩ := BTree.mem_flatten_bounds hmem hl
              simp only [boundHi] at hhi'
              rw [hhi'] at hsltF
              exact absurd hsltF (by simp)
            · exact hmem

/-- BST inorder is sorted (the inorder contract vocabulary). -/
theorem BTree.flatten_sorted_of_bst {t : BTree}
    (h : Bst none none t) : BTree.Sorted t.flatten := by
  have gen : ∀ (lo hi : Option (BitVec 32)) (u : BTree),
      Bst lo hi u → BTree.Sorted u.flatten := by
    intro lo hi u hu
    induction u generalizing lo hi with
    | leaf =>
      cases hu
      exact True.intro
    | node k l r ihl ihr =>
      cases hu with
      | node hloB hhiB hl hr =>
        have hleft : BTree.Sorted (l.flatten ++ [k]) :=
          BTree.Sorted.append (ihl lo (some k) hl) True.intro
            (fun a ha b hb => by
              simp only [List.mem_singleton] at hb
              subst hb
              obtain ⟨_, hhi⟩ := BTree.mem_flatten_bounds ha hl
              simpa [boundHi] using hhi)
        refine BTree.Sorted.append hleft (ihr (some k) hi hr)
          (fun a ha b hb => ?_)
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with haL | rfl
        · obtain ⟨_, hhiA⟩ := BTree.mem_flatten_bounds haL hl
          obtain ⟨hloB', _⟩ := BTree.mem_flatten_bounds hb hr
          simp only [boundHi] at hhiA
          simp only [boundLo] at hloB'
          exact bst_slt_trans hhiA hloB'
        · obtain ⟨hloB', _⟩ := BTree.mem_flatten_bounds hb hr
          simpa [boundLo] using hloB'
  exact gen none none t h

/-- Insert preserves the BST invariant inside the bounds. -/
theorem BTree.binsert_bst {t : BTree} {lo hi x}
    (h : Bst lo hi t) (hlo : boundLo lo x) (hhi : boundHi x hi) :
    Bst lo hi (BTree.binsert t x) := by
  induction t generalizing lo hi with
  | leaf =>
    cases h
    simp only [BTree.binsert]
    exact Bst.node hlo hhi (Bst.leaf _ _) (Bst.leaf _ _)
  | node k l r ihl ihr =>
    cases h with
    | node hloB hhiB hl hr =>
      simp only [BTree.binsert]
      by_cases heq : (x == k) = true
      · simp only [heq, ite_true]
        exact Bst.node hloB hhiB hl hr
      · simp only [heq]
        by_cases hslt : (x.slt k) = true
        · simp only [hslt, ite_true]
          exact Bst.node hloB hhiB
            (ihl hl hlo (by simpa [boundHi] using hslt)) hr
        · have hsltF : (x.slt k) = false := by
            cases h : (x.slt k) with
            | true => exact absurd h hslt
            | false => rfl
          have hgt : (k.slt x) = true := by
            by_cases hcon : (k.slt x) = true
            · exact hcon
            · have hconF : (k.slt x) = false := by
                cases h : (k.slt x) with
                | true => exact absurd h hcon
                | false => rfl
              have hkx : k = x := by
                rw [BitVec.slt_eq_decide] at hsltF hconF
                simp only [decide_eq_false_iff_not] at hsltF hconF
                have : k.toInt = x.toInt := by omega
                exact BitVec.eq_of_toInt_eq this
              have hxk : x = k := hkx.symm
              have hxx : (x == k) = true := by rw [hxk]; simp
              exact absurd hxx heq
          simp only [hsltF, Bool.false_eq_true, ite_false]
          exact Bst.node hloB hhiB hl
            (ihr hr (by simpa [boundLo] using hgt) hhi)

/-- Insert touches membership exactly at the key (set
    semantics; needs no invariant — membership is
    proof-irrelevant). -/
theorem BTree.mem_flatten_binsert {t : BTree} {x y : BitVec 32} :
    y ∈ (BTree.binsert t x).flatten ↔ y = x ∨ y ∈ t.flatten := by
  induction t with
  | leaf =>
    simp [BTree.binsert, BTree.flatten]
  | node k l r ihl ihr =>
    by_cases heq : (x == k) = true
    · have hdup : BTree.binsert (BTree.node k l r) x =
          BTree.node k l r := by
        simp only [BTree.binsert]
        rw [ite_eq_left heq]
      have hxk : x = k := beq_iff_eq.mp heq
      rw [hdup, hxk]
      constructor
      · intro hmem
        exact Or.inr hmem
      · intro hmem
        rcases hmem with rfl | hmem
        · simp [BTree.flatten]
        · exact hmem
    · simp only [BTree.binsert]
      rw [ite_eq_right heq]
      by_cases hslt : (x.slt k) = true
      · rw [ite_eq_left hslt]
        simp only [BTree.flatten, List.mem_append,
          List.mem_singleton]
        rw [ihl]
        simp only [or_assoc]
      · have hsltF : (x.slt k) = false := by
          cases h : (x.slt k) with
          | true => exact absurd h hslt
          | false => rfl
        have hnslt : ¬((x.slt k) = true) := by
          rw [hsltF]
          exact Bool.false_ne_true
        rw [ite_eq_right hnslt]
        simp only [BTree.flatten, List.mem_append,
          List.mem_singleton]
        rw [ihr]
        simp only [or_assoc, or_comm, or_left_comm]
/-! ## Memory vocabulary -/

/-- A live tree node block: payload `k` at index 0, encoded
    left link at index 1, encoded right link at index 2 (a
    `cellsAt` specialization, so the array kit's store equation
    applies unchanged). -/
def nodeAt3 (m : Mem) (a t : Nat) (k : BitVec 32)
    (l r : Option Addr) : Prop :=
  cellsAt m a t [k, linkWord l, linkWord r]

/-- Key read leg. -/
theorem nodeLoadKey {m : Mem} {a t : Nat} {k : BitVec 32}
    {l r : Option Addr} (h : nodeAt3 m a t k l r) :
    memLoad m a t 0 = .ok k := by
  unfold nodeAt3 at h
  exact memLoad_cellsAt m a t 0 [k, linkWord l, linkWord r] k h rfl

/-- Left-link read leg. -/
theorem nodeLoadLeft {m : Mem} {a t : Nat} {k : BitVec 32}
    {l r : Option Addr} (h : nodeAt3 m a t k l r) :
    memLoad m a t 1 = .ok (linkWord l) := by
  unfold nodeAt3 at h
  exact memLoad_cellsAt m a t 1 [k, linkWord l, linkWord r]
    (linkWord l) h rfl

/-- Right-link read leg. -/
theorem nodeLoadRight {m : Mem} {a t : Nat} {k : BitVec 32}
    {l r : Option Addr} (h : nodeAt3 m a t k l r) :
    memLoad m a t 2 = .ok (linkWord r) := by
  unfold nodeAt3 at h
  exact memLoad_cellsAt m a t 2 [k, linkWord l, linkWord r]
    (linkWord r) h rfl

/-- Left-link swing equation (store leg, `List.set` form). -/
theorem nodeStoreLeft {m : Mem} {a t : Nat} {k : BitVec 32}
    {l r : Option Addr} (h : nodeAt3 m a t k l r)
    (l' : Option Addr) :
    memStore m a t 1 (linkWord l') =
      .ok ⟨m.next,
        (a, ⟨t, true, ([k, linkWord l, linkWord r]).set 1
          (linkWord l')⟩) ::
          m.blocks,
        m.blocks64⟩ := by
  unfold nodeAt3 at h
  exact memStore_cellsAt m a t 1 [k, linkWord l, linkWord r]
    (linkWord l') h (by simp)

/-- The swung node satisfies `nodeAt3` with the new left
    link. -/
theorem nodeStoreLeft_nodeAt3 {m : Mem} {a t : Nat}
    {k : BitVec 32} {l r l' : Option Addr} {m' : Mem}
    (h : nodeAt3 m a t k l r)
    (hstore : memStore m a t 1 (linkWord l') = .ok m') :
    nodeAt3 m' a t k l' r := by
  unfold nodeAt3 at h ⊢
  have hc := memFind_cellsAt_store m a t 1
    [k, linkWord l, linkWord r] (linkWord l') m' h
    (by simp) hstore
  have hset : ([k, linkWord l, linkWord r]).set 1
      (linkWord l') = [k, linkWord l', linkWord r] := by simp
  rw [hset] at hc
  exact hc

/-- Right-link swing equation (store leg, `List.set`
    form). -/
theorem nodeStoreRight {m : Mem} {a t : Nat} {k : BitVec 32}
    {l r : Option Addr} (h : nodeAt3 m a t k l r)
    (r' : Option Addr) :
    memStore m a t 2 (linkWord r') =
      .ok ⟨m.next,
        (a, ⟨t, true, ([k, linkWord l, linkWord r]).set 2
          (linkWord r')⟩) ::
          m.blocks,
        m.blocks64⟩ := by
  unfold nodeAt3 at h
  exact memStore_cellsAt m a t 2 [k, linkWord l, linkWord r]
    (linkWord r') h (by simp)

/-- The swung node satisfies `nodeAt3` with the new right
    link. -/
theorem nodeStoreRight_nodeAt3 {m : Mem} {a t : Nat}
    {k : BitVec 32} {l r r' : Option Addr} {m' : Mem}
    (h : nodeAt3 m a t k l r)
    (hstore : memStore m a t 2 (linkWord r') = .ok m') :
    nodeAt3 m' a t k l r' := by
  unfold nodeAt3 at h ⊢
  have hc := memFind_cellsAt_store m a t 2
    [k, linkWord l, linkWord r] (linkWord r') m' h
    (by simp) hstore
  have hset : ([k, linkWord l, linkWord r]).set 2
      (linkWord r') = [k, linkWord l, linkWord r'] := by simp
  rw [hset] at hc
  exact hc

/-- Naming helper: expose the payload and both links (the
    `nodeAt_parts` precedent — the `rfl`s substitute the
    inaccessible originals away). -/
theorem nodeAt3_parts {m : Mem} {a : Addr} {t : Nat} {k : BitVec 32}
    {l r : Option Addr} (h : nodeAt3 m a t k l r) :
    ∃ k' l' r', k' = k ∧ l' = l ∧ r' = r :=
  ⟨k, l, r, rfl, rfl, rfl⟩

/-- Naming helper: expose the block tag. -/
theorem nodeAt3_tag {m : Mem} {a : Addr} {t : Nat} {k : BitVec 32}
    {l r : Option Addr} (h : nodeAt3 m a t k l r) : ∃ t', t' = t :=
  ⟨t, rfl⟩

/-- Link decode inverts link encode (roundtrip for either
    tree link, under the heap exactness bound; no node fact
    needed — only allocation of the target). -/
theorem nodeAt3_link_roundtrip {m : Mem} {n : Option Addr}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (halloc : ∀ c', n = some c' → (memFind m c').isSome = true) :
    addrOfWord (linkWord n) = n := by
  cases n with
  | none => exact addrOfWord_linkWord_none
  | some c' => exact addrOfWord_linkWord_some (hex c' (halloc c' rfl))

/-- Membership in the tree footprint (both subtrees). -/
inductive TreeSegMem {m : Mem} : Option Addr → Addr → Prop
  | here {a t k l r} : nodeAt3 m a t k l r →
    TreeSegMem (some a) a
  | left {s a t k l r} : nodeAt3 m s t k l r →
    TreeSegMem (m := m) l a → TreeSegMem (some s) a
  | right {s a t k l r} : nodeAt3 m s t k l r →
    TreeSegMem (m := m) r a → TreeSegMem (some s) a

/-- The tree segment from `s` holding `t`: each step pins one
    node, then continues in both links. Inherently acyclic — a
    cyclic heap cannot satisfy it for a finite `BTree`. -/
inductive TreeSeg (m : Mem) : Option Addr → BTree → Prop
  | nil : TreeSeg m none .leaf
  | cons {a t k l r tl tr} : nodeAt3 m a t k l r →
    TreeSeg m l tl → TreeSeg m r tr →
    TreeSeg m (some a) (.node k tl tr)

/-- A segment starting at `some c` allocates `c`. -/
theorem TreeSeg_head_alloc {m : Mem} {c : Addr}
    {t : BTree} (h : TreeSeg m (some c) t) :
    (memFind m c).isSome = true := by
  cases h with
  | cons h3 _ _ =>
    unfold nodeAt3 cellsAt at h3
    simp [h3]

/-- Storing outside the footprint preserves the segment (the
    frame lemma: a swing at the head leaves every non-member,
    hence both subtrees, untouched). -/
theorem TreeSeg.store_other {m : Mem} {s : Option Addr}
    {t : BTree} (h : TreeSeg m s t)
    {a' tg i : Nat} {x : BitVec 32} {m' : Mem}
    (hstore : memStore m a' tg i x = .ok m')
    (hout : ∀ a, TreeSegMem (m := m) s a → a ≠ a') :
    TreeSeg m' s t := by
  revert hstore hout m'
  induction h with
  | nil =>
    intro m' hstore hout
    exact .nil
  | cons hnode _ _ ihl ihr =>
    intro m' hstore hout
    apply TreeSeg.cons
    · unfold nodeAt3 cellsAt at hnode ⊢
      exact (memFind_memStore_other _ _ _ _ _ _ _ hstore
        (hout _ (.here hnode))).trans hnode
    · exact ihl hstore (fun b hb => hout b (.left hnode hb))
    · exact ihr hstore (fun b hb => hout b (.right hnode hb))

/-! ## Pure explicit-stack inorder (step-5 oracle algebra) -/

/-- Pending-right frame of the explicit inorder stack: the
    popped node's key plus its still-unvisited right subtree
    (the C loop pushes addresses; the memory layer maps each
    frame to its `TreeSeg` subtree). -/
abbrev InorderFrame := BitVec 32 × BTree

/-- Push the left spine of `t` onto `s` (the inner `while`:
    descend left, pushing each ancestor). -/
def pushSpine : BTree → List InorderFrame → List InorderFrame
  | .leaf, s => s
  | .node k l r, s => pushSpine l ((k, r) :: s)

/-- Stack cost: pending nodes including their right subtrees.
    Popping drops the frame's own slot, so the cost strictly
    decreases across a pop-push step. -/
def stackCost : List InorderFrame → Nat
  | [] => 0
  | (_, r) :: s => r.bsize + 1 + stackCost s

/-- Pushing a spine adds exactly the subtree's node count. -/
theorem pushSpine_cost (t : BTree) (s : List InorderFrame) :
    stackCost (pushSpine t s) = t.bsize + stackCost s := by
  induction t generalizing s with
  | leaf =>
    simp [pushSpine, BTree.bsize, stackCost]
  | node k l r ihl _ =>
    simp only [pushSpine, BTree.bsize]
    rw [ihl]
    simp only [stackCost]
    omega

/-- Pop-and-emit drain with pop fuel (structural on `F`, so no
    termination proof): pop the key, push its right spine,
    repeat. Fuel counts pops; pushes are free. -/
def drainF : Nat → List InorderFrame → List (BitVec 32)
  | _, [] => []
  | 0, _ :: _ => []
  | F + 1, (k, r) :: s => k :: drainF F (pushSpine r s)

/-- The drain at exactly its stack cost (the canonical
    unfueled reading). -/
def drain (s : List InorderFrame) : List (BitVec 32) :=
  drainF (stackCost s) s

/-- Pop equation for `drain` (the outer-loop step). -/
theorem drain_cons (k : BitVec 32) (r : BTree) (s : List InorderFrame) :
    drain ((k, r) :: s) = k :: drain (pushSpine r s) := by
  have hcost : stackCost ((k, r) :: s) = (r.bsize + stackCost s) + 1 := by
    simp only [stackCost]
    omega
  simp only [drain, hcost, drainF, pushSpine_cost]

/-- Draining a pushed spine emits the subtree flatten first
    (the inorder stack invariant, pure half). -/
theorem drain_pushSpine (t : BTree) (s : List InorderFrame) :
    drain (pushSpine t s) = t.flatten ++ drain s := by
  induction t generalizing s with
  | leaf =>
    simp [pushSpine, BTree.flatten]
  | node k l r ihl ihr =>
    simp only [pushSpine]
    rw [ihl, drain_cons, ihr, BTree.flatten]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Whole-tree traversal: draining the pushed spine of `t`
    over the empty stack is exactly the flatten. -/
theorem drain_pushSpine_nil (t : BTree) :
    drain (pushSpine t []) = t.flatten := by
  rw [drain_pushSpine]
  simp [drain, drainF, stackCost]