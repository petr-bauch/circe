/-
Circe.Mem.LinkedList — dynamic-list memory vocabulary (L2): link
encoding, per-node points-to, the list-segment predicate, field
load/store triples, and the store-outside-segment frame lemma.

A `Node = { val : i32, next : Node * }` is one 2-word block:
payload at index 0, encoded link at index 1. Null is word `0`;
a live link `a` is word `a + 1` (bump addresses never wrap in
the test heaps; exactness is an explicit side condition).
-/
import Circe.Mem.Model
import Circe.Mem.Agree

/-- Link encoding: null is the zero word, a live link `a` is the
    word `a + 1` (so every live link word is nonzero below
    `2 ^ 32`). -/
def linkWord : Option Addr → BitVec 32
  | none => 0
  | some a => BitVec.ofNat 32 (a + 1)

theorem linkWord_none : linkWord none = 0 := rfl

theorem linkWord_some (a : Addr) :
    linkWord (some a) = BitVec.ofNat 32 (a + 1) := rfl

/-- A live link word is nonzero (exactness side condition). -/
theorem linkWord_some_ne_zero {a : Addr} (h : a + 1 < 2 ^ 32) :
    linkWord (some a) ≠ 0 := by
  rw [linkWord_some]
  intro heq
  have hto := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at hto
  have hz : BitVec.toNat (0 : BitVec 32) = 0 := by decide
  rw [hz] at hto
  omega

/-- Link words are injective on in-range addresses. -/
theorem linkWord_some_inj {a b : Addr}
    (ha : a + 1 < 2 ^ 32) (hb : b + 1 < 2 ^ 32)
    (h : linkWord (some a) = linkWord (some b)) : a = b := by
  rw [linkWord_some, linkWord_some] at h
  have hto := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] at hto
  exact Nat.add_right_cancel hto

/-- Null never collides with a live link. -/
theorem linkWord_none_ne_some {a : Addr} (h : a + 1 < 2 ^ 32) :
    linkWord none ≠ linkWord (some a) := by
  rw [linkWord_none]
  exact Ne.symm (linkWord_some_ne_zero h)

/-- A live node block: payload `v` at index 0, encoded link at
    index 1 (a `cellsAt` specialization, so the array kit's store
    equation applies unchanged). -/
def nodeAt (m : Mem) (a t : Nat) (v : BitVec 32)
    (n : Option Addr) : Prop :=
  cellsAt m a t [v, linkWord n]

/-- Payload read leg. -/
theorem nodeLoadVal {m : Mem} {a t : Nat} {v : BitVec 32}
    {n : Option Addr} (h : nodeAt m a t v n) :
    memLoad m a t 0 = .ok v :=
  memLoad_cellsAt m a t 0 [v, linkWord n] v h rfl

/-- Link read leg. -/
theorem nodeLoadNext {m : Mem} {a t : Nat} {v : BitVec 32}
    {n : Option Addr} (h : nodeAt m a t v n) :
    memLoad m a t 1 = .ok (linkWord n) :=
  memLoad_cellsAt m a t 1 [v, linkWord n] (linkWord n) h rfl

/-- Link swing equation (store leg, `List.set` form like
    `memStore_cellsAt`). -/
theorem nodeStoreNext {m : Mem} {a t : Nat} {v : BitVec 32}
    {n : Option Addr} (h : nodeAt m a t v n)
    (n' : Option Addr) :
    memStore m a t 1 (linkWord n') =
      .ok ⟨m.next,
        (a, ⟨t, true, ([v, linkWord n]).set 1 (linkWord n')⟩) ::
          m.blocks,
        m.blocks64⟩ := by
  unfold nodeAt at h
  exact memStore_cellsAt m a t 1 [v, linkWord n] (linkWord n') h
    (by simp)

/-- The swung node satisfies `nodeAt` with the new link. -/
theorem nodeStoreNext_nodeAt {m : Mem} {a t : Nat}
    {v : BitVec 32} {n n' : Option Addr} {m' : Mem}
    (h : nodeAt m a t v n)
    (hstore : memStore m a t 1 (linkWord n') = .ok m') :
    nodeAt m' a t v n' := by
  unfold nodeAt at h ⊢
  have hc := memFind_cellsAt_store m a t 1 [v, linkWord n]
    (linkWord n') m' h (by simp) hstore
  have hset : ([v, linkWord n]).set 1 (linkWord n') =
      [v, linkWord n'] := by simp
  rw [hset] at hc
  exact hc

/-- The list segment from `s` holding payloads `vs`: each step pins
    one node, then continues at its link. Inherently acyclic — a
    cyclic heap cannot satisfy it for a finite `vs`. -/
inductive ListSeg (m : Mem) : Option Addr → List (BitVec 32) → Prop
  | nil : ListSeg m none []
  | cons {a t v n vs} : nodeAt m a t v n → ListSeg m n vs →
      ListSeg m (some a) (v :: vs)

/-- Membership in the segment's address footprint. -/
inductive SegMem {m : Mem} : Option Addr → Addr → Prop
  | here {a t v n} : nodeAt m a t v n → SegMem (some a) a
  | there {s a t v n} : nodeAt m s t v n → SegMem n a →
      SegMem (some s) a

/-- An empty payload list starts at null. -/
theorem ListSeg_nil_start {m : Mem} {s : Option Addr}
    (h : ListSeg m s []) : s = none := by
  cases h with
  | nil => rfl

/-- Storing outside the segment footprint preserves it (the frame
    lemma: a swing at the head leaves every non-member, hence the
    tail segment, untouched). -/
theorem ListSeg.store_other {m : Mem} {s : Option Addr}
    {vs : List (BitVec 32)} (h : ListSeg m s vs)
    {a' t i : Nat} {x : BitVec 32} {m' : Mem}
    (hstore : memStore m a' t i x = .ok m')
    (hout : ∀ a, SegMem (m := m) s a → a ≠ a') :
    ListSeg m' s vs := by
  revert hstore hout m'
  induction h with
  | nil =>
    intro m' hstore hout
    exact .nil
  | cons hnode _ ih =>
    intro m' hstore hout
    apply ListSeg.cons
    · unfold nodeAt cellsAt at hnode ⊢
      exact (memFind_memStore_other _ _ _ _ _ _ _ hstore
        (hout _ (.here hnode))).trans hnode
    · exact ih hstore (fun b hb => hout b (.there hnode hb))
