/-
Circe.Mem.LinkedList — dynamic-list memory vocabulary (L2):
per-node points-to over the `Model` link codec, the list-segment
predicate, field load/store triples, and the store-outside-segment
frame lemma.

A `Node = { val : i32, next : Node * }` is one 2-word block:
payload at index 0, encoded link at index 1. Null is word `0`;
a live link `a` is word `a + 1` (bump addresses never wrap in
the test heaps; exactness is an explicit side condition).
-/
import Circe.Mem.Model
import Circe.Mem.Agree

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

/-! ## Address footprint theory (L3c: reversal needs acyclicity)

A segment is acyclic, but its addresses cannot be collected into a
`List`: `ListSeg` lives in `Prop`, and large elimination out of
`Prop` into `Type` is forbidden. The footprint theory therefore
counts chase steps instead (`chaseN`, plain `Nat` recursion over an
executable step): every reachable address is visited at a unique
step, which is the nodup argument in disguise. -/

/-- One chase step: null stays null; a live address decodes its
    link word (total — garbage on dangling links, exactly like the
    evaluator, so agreement is never at issue). -/
def chaseStep (m : Mem) : Option Addr → Option Addr
  | none => none
  | some a =>
    match memFind m a with
    | none => none
    | some b =>
      match b.data[1]? with
      | none => none
      | some w => addrOfWord w

/-- Bounded chase: `k` steps from `s`. -/
def chaseN (m : Mem) : Nat → Option Addr → Option Addr
  | 0, s => s
  | k + 1, s => chaseStep m (chaseN m k s)

/-- A segment starting at `some c` allocates `c`. -/
theorem ListSeg_head_alloc {m : Mem} {c : Addr}
    {vs : List (BitVec 32)} (h : ListSeg m (some c) vs) :
    (memFind m c).isSome = true := by
  cases h with
  | cons h3 _ =>
    unfold nodeAt cellsAt at h3
    simp [h3]

/-- A reachability derivation starting at `some c` allocates `c`
    (both constructors carry a points-to at the head). -/
theorem SegMem_head_alloc {m : Mem} {s : Option Addr} {b : Addr}
    (hb : SegMem (m := m) s b) :
    ∀ c, s = some c → (memFind m c).isSome = true := by
  intro c hc
  subst hc
  cases hb with
  | here h3 =>
    unfold nodeAt cellsAt at h3
    simp [h3]
  | there h3 _ =>
    unfold nodeAt cellsAt at h3
    simp [h3]

/-- Two points-to facts at one address agree on the link (blocks are
    single; link words are injective under the heap exactness
    bound). -/
theorem nodeAt_link_unique {m : Mem} {a : Addr} {t t' : Nat}
    {v v' : BitVec 32} {n n' : Option Addr}
    (h1 : nodeAt m a t v n) (h2 : nodeAt m a t' v' n')
    (hex : ∀ x, (memFind m x).isSome → x + 1 < 2 ^ 32)
    (halloc : ∀ c, n = some c → (memFind m c).isSome)
    (halloc' : ∀ c, n' = some c → (memFind m c).isSome) :
    n = n' := by
  unfold nodeAt cellsAt at h1 h2
  have hlink : linkWord n = linkWord n' := by
    have h := h1.symm.trans h2
    simp only [Option.some.injEq, Block.mk.injEq,
      List.cons.injEq] at h
    exact h.2.2.2.1
  cases n with
  | none =>
    cases n' with
    | none => rfl
    | some c' =>
      exfalso
      have hne := linkWord_some_ne_zero
        (hex c' (halloc' c' rfl))
      rw [linkWord_none] at hlink
      exact hne hlink.symm
  | some c =>
    cases n' with
    | none =>
      exfalso
      have hne := linkWord_some_ne_zero
        (hex c (halloc c rfl))
      rw [linkWord_none] at hlink
      exact hne hlink
    | some c' =>
      have heq := linkWord_some_inj
        (hex c (halloc c rfl)) (hex c' (halloc' c' rfl)) hlink
      rw [heq]

/-- Chase composition: steps add. -/
theorem chaseN_add (m : Mem) (a b : Nat) (s : Option Addr) :
    chaseN m (a + b) s = chaseN m a (chaseN m b s) := by
  induction a with
  | zero => simp [chaseN]
  | succ a ih => simp [chaseN, Nat.succ_add, ih]

/-- Chasing from null stays null. -/
theorem chaseN_none (m : Mem) (k : Nat) :
    chaseN m k none = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp [chaseN, chaseStep, ih]

/-- One chase step through a known node decodes its link. -/
theorem chaseStep_nodeAt {m : Mem} {c : Addr} {t : Nat}
    {v : BitVec 32} {n : Option Addr}
    (hnode : nodeAt m c t v n)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (halloc : ∀ c', n = some c' → (memFind m c').isSome = true) :
    chaseStep m (some c) = n := by
  unfold nodeAt cellsAt at hnode
  simp only [chaseStep, hnode]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq]
  cases n with
  | none => exact addrOfWord_linkWord_none
  | some c' =>
    have hlt := hex c' (halloc c' rfl)
    have h := addrOfWord_linkWord_some hlt
    simpa [linkWord] using h

/-- Reachability is a chase visit: every member is visited at
    some step (link decoding at each step needs the exactness
    bound; allocation comes from the derivation itself). -/
theorem SegMem_chase {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {s : Option Addr} {b : Addr}
    (hb : SegMem (m := m) s b) :
    ∃ k, chaseN m k s = some b := by
  induction hb with
  | here hnode =>
    exact ⟨0, rfl⟩
  | there hnode hmem ih =>
    obtain ⟨k, hk⟩ := ih
    have hstep := chaseStep_nodeAt hnode hex
      (SegMem_head_alloc hmem)
    have h1 : chaseN m 1 _ = _ := hstep
    refine ⟨k + 1, ?_⟩
    rw [chaseN_add, h1, hk]

/-- The chase follows the tail: a visit at step `j` (within
    bounds) lands on a segment tail. -/
theorem chase_follows_tail {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {s : Option Addr} {vs : List (BitVec 32)}
    (h : ListSeg m s vs) :
    ∀ (j d), chaseN m j s = some d → j ≤ vs.length →
      ∃ (vs' : List (BitVec 32)) (t' : ListSeg m (some d) vs'),
        True := by
  intro j
  induction j with
  | zero =>
    intro d hch hle
    have hs : s = some d := hch
    subst hs
    exact ⟨vs, h, trivial⟩
  | succ j ih =>
    intro d hch hle
    simp only [chaseN] at hch
    cases hjd : chaseN m j s with
    | none =>
      rw [hjd] at hch
      simp [chaseStep] at hch
    | some d' =>
      obtain ⟨vs', t', _⟩ := ih d' hjd (by omega)
      cases t' with
      | cons h3 t3 =>
        have hround := chaseStep_nodeAt h3 hex (fun c hc => by
          cases t3 with
          | nil => cases hc
          | cons h4 _ =>
            cases hc
            unfold nodeAt cellsAt at h4
            simp [h4])
        rw [hjd, hround] at hch
        cases hch
        exact ⟨_, t3, trivial⟩

/-- Reachability extends by one step at the tail (the snoc
    companion to `there`, which extends at the head). -/
theorem SegMem_snoc {m : Mem} {s : Option Addr} {d b : Addr}
    {t t' : Nat} {v v' : BitVec 32} {n' : Option Addr}
    (hd : SegMem (m := m) s d) (hdb : nodeAt m d t v (some b))
    (hb : nodeAt m b t' v' n') : SegMem (m := m) s b := by
  revert hdb hb
  induction hd with
  | here _ => intro hdb hb; exact .there hdb (.here hb)
  | there h5 _ ih2 => intro hdb hb; exact .there h5 (ih2 hdb hb)

/-- A self-loop with any segment from its address is
    impossible (a finite segment cannot revisit its head). -/
theorem ListSeg_no_revisit {m : Mem} {a : Addr} {t : Nat}
    {v : BitVec 32} {vs : List (BitVec 32)}
    (hloop : nodeAt m a t v (some a))
    (h : ListSeg m (some a) vs)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32) :
    False := by
  revert h
  induction vs with
  | nil =>
    intro h
    cases h
  | cons w ws ih =>
    intro h
    cases h with
    | cons h2 t2 =>
      have hlink := nodeAt_link_unique hloop h2 hex
        (fun c hc => by
          cases hc
          unfold nodeAt cellsAt at hloop
          simp [hloop])
        (fun c hc => by
          have t2c := t2
          rw [hc] at t2c
          exact ListSeg_head_alloc t2c)
      subst hlink
      exact ih t2

/-- A chase visit within bounds is reachability (the reverse
    bridge: tails at both ends align the step). -/
theorem chase_mem_SegMem {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {s : Option Addr} {vs : List (BitVec 32)}
    (h : ListSeg m s vs) :
    ∀ (j b), chaseN m j s = some b → j ≤ vs.length →
      SegMem (m := m) s b := by
  intro j
  induction j with
  | zero =>
    intro b hch hle
    have hs : s = some b := hch
    subst hs
    cases h with
    | cons h3 _ => exact .here h3
  | succ j ih =>
    intro b hch hle
    have hch0 := hch
    simp only [chaseN] at hch
    cases hjd : chaseN m j s with
    | none =>
      rw [hjd] at hch
      simp [chaseStep] at hch
    | some d' =>
      have hmemd : SegMem (m := m) s d' := ih d' hjd (by omega)
      obtain ⟨_, td, _⟩ := chase_follows_tail hex h j d' hjd
        (by omega)
      obtain ⟨_, tb, _⟩ := chase_follows_tail hex h (j + 1) b
        hch0 hle
      cases td with
      | cons h3 t3 =>
        cases tb with
        | cons hb3 _ =>
          have hround := chaseStep_nodeAt h3 hex (fun c hc => by
            cases t3 with
            | nil => cases hc
            | cons h4 _ =>
              cases hc
              unfold nodeAt cellsAt at h4
              simp [h4])
          rw [hjd, hround] at hch
          cases hch
          exact SegMem_snoc hmemd h3 hb3

/-- A tail allocates its link targets (nil case is vacuous,
    cons case is the head fact). -/
theorem ListSeg_tail_alloc {m : Mem} {n : Option Addr}
    {vs : List (BitVec 32)} (t : ListSeg m n vs) :
    ∀ c, n = some c → (memFind m c).isSome = true := by
  intro c hc
  cases t with
  | nil => cases hc
  | cons h3 _ =>
    cases hc
    unfold nodeAt cellsAt at h3
    simp [h3]

/-- Chase visits stay within the segment length. -/
theorem chaseN_bound {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {s : Option Addr} {vs : List (BitVec 32)}
    (h : ListSeg m s vs) :
    ∀ (j c), chaseN m j s = some c → j ≤ vs.length := by
  revert h
  induction vs generalizing s with
  | nil =>
    intro h j c hch
    cases h with
    | nil =>
      rw [chaseN_none] at hch
      cases hch
  | cons w ws ih =>
    intro h j c hch
    cases h with
    | cons h2 t2 =>
      cases j with
      | zero => simp
      | succ j =>
        have hstep := chaseStep_nodeAt h2 hex
          (ListSeg_tail_alloc t2)
        have h1 : chaseN m 1 _ = _ := hstep
        rw [chaseN_add, h1] at hch
        have hle := ih t2 _ _ hch
        simpa using Nat.succ_le_succ hle

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

/-! ## Segment acyclicity (the conjunction)

Visit uniqueness and head-freshness are proved together by strong
induction on the segment length: uniqueness at `k + 1` uses
freshness at `k` (a head visit inside the tail contradicts it),
freshness at `k + 1` uses uniqueness at `k + 1` (a below-visit of
the head closes a cycle, giving two visits of the same address).
-/

/-- A nonempty segment starts at `some` address. -/
theorem ListSeg_cons_head {m : Mem} {s : Option Addr}
    {vs : List (BitVec 32)} (h : ListSeg m s vs) (hne : vs ≠ []) :
    ∃ c₀, s = some c₀ := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons _ _ => exact ⟨_, rfl⟩

/-- A points-to fact survives a store elsewhere. -/
theorem nodeAt_store_other {m m' : Mem} {a' c : Addr} {t ti i : Nat}
    {v x : BitVec 32} {n : Option Addr}
    (h : nodeAt m' c t v n)
    (hstore : memStore m a' ti i x = .ok m') (hne : c ≠ a') :
    nodeAt m c t v n := by
  unfold nodeAt cellsAt at h ⊢
  rw [memFind_memStore_other _ _ _ _ _ _ _ hstore hne] at h
  exact h

/-- Membership survives a store elsewhere (twin-segment
    transport: the same segment before and after). -/
theorem SegMem_of_store {m m' : Mem} {s : Option Addr}
    {b : Addr} {a' : Addr} {t i : Nat} {x : BitVec 32}
    (h : SegMem (m := m') s b)
    (hstore : memStore m a' t i x = .ok m')
    (hout : ∀ c, SegMem (m := m') s c → c ≠ a') :
    SegMem (m := m) s b := by
  revert hout
  induction h with
  | here hnode =>
    intro hout
    have hne : _ ≠ a' := hout _ (.here hnode)
    exact .here (nodeAt_store_other hnode hstore hne)
  | there hnode hmem ih =>
    intro hout
    have hne : _ ≠ a' := hout _ (.here hnode)
    exact .there (nodeAt_store_other hnode hstore hne)
      (ih (fun c hc => hout c (.there hnode hc)))

/-- The heap exactness bound survives a store (nothing new is
    allocated; the stored address was already live). -/
theorem hex_store {m m' : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {a' : Addr} {t i : Nat} {x : BitVec 32}
    (hstore : memStore m a' t i x = .ok m')
    (ha : (memFind m a').isSome = true) :
    ∀ y, (memFind m' y).isSome = true → y + 1 < 2 ^ 32 := by
  intro y hy
  by_cases heq : y = a'
  · subst heq
    exact hex _ ha
  · have hfind := memFind_memStore_other _ _ _ _ _ _ _ hstore heq
    rw [hfind] at hy
    exact hex _ hy

/-- A node exposes its tag (naming helper: the tag is an
    implicit argument, so callers obtain it through this). -/
theorem nodeAt_tag {m : Mem} {a : Addr} {t : Nat} {v : BitVec 32}
    {n : Option Addr} (h : nodeAt m a t v n) : ∃ t', t' = t :=
  ⟨t, rfl⟩

/-- A segment head exposes its payload, link, and tail values
    (naming helpers: implicits, so callers obtain them through
    these and substitute the inaccessible originals away). -/
theorem nodeAt_parts {m : Mem} {a : Addr} {t : Nat} {v : BitVec 32}
    {n : Option Addr} (h : nodeAt m a t v n) :
    ∃ v' n', v' = v ∧ n' = n := ⟨v, n, rfl, rfl⟩

theorem listSegVals {m : Mem} {s : Option Addr}
    {vs : List (BitVec 32)} (h : ListSeg m s vs) :
    ∃ vs', vs' = vs := ⟨vs, rfl⟩

/-- Link decode inverts link encode (roundtrip at a known
    node, under the heap exactness bound). -/
theorem nodeAt_link_roundtrip {m : Mem} {c : Addr} {t : Nat}
    {v : BitVec 32} {n : Option Addr}
    (h : nodeAt m c t v n)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (halloc : ∀ c', n = some c' → (memFind m c').isSome = true) :
    addrOfWord (linkWord n) = n := by
  cases n with
  | none => exact addrOfWord_linkWord_none
  | some c' => exact addrOfWord_linkWord_some (hex c' (halloc c' rfl))

/-- A chase that returns to its start repeats every visit
    (the cycle-closure fact: going around once more revisits). -/
theorem chase_cycle {m : Mem} {n : Option Addr} {a c₀ : Addr}
    {k₂ : Nat}
    (hk₂ : chaseN m k₂ n = some a)
    (hroundA : chaseStep m (some a) = some c₀)
    (hroundC : chaseStep m (some c₀) = n) :
    chaseN m (k₂ + 2) n = n ∧
      chaseN m (k₂ + (k₂ + 2)) n = some a := by
  have h2step : chaseN m 2 (some a) = n := by
    show chaseStep m (chaseStep m (some a)) = n
    rw [hroundA, hroundC]
  have hL : chaseN m (k₂ + 2) n = n := by
    have hadd : k₂ + 2 = 2 + k₂ := by omega
    rw [hadd, chaseN_add, hk₂]
    exact h2step
  exact ⟨hL, by rw [chaseN_add, hL]; exact hk₂⟩

/-- A chase that avoids the stored address reads identically
    before and after the store (other-address lookups agree). -/
theorem chaseN_store_other {m m'' : Mem} {a' : Addr} {t i : Nat}
    {x : BitVec 32}
    (hstore : memStore m a' t i x = .ok m'')
    {s : Option Addr} (k : Nat)
    (havoid : ∀ j, j ≤ k → ∀ d, chaseN m'' j s = some d → d ≠ a') :
    chaseN m'' k s = chaseN m k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hIH := ih (fun j hj d hd => havoid j (by omega) d hd)
    simp only [chaseN, hIH]
    cases hK : chaseN m k s with
    | none => rfl
    | some d =>
      have hd : d ≠ a' := by
        have h2 : chaseN m'' k s = some d := by rw [hIH]; exact hK
        exact havoid k (by omega) d h2
      simp only [chaseStep,
        memFind_memStore_other _ _ _ _ _ _ _ hstore hd]

/-- A chase past the end of a segment reads `none`
    (the segment is nil-terminated). -/
theorem chaseN_seg_none {m : Mem} {s : Option Addr}
    {vs : List (BitVec 32)}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (h : ListSeg m s vs) :
    chaseN m vs.length s = none := by
  induction h with
  | nil => rfl
  | cons hnode t2 ih =>
    simp only [List.length_cons]
    have hstep := chaseStep_nodeAt hnode hex (ListSeg_tail_alloc t2)
    have h1 : chaseN m 1 _ = _ := hstep
    rw [chaseN_add, h1]
    exact ih

/-- A stored address is not reachable from a framed segment
    (first-visit minimality: the strict prefix before the first
    visit reads identically in both memories, so a visit would
    land inside the pre-store segment — against its acyclicity
    or the carried avoidance). -/
theorem SegMem_store_avoid {m m'' : Mem} {a' : Addr} {t i : Nat}
    {x : BitVec 32}
    (hstore : memStore m a' t i x = .ok m'')
    {s : Option Addr} {vs : List (BitVec 32)}
    (hseg : ListSeg m s vs)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hex'' : ∀ y, (memFind m'' y).isSome = true → y + 1 < 2 ^ 32)
    (hhead : ∀ y, s = some y → y ≠ a')
    (havoidM : ∀ b, SegMem (m := m) s b → b ≠ a') :
    ∀ b, SegMem (m := m'') s b → b ≠ a' := by
  intro b hb hab
  subst b
  obtain ⟨k, hk⟩ := SegMem_chase hex'' hb
  have least : ∀ k, chaseN m'' k s = some a' →
      ∃ k₀, chaseN m'' k₀ s = some a' ∧
        ∀ j, chaseN m'' j s = some a' → k₀ ≤ j := by
    intro k
    refine Nat.strongRecOn k ?_
    intro n ih hk
    classical
    by_cases hkk : ∃ j, j < n ∧ chaseN m'' j s = some a'
    · obtain ⟨j, hjlt, hjv⟩ := hkk
      obtain ⟨k₀, hk₀, hmin⟩ := ih j hjlt hjv
      exact ⟨k₀, hk₀, hmin⟩
    · refine ⟨n, hk, fun j hj => ?_⟩
      by_cases hjj : j = n
      · subst hjj
        exact Nat.le_refl _
      · by_cases h : j < n
        · exact absurd ⟨j, h, hj⟩ hkk
        · omega
  obtain ⟨k₀, hk₀, hk₀min⟩ := least k hk
  have havoid : ∀ j, j < k₀ → ∀ d, chaseN m'' j s = some d → d ≠ a' := by
    intro j hj d hd hcon
    subst hcon
    have hle := hk₀min j hd
    omega
  cases k₀ with
  | zero =>
    simp only [chaseN] at hk₀
    exact hhead _ hk₀ rfl
  | succ j =>
    replace hk₀ : chaseN m'' (j + 1) s = some a' := hk₀
    have hlift : chaseN m'' j s = chaseN m j s :=
      chaseN_store_other hstore j (fun j' hj' d hd =>
        havoid j' (by omega) d hd)
    cases hV : chaseN m'' j s with
    | none =>
      simp [chaseN, hV, chaseStep] at hk₀
    | some q =>
      have hqne : q ≠ a' := havoid j (by omega) q hV
      have hmj : chaseN m j s = some q := by rw [← hlift]; exact hV
      have hstep : chaseStep m (some q) = chaseStep m'' (some q) := by
        simp only [chaseStep,
          memFind_memStore_other _ _ _ _ _ _ _ hstore hqne]
      have hm : chaseN m (j + 1) s = some a' := by
        have e1 : chaseN m (j + 1) s = chaseStep m (some q) := by
          simp only [chaseN, hmj]
        have e3 : chaseStep m'' (some q) = some a' := by
          simp only [chaseN, hV] at hk₀
          exact hk₀
        rw [e1, hstep]
        exact e3
      by_cases hle : j + 1 ≤ vs.length
      · exact (havoidM a' (chase_mem_SegMem hex hseg (j + 1) a' hm hle)) rfl
      · have hexD : ∃ d, j + 1 = d + vs.length :=
          ⟨j + 1 - vs.length, by omega⟩
        obtain ⟨d, hd⟩ := hexD
        have hnone : chaseN m (j + 1) s = none := by
          rw [hd, chaseN_add, chaseN_seg_none hex hseg, chaseN_none]
        rw [hm] at hnone
        exact absurd hnone (by simp)

/-- Segments are acyclic: chase visits are unique, and no head is
    reachable from its own tail. -/
theorem ListSeg_acyclic_aux (k : Nat) :
    ∀ (m) (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (s) (vs : List (BitVec 32)), vs.length ≤ k →
      (h : ListSeg m s vs) →
      (∀ (k₁ k₂ c), chaseN m k₁ s = some c → chaseN m k₂ s = some c →
        k₁ = k₂) ∧
      (∀ (a t v) (hnode : nodeAt m a t v s) (b)
        (hb : SegMem (m := m) s b), b ≠ a) := by
  induction k with
  | zero =>
    intro m hex s vs hle h
    have hnil : vs = [] := List.length_eq_zero_iff.mp
      (Nat.le_zero.mp hle)
    subst hnil
    cases h with
    | nil =>
      refine ⟨?_, ?_⟩
      · intro k₁ k₂ c h1 h2
        rw [chaseN_none] at h1
        cases h1
      · intro a t v hnode b hb
        cases hb
  | succ k ih =>
    intro m hex s vs hle h
    cases vs with
    | nil =>
      cases h with
      | nil =>
        refine ⟨?_, ?_⟩
        · intro k₁ k₂ c h1 h2
          rw [chaseN_none] at h1
          cases h1
        · intro a t v hnode b hb
          cases hb
    | cons w ws =>
      have hne : w :: ws ≠ [] := by simp
      obtain ⟨c₀, hs⟩ := ListSeg_cons_head h hne
      subst hs
      cases h with
      | cons h2 t2 =>
        have hle' : ws.length ≤ k := by
          have hcc := hle
          simp only [List.length_cons] at hcc
          omega
        obtain ⟨ihN, ihH⟩ := ih m hex _ _ hle' t2
        have hstep := chaseStep_nodeAt h2 hex
          (ListSeg_tail_alloc t2)
        have h1c : chaseN m 1 _ = _ := hstep
        have hN : ∀ (k₁ k₂ c), chaseN m k₁ (some c₀) = some c →
            chaseN m k₂ (some c₀) = some c → k₁ = k₂ := by
          intro k₁ k₂ c hv1 hv2
          cases k₁ with
          | zero =>
            cases k₂ with
            | zero => rfl
            | succ j₂ =>
              have hc0 : some _ = some c := hv1
              rw [chaseN_add, h1c] at hv2
              have hseg := chase_mem_SegMem hex t2 _ _ hv2
                (chaseN_bound hex t2 _ _ hv2)
              exact absurd (Option.some_inj.mp hc0).symm
                (ihH _ _ _ h2 _ hseg)
          | succ j₁ =>
            cases k₂ with
            | zero =>
              have hc0 : some _ = some c := hv2
              rw [chaseN_add, h1c] at hv1
              have hseg := chase_mem_SegMem hex t2 _ _ hv1
                (chaseN_bound hex t2 _ _ hv1)
              exact absurd (Option.some_inj.mp hc0).symm
                (ihH _ _ _ h2 _ hseg)
            | succ j₂ =>
              rw [chaseN_add, h1c] at hv1 hv2
              have heq := ihN _ _ _ hv1 hv2
              exact congrArg Nat.succ heq
        refine ⟨hN, ?_⟩
        intro a t v hnode b hb
        cases hb with
        | here _ =>
          intro heq
          subst a
          have hlink := nodeAt_link_unique hnode h2 hex
            (fun c hc => by
              cases hc
              unfold nodeAt cellsAt at hnode
              simp [hnode])
            (ListSeg_tail_alloc t2)
          subst hlink
          exact ListSeg_no_revisit hnode t2 hex
        | there hnode' hmem' =>
          intro heq
          subst b
          have heqA := nodeAt_link_unique h2 hnode' hex
            (ListSeg_tail_alloc t2)
            (SegMem_head_alloc hmem')
          subst heqA
          obtain ⟨k₂, hk₂⟩ := SegMem_chase hex hmem'
          have hroundA := chaseStep_nodeAt hnode hex
            (fun c hc => by
              cases hc
              unfold nodeAt cellsAt at h2
              simp [h2])
          obtain ⟨hL, hvisit2⟩ := chase_cycle hk₂ hroundA hstep
          have hcontra := ihN _ _ _ hk₂ hvisit2
          omega

/-- The head of a segment is fresh for its own tail. -/
theorem ListSeg_head_notin_tail {m : Mem} {a : Addr} {t : Nat}
    {v : BitVec 32} {n₀ : Option Addr} {rest' : List (BitVec 32)}
    (hnode : nodeAt m a t v n₀) (htail : ListSeg m n₀ rest')
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32) :
    ∀ b, SegMem (m := m) n₀ b → b ≠ a := by
  intro b hb
  have hlen : rest'.length ≤ rest'.length := Nat.le_refl _
  have hcon := ListSeg_acyclic_aux rest'.length m hex n₀ rest' hlen
    htail
  exact hcon.2 a t v hnode b hb
