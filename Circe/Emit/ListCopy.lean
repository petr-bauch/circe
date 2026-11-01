/-
Circe.Emit.ListCopy — pillar-1 goal #4: deep copy (`list_copy`)
with per-element `malloc` in the traversal.

The corpus (`tests/cpp/list_copy.cpp`, entry
`Node *list_copy(Node *head)`) chases with a single cursor,
`malloc`-ing one fresh 2-word cell per node, copying the payload,
clearing the fresh link, and appending to the new tail (head-case
vs interior-case on the new tail). It returns the new head
(`nullptr` on empty input). The input chain is never written —
only fresh cells and the previous fresh tail are stored. Faults
are loud: null/dangling/missing loads abort, allocation is
infallible, and exactness decodes every link (fuel bounds the
chase by the segment length).

The mirror allocates with `.nnew` (the statement-level
`memAlloc m 2` arm, as in `pushFront`), copies with `.psetVal`,
clears with `.psetNext .. null`, and appends with the tail `if`
(head-case assigns `new_head`, interior-case swings with
`.psetNext`). The `let nd` inside the loop conses a shadow `nd`
slot per iteration (first-hit lookup keeps the latest); the loop
invariant threads the shadow address list explicitly.

The contract: the returned chain holds the input payloads in
order, every returned cell is fresh (below-mark source vs
above-mark destination bounds, pairwise distinct by segment
acyclicity at the end), and the input chain is untouched (the
full source segment rides every step).
-/
import Circe.Emit.LinkedReverse

/-- Mangled name of the copy entry. -/
def listCopyName : String :=
  "_Z9list_copyP4Node"

/-- The copy loop body: allocate, copy the payload, clear the
    fresh link, append (head-case vs interior-case on the new
    tail), advance. -/
def listCopyLoopBody : CStmt :=
  (.seq (.let_ "nd" nodeTy .nnew)
    (.seq (.psetVal (.var "nd") (.pgetVal (.var "cur")))
      (.seq (.psetNext (.var "nd") (.lit .nullptr))
        (.seq (.if_ (.ueq (.var "tail") (.lit .nullptr))
                (.assign "new_head" (.var "nd"))
                (.psetNext (.var "tail") (.var "nd")))
          (.seq (.assign "tail" (.var "nd"))
            (.assign "cur" (.pgetNext (.var "cur"))))))))

/-- The copy loop (isolated for the loop/evaluator agreement). -/
def listCopyLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) listCopyLoopBody)

/-- Canonical CoreIR for `list_copy`: seed the new head, the
    tail, and the cursor, chase, and return the new head. -/
def listCopyBody : CStmt :=
  (.seq (.let_ "new_head" nodeTy (.lit .nullptr))
    (.seq (.let_ "tail" nodeTy (.lit .nullptr))
      (.seq (.let_ "cur" nodeTy (.var "head"))
        (.seq listCopyLoop (.return_ (.var "new_head"))))))

/-- The copy entry: a single `Node*` in, a `Node*` out (the fresh
    head, null on empty input). -/
def listCopyFunc : Func :=
  ⟨listCopyName,
   [{ name := "head", ty := nodeTy, role := .owned }],
   nodeTy,
   listCopyBody⟩

/-- Copy base environment: head slot, then the three loop slots
    (the entry binds `head` first, then the lets cons `new_head`,
    `tail`, `cur` on the front). -/
def mkListCopyBase (head nh tail cur : Option Addr) : Env :=
  [("cur", .ptrVal cur), ("tail", .ptrVal tail),
    ("new_head", .ptrVal nh), ("head", .ptrVal head)]

/-- The `nd` shadow slots: one per completed iteration (the loop
    body's `let nd` conses on the front, so lookup sees the
    latest). -/
def ndShadows (nds : List Addr) : Env :=
  nds.map (fun a => ("nd", .ptrVal (some a)))

/-- Full copy environment: shadows on the front, base behind. -/
def mkListCopyEnv (head nh tail cur : Option Addr)
    (nds : List Addr) : Env :=
  ndShadows nds ++ mkListCopyBase head nh tail cur

theorem ndShadows_keys (nds : List Addr) (k : String) (v : Value) :
    (k, v) ∈ ndShadows nds → k = "nd" := by
  intro hmem
  simp only [ndShadows] at hmem
  obtain ⟨a, _, h⟩ := List.mem_map.mp hmem
  cases h
  rfl

/-- Lookup through an env prefix whose keys all miss. -/
theorem envLookup_append_miss (l₁ l₂ : Env) (x : String)
    (hmiss : ∀ k v, (k, v) ∈ l₁ → k ≠ x) :
    envLookup (l₁ ++ l₂) x = envLookup l₂ x := by
  induction l₁ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    have hne : x ≠ k := Ne.symm (hmiss k v (by simp))
    have hmiss' : ∀ k' v', (k', v') ∈ tl → k' ≠ x := by
      intro k' v' hmem
      exact hmiss k' v' (by simp [hmem])
    simp [List.cons_append, envLookup, hne, ih hmiss']

/-- Update through an env prefix whose keys all miss. -/
theorem envUpdate_append_miss (l₁ l₂ : Env) (x : String)
    (v : Value) (l₂' : Env)
    (hmiss : ∀ k w, (k, w) ∈ l₁ → k ≠ x)
    (hup : envUpdate l₂ x v = some l₂') :
    envUpdate (l₁ ++ l₂) x v = some (l₁ ++ l₂') := by
  induction l₁ with
  | nil => simpa using hup
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    have hne : x ≠ k := Ne.symm (hmiss k w (by simp))
    have hmiss' : ∀ k' w', (k', w') ∈ tl → k' ≠ x := by
      intro k' w' hmem
      exact hmiss k' w' (by simp [hmem])
    have hih := ih hmiss'
    simp only [List.cons_append, envUpdate_miss _ _ _ _ _ hne,
      hih]

theorem mkListCopyEnv_cur (head nh tail cur : Option Addr)
    (nds : List Addr) :
    envLookup (mkListCopyEnv head nh tail cur nds) "cur" =
      some (.ptrVal cur) := by
  simp only [mkListCopyEnv]
  rw [envLookup_append_miss _ _ _
    (fun k v hmem hcon => by
      have := ndShadows_keys nds k v hmem
      rw [this] at hcon
      exact absurd hcon (by decide))]
  simp [mkListCopyBase, envLookup,
    show ("cur" : String) ≠ "tail" by decide,
    show ("cur" : String) ≠ "new_head" by decide,
    show ("cur" : String) ≠ "head" by decide]

theorem mkListCopyEnv_tail (head nh tail cur : Option Addr)
    (nds : List Addr) :
    envLookup (mkListCopyEnv head nh tail cur nds) "tail" =
      some (.ptrVal tail) := by
  simp only [mkListCopyEnv]
  rw [envLookup_append_miss _ _ _
    (fun k v hmem hcon => by
      have := ndShadows_keys nds k v hmem
      rw [this] at hcon
      exact absurd hcon (by decide))]
  simp [mkListCopyBase, envLookup]

theorem mkListCopyEnv_new_head (head nh tail cur : Option Addr)
    (nds : List Addr) :
    envLookup (mkListCopyEnv head nh tail cur nds) "new_head" =
      some (.ptrVal nh) := by
  simp only [mkListCopyEnv]
  rw [envLookup_append_miss _ _ _
    (fun k v hmem hcon => by
      have := ndShadows_keys nds k v hmem
      rw [this] at hcon
      exact absurd hcon (by decide))]
  simp [mkListCopyBase, envLookup,
    show ("new_head" : String) ≠ "head" by decide]

theorem mkListCopyEnv_head (head nh tail cur : Option Addr)
    (nds : List Addr) :
    envLookup (mkListCopyEnv head nh tail cur nds) "head" =
      some (.ptrVal head) := by
  simp only [mkListCopyEnv]
  rw [envLookup_append_miss _ _ _
    (fun k v hmem hcon => by
      have := ndShadows_keys nds k v hmem
      rw [this] at hcon
      exact absurd hcon (by decide))]
  simp [mkListCopyBase, envLookup]

theorem mkListCopyEnv_nd_latest (head nh tail cur : Option Addr)
    (nd : Addr) (nds : List Addr) :
    envLookup
      (mkListCopyEnv head nh tail cur (nd :: nds)) "nd" =
      some (.ptrVal (some nd)) := by
  simp [mkListCopyEnv, ndShadows, envLookup]

/-! ## Forward mirror (chase with per-node allocation) -/

/-- Copy chase: each step loads the payload and link (loud on
    miss), allocates one fresh cell, stores the payload, clears
    the fresh link, then appends — head-case (`tail = none`)
    seeds the new head, interior-case swings the old tail link.
    Fuel bounds the chase by the remaining segment length. -/
def listCopyChase (F : Nat) (m : Mem) (cur nh tail : Option Addr) :
    Result (Mem × Option Addr × Option Addr) :=
  match cur with
  | none => .ok (m, nh, tail)
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
          match memLoad m a b.tag 1 with
          | .error e => .error e
          | .ok w' =>
            let (m1, nd) := memAlloc m 2
            match memStore m1 nd nd 0 w with
            | .error e => .error e
            | .ok m2 =>
              match memStore m2 nd nd 1 (linkWord none) with
              | .error e => .error e
              | .ok m3 =>
                match tail with
                | none =>
                  listCopyChase F m3 (addrOfWord w')
                    (some nd) (some nd)
                | some p =>
                  match memFind m3 p with
                  | none => .error .AssertFail
                  | some bp =>
                    match memStore m3 p bp.tag 1
                        (linkWord (some nd)) with
                    | .error e => .error e
                    | .ok m4 =>
                      listCopyChase F m4 (addrOfWord w') nh
                        (some nd)

/-- Entry mirror: chase from the head with empty destination,
    then return the new head. -/
def listCopyFwd (F : Nat) (m : Mem) (head : Option Addr) :
    Result (Mem × Option Addr) :=
  match listCopyChase F m head none none with
  | .error e => .error e
  | .ok (m', nh', _) => .ok (m', nh')

/-! ## Copy kit (per-step transports) -/

/-- A store preserves the `next` counter (the ok-value reuses
    the pre-store counter). -/
theorem memStore_next {m m' : Mem} {a : Addr} {t i : Nat}
    {x : BitVec 32}
    (hstore : memStore m a t i x = .ok m') : m'.next = m.next := by
  have hex1 : ∃ b, memFind m a = some b := by
    unfold memStore at hstore
    cases hF : memFind m a with
    | none => simp [hF] at hstore
    | some b => exact ⟨b, rfl⟩
  obtain ⟨b, hF⟩ := hex1
  unfold memStore at hstore
  rw [hF] at hstore
  dsimp only at hstore
  split at hstore
  · simp at hstore
  · split at hstore
    · simp at hstore
    · split at hstore
      · simp only [Except.ok.injEq] at hstore
        cases hstore
        rfl
      · simp at hstore

/-- A successful load pins the tag (the `b.tag != t` guard
    must have passed — connects the step's existential tag with
    the caller's node tag). -/
theorem memLoad_tag {m : Mem} {a t i : Nat} {x : BitVec 32}
    {b : Block} (hload : memLoad m a t i = .ok x)
    (hfind : memFind m a = some b) : t = b.tag := by
  unfold memLoad at hload
  rw [hfind] at hload
  by_cases heq : b.tag = t
  · exact heq.symm
  · simp [heq] at hload

/-- Exactness survives an allocation with room to spare (the
    fresh cell's bound comes from the room hypothesis, old cells
    ride the allocation untouched). -/
theorem hex_alloc {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {C len : Nat} (hC : C + 1 < 2 ^ 32)
    (hroom : m.next + len ≤ C)
    (d : List (BitVec 32)) :
    ∀ y, (memFind (memAllocData m d).1 y).isSome = true →
      y + 1 < 2 ^ 32 := by
  intro y hy
  have hnd : (memAllocData m d).2 = m.next := memAllocData_next m d
  by_cases heq : y = (memAllocData m d).2
  · subst heq
    rw [hnd] at *
    have hle : m.next ≤ C :=
      Nat.le_trans (Nat.le_add_right _ _) hroom
    have hle1 : m.next + 1 ≤ C + 1 := Nat.add_le_add_right hle 1
    exact Nat.lt_of_le_of_lt hle1 hC
  · have hne : y ≠ m.next := by
      rw [← hnd]
      exact heq
    have hfind := memFind_memAllocData_other m d y hne
    rw [hfind] at hy
    exact hex _ hy

/-- Membership survives a store elsewhere (forward twin of
    `SegMem_of_store`: the footprint router — the `there` case
    re-routes membership). -/
theorem SegMem_store_other_fwd {m m' : Mem} {s : Option Addr}
    {b x : Addr} {t i : Nat} {v : BitVec 32}
    (hmem : SegMem (m := m) s b)
    (hout : ∀ c, SegMem (m := m) s c → c ≠ x)
    (hstore : memStore m x t i v = .ok m') :
    SegMem (m := m') s b := by
  revert hout
  induction hmem with
  | here hnode =>
    intro hout
    exact .here (nodeAt_store_other_fwd hnode hstore
      (hout _ (.here hnode)))
  | there hnode hmem ih =>
    intro hout
    exact .there (nodeAt_store_other_fwd hnode hstore
      (hout _ (.here hnode)))
      (ih (fun c hc => hout c (.there hnode hc)))

/-- Membership survives an allocation elsewhere (forward twin
    for `memAllocData`: the fresh address is outside). -/
theorem SegMem_alloc_other_fwd {m : Mem} {s : Option Addr}
    {b : Addr} (hmem : SegMem (m := m) s b)
    (hout : ∀ c, SegMem (m := m) s c → c ≠ m.next)
    (d : List (BitVec 32)) :
    SegMem (m := (memAllocData m d).1) s b := by
  revert hout
  induction hmem with
  | here hnode =>
    intro hout
    exact .here (nodeAt_alloc_other hnode d
      (hout _ (.here hnode)))
  | there hnode hmem ih =>
    intro hout
    exact .there (nodeAt_alloc_other hnode d
      (hout _ (.here hnode)))
      (ih (fun c hc => hout c (.there hnode hc)))

/-- A segment carrying a per-node footprint bound (the copy
    invariant bundles the below-mark source bound and the
    above-mark destination bound into the derivation itself, so
    transports never need cross-memory alignment — the bound
    travels with its node). -/
inductive BoundedSeg (m : Mem) (n₀ : Nat) (P : Addr → Prop) :
    Option Addr → List (BitVec 32) → Prop
  | nil : BoundedSeg m n₀ P none []
  | cons {a t v n vs} : nodeAt m a t v n → P a →
      BoundedSeg m n₀ P n vs →
      BoundedSeg m n₀ P (some a) (v :: vs)

/-- Forget the bounds (for the plain-`ListSeg` kit). -/
theorem BoundedSeg.toListSeg {m : Mem} {n₀ : Nat}
    {P : Addr → Prop} {s : Option Addr} {vs : List (BitVec 32)}
    (h : BoundedSeg m n₀ P s vs) : ListSeg m s vs := by
  induction h with
  | nil => exact .nil
  | cons hnode _ _ ih => exact .cons hnode ih

/-- A bounded segment rides a store at an outside address
    (the footprint router — the `there` case re-routes
    membership; outsideness is per-node, discharged fresh from
    the mark or the carried arithmetic). -/
theorem BoundedSeg.store_other {m m' : Mem} {n₀ : Nat}
    {P : Addr → Prop} {s : Option Addr} {vs : List (BitVec 32)}
    {x : Addr} {t i : Nat} {v : BitVec 32}
    (h : BoundedSeg m n₀ P s vs)
    (hout : ∀ a t v n, nodeAt m a t v n → a ≠ x)
    (hstore : memStore m x t i v = .ok m') :
    BoundedSeg m' n₀ P s vs := by
  revert hout
  induction h with
  | nil =>
    intro _
    exact .nil
  | cons hnode hP _ ih =>
    intro hout
    exact .cons (nodeAt_store_other_fwd hnode hstore
        (hout _ _ _ _ hnode))
      hP (ih hout)

/-- A bounded segment rides an allocation (per-node freshness
    against the high-water mark). -/
theorem BoundedSeg.alloc_other {m : Mem} {n₀ : Nat}
    {P : Addr → Prop} {s : Option Addr} {vs : List (BitVec 32)}
    (h : BoundedSeg m n₀ P s vs)
    (hout : ∀ a t v n, nodeAt m a t v n → a ≠ m.next)
    (d : List (BitVec 32)) :
    BoundedSeg (memAllocData m d).1 n₀ P s vs := by
  revert hout
  induction h with
  | nil =>
    intro _
    exact .nil
  | cons hnode hP _ ih =>
    intro hout
    exact .cons (nodeAt_alloc_other hnode d (hout _ _ _ _ hnode))
      hP (ih hout)

/-- The carried bound at a footprint address: joint induction
    on the segment (the derivation re-routes through link
    alignment — same memory throughout). -/
theorem BoundedSeg_mem {m : Mem} {n₀ : Nat} {P : Addr → Prop}
    {s : Option Addr} {vs : List (BitVec 32)}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hB : BoundedSeg m n₀ P s vs)
    {a : Addr} (hmem : SegMem (m := m) s a) : P a := by
  revert hmem
  induction hB with
  | nil =>
    intro hmem
    cases hmem
  | cons hnode hP t2B ih =>
    intro hmem
    cases hmem with
    | here _ => exact hP
    | there hnodeQ hmemT =>
      have heq := nodeAt_link_unique hnode hnodeQ hex
        (ListSeg_start_alloc (BoundedSeg.toListSeg t2B))
        (SegMem_head_alloc hmemT)
      rw [← heq] at hmemT
      exact ih hmemT

/-- Footprint outsideness from a bounded segment (the carried
    bound plus a per-address separator). -/
theorem BoundedSeg_outside {m : Mem} {n₀ : Nat} {P : Addr → Prop}
    {s : Option Addr} {vs : List (BitVec 32)} {x : Addr}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hB : BoundedSeg m n₀ P s vs)
    (hout : ∀ a, P a → a ≠ x)
    {a : Addr} (hmem : SegMem (m := m) s a) : a ≠ x :=
  hout _ (BoundedSeg_mem hex hB hmem)

/-- A store into a known cell succeeds (tag, liveness, and
    bounds all discharge from the cell fact). -/
theorem memStore_cellsAt_ok {m : Mem} {a t : Nat}
    {l : List (BitVec 32)} {i : Nat} {x : BitVec 32}
    (hcell : cellsAt m a t l) (hlt : i < l.length) :
    ∃ m', memStore m a t i x = .ok m' := by
  have hfind : memFind m a = some ⟨t, true, l⟩ := hcell
  have hok : memStore m a t i x =
      .ok ⟨m.next, (a, ⟨t, true, l.set i x⟩) :: m.blocks,
        m.blocks64⟩ := by
    unfold memStore
    rw [hfind]
    simp [hlt]
  exact ⟨_, hok⟩

/-- A bounded segment rides an allocation plus two fresh-cell
    stores (the `alloc_stores_other` kit lemma carrying the
    bound — outsideness is the allocator invariant). -/
theorem BoundedSeg.alloc_stores_other {m : Mem} {n₀ : Nat}
    {P : Addr → Prop} {s : Option Addr} {vs : List (BitVec 32)}
    (h : BoundedSeg m n₀ P s vs)
    (hmfresh : memFind m m.next = none)
    {m1 m2 m3 : Mem} {a' : Addr}
    {t1 i1 : Nat} {x1 : BitVec 32}
    {t2 i2 : Nat} {x2 : BitVec 32}
    (ha' : a' = m.next)
    (halloc : m1 = (memAlloc m 2).1)
    (hstore1 : memStore m1 a' t1 i1 x1 = .ok m2)
    (hstore2 : memStore m2 a' t2 i2 x2 = .ok m3) :
    BoundedSeg m3 n₀ P s vs := by
  have hdiff : ∀ (c t : Nat) (v : BitVec 32) (n : Option Addr),
      nodeAt m c t v n → c ≠ m.next := by
    intro c t v n hc heq
    have hfind : memFind m c = some _ := hc
    rw [heq] at hfind
    rw [hmfresh] at hfind
    simp at hfind
  have hbridge : (memAlloc m 2).1 =
      (memAllocData m (List.replicate 2 0)).1 := rfl
  induction h with
  | nil => exact .nil
  | cons hnode hP _ ih =>
      have h1 := nodeAt_alloc_other hnode (List.replicate 2 0)
        (hdiff _ _ _ _ hnode)
      rw [← hbridge, ← halloc] at h1
      have h2 := nodeAt_store_other_fwd h1 hstore1 (by
        rw [ha']
        exact hdiff _ _ _ _ hnode)
      exact .cons
        (nodeAt_store_other_fwd h2 hstore2 (by
          rw [ha']
          exact hdiff _ _ _ _ hnode))
        hP ih

/-- Destination snoc with the carried bound (bounded twin of
    `ListSeg.swing_snoc`: swing the old tail link and append the
    fresh cell — one induction that replaces the tail's
    ascription at its address and extends at the end; the
    nonempty-tail contradiction mirrors the `ListSeg` version). -/
theorem BoundedSeg_swing_snoc {m m' : Mem} {n₀ : Nat}
    {P : Addr → Prop} {s : Option Addr} {pref : List (BitVec 32)}
    {p nd : Addr} {tp tnd : Nat} {wp wnd : BitVec 32}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (h : BoundedSeg m n₀ P s pref)
    (hlast : nodeAt m p tp wp none)
    (hmemtail : SegMem (m := m) s p)
    (hstore : memStore m p tp 1 (linkWord (some nd)) = .ok m')
    (hswingP : nodeAt m' p tp wp (some nd))
    (hnd : nodeAt m' nd tnd wnd none)
    (hPp : P p) (hPnd : P nd) :
    BoundedSeg m' n₀ P s (pref ++ [wnd]) := by
  induction h with
  | nil =>
    cases hmemtail
  | cons hnode hP t2 ih =>
    rename_i a₀ t₀ v₀ nL vs₀
    by_cases heq : a₀ = p
    · subst heq
      have h1 := hnode
      have h2 := hlast
      unfold nodeAt cellsAt at h1 h2
      have hpl := h1.symm.trans h2
      simp only [Option.some.injEq, Block.mk.injEq,
        List.cons.injEq] at hpl
      have hvw : _ = wp := hpl.2.2.1
      rw [hvw]
      cases t2 with
      | nil =>
        exact .cons hswingP hPp (.cons hnd hPnd .nil)
      | cons h3 hP3 _ =>
        exact False.elim (linkWord_none_ne_some
          (hex _ (by
            have h3c := h3
            unfold nodeAt cellsAt at h3c
            simp [h3c]))
          hpl.2.2.2.1.symm)
    · cases hmemtail with
      | here _ => exact absurd rfl heq
      | there hnodeQ hT =>
        have halign := nodeAt_link_unique hnode hnodeQ hex
          (ListSeg_start_alloc (BoundedSeg.toListSeg t2))
          (SegMem_head_alloc hT)
        rw [← halign] at hT
        exact .cons (nodeAt_store_other_fwd hnode hstore heq)
          hP (ih hT)

/-- Destination reachability rides an allocation plus two
    fresh-cell stores (the three-step transport for the copy
    tail — the transported addresses are the original ones, so
    allocator freshness discharges every stage). -/
theorem SegMem_alloc_stores_other_fwd {m : Mem} {s : Option Addr}
    {b : Addr} (hmem : SegMem (m := m) s b)
    (hmfresh : memFind m m.next = none)
    {m1 m2 m3 : Mem} {nd : Addr}
    {t1 i1 : Nat} {x1 : BitVec 32}
    {t2 i2 : Nat} {x2 : BitVec 32}
    (hnd : nd = m.next)
    (halloc : m1 = (memAlloc m 2).1)
    (hstore1 : memStore m1 nd t1 i1 x1 = .ok m2)
    (hstore2 : memStore m2 nd t2 i2 x2 = .ok m3) :
    SegMem (m := m3) s b := by
  have hdiff : ∀ (c t : Nat) (v : BitVec 32) (n : Option Addr),
      nodeAt m c t v n → c ≠ m.next := by
    intro c t v n hc heq
    have hfind : memFind m c = some _ := hc
    rw [heq] at hfind
    rw [hmfresh] at hfind
    simp at hfind
  have hbridge : (memAlloc m 2).1 =
      (memAllocData m (List.replicate 2 0)).1 := rfl
  induction hmem with
  | here hnode =>
      have h1 := nodeAt_alloc_other hnode (List.replicate 2 0)
        (hdiff _ _ _ _ hnode)
      rw [← hbridge, ← halloc] at h1
      have h2 := nodeAt_store_other_fwd h1 hstore1 (by
        rw [hnd]
        exact hdiff _ _ _ _ hnode)
      exact .here (nodeAt_store_other_fwd h2 hstore2 (by
        rw [hnd]
        exact hdiff _ _ _ _ hnode))
  | there hnode _ ih =>
      have h1 := nodeAt_alloc_other hnode (List.replicate 2 0)
        (hdiff _ _ _ _ hnode)
      rw [← hbridge, ← halloc] at h1
      have h2 := nodeAt_store_other_fwd h1 hstore1 (by
        rw [hnd]
        exact hdiff _ _ _ _ hnode)
      exact .there (nodeAt_store_other_fwd h2 hstore2 (by
        rw [hnd]
        exact hdiff _ _ _ _ hnode)) ih

/-- A bounded segment rides a store separated by its carried
    bound (every node's ascription separates it from the stored
    address — the copy swing store). -/
theorem BoundedSeg.store_other_sep {m m' : Mem} {n₀ : Nat}
    {P : Addr → Prop} {s : Option Addr} {vs : List (BitVec 32)}
    {x : Addr} {t i : Nat} {v : BitVec 32}
    (h : BoundedSeg m n₀ P s vs)
    (hsep : ∀ a, P a → a ≠ x)
    (hstore : memStore m x t i v = .ok m') :
    BoundedSeg m' n₀ P s vs := by
  revert hsep
  induction h with
  | nil =>
      intro _
      exact .nil
  | cons hnode hP _ ih =>
      intro hsep
      exact .cons (nodeAt_store_other_fwd hnode hstore
          (hsep _ hP))
        hP (ih hsep)

/-- The swung tail keeps its destination membership: induction
    on the old derivation, replacing the tail's ascription with
    the swung one (`by_cases` on the head address — the replaced
    node continues through its new link, other nodes ride the
    store). -/
theorem SegMem_swing_replace {m m4 : Mem} {nh : Option Addr}
    {pref : List (BitVec 32)}
    {p nd : Addr} {tp : Nat} {w x : BitVec 32}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hdst : ListSeg m nh pref)
    (hmem : SegMem (m := m) nh p)
    (hstore : memStore m p tp 1 x = .ok m4)
    (hswingP : nodeAt m4 p tp w (some nd)) :
    SegMem (m := m4) nh p := by
  revert hmem
  induction hdst with
  | nil =>
    intro hmem
    cases hmem
  | cons hnode t2 ih =>
    rename_i a₀ t₀ v₀ n₀ vs₀
    intro hmem
    cases hmem with
    | here _ => exact .here hswingP
    | there hnodeQ hmemT =>
      by_cases heq : a₀ = p
      · subst heq
        exact .here hswingP
      · have halign := nodeAt_link_unique hnode hnodeQ hex
          (ListSeg_start_alloc t2)
          (SegMem_head_alloc hmemT)
        rw [← halign] at hmemT
        exact .there (nodeAt_store_other_fwd hnodeQ hstore heq)
          (halign ▸ ih hmemT)

/-! ## The copy invariant and the per-iteration step -/

/-- Copy loop invariant: the full source stays intact below
    the mark, the suffix and destination ride every step, the
    tail linkage tracks the last fresh cell, and allocator room
    covers the remaining nodes. -/
structure CopyInv (n₀ : Nat) (vs₀ : List (BitVec 32)) (F : Nat)
    (m : Mem) (head cur nh tail : Option Addr)
    (pref suf : List (BitVec 32)) : Prop where
  hfullB : BoundedSeg m n₀ (· < n₀) head vs₀
  hsrcB : BoundedSeg m n₀ (· < n₀) cur suf
  hdstB : BoundedSeg m n₀ (n₀ ≤ ·) nh pref
  hmemtail : ∀ p, tail = some p → SegMem (m := m) nh p
  hlastP : ∀ p, tail = some p → ∃ tp wp, nodeAt m p tp wp none
  htailt : ∀ p, tail = some p → p < m.next
  hmark : Mark m
  hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32
  hnextge : n₀ ≤ m.next
  hroom : m.next + suf.length ≤ n₀ + vs₀.length
  hlen : suf.length ≤ F
  hsplit : pref ++ suf = vs₀
  hroom0 : n₀ + vs₀.length + 1 < 2 ^ 32
  hcoh : tail = none → pref = [] ∧ nh = none

/-- One copy iteration with an empty destination: load,
    allocate, copy the payload, clear the link, seed the new
    head and tail. -/
theorem copy_step_none {n₀ : Nat} {vs₀ : List (BitVec 32)} {F : Nat}
    {m : Mem} {head : Option Addr} {a : Addr} {w : BitVec 32}
    {ws pref : List (BitVec 32)}
    (hinv : CopyInv n₀ vs₀ (F + 1) m head (some a) none none pref
      (w :: ws)) :
    ∃ (nd : Addr) (m1 m2 m3 : Mem) (t : Nat) (lw : BitVec 32),
      memAlloc m 2 = (m1, nd) ∧
      memLoad m a t 0 = .ok w ∧
      memLoad m a t 1 = .ok lw ∧
      memStore m1 nd nd 0 w = .ok m2 ∧
      memStore m2 nd nd 1 (linkWord none) = .ok m3 ∧
      cellsAt m2 (memAlloc m 2).2 ((memAlloc m 2).2) [w, 0] ∧
      CopyInv n₀ vs₀ F m3 head (addrOfWord lw) (some nd)
        (some nd) (pref ++ [w]) ws := by
  have hsrcB := hinv.hsrcB
  have hnextge := hinv.hnextge
  have hroom := hinv.hroom
  have hlen := hinv.hlen
  -- Head-case coherence: no old tail means the old destination
  -- is empty (`pref = []`).
  obtain ⟨hpref, _⟩ := hinv.hcoh rfl
  subst hpref
  cases hsrcB with
  | @cons a₀ t₀ v₀ nL vs₀ hnode hltB t2B =>
    have hcell : cellsAt m a t₀ [w, linkWord nL] := hnode
    have hL0 : memLoad m a t₀ 0 = .ok w :=
      memLoad_cellsAt m a t₀ 0 [w, linkWord nL] w hcell
        (by simp)
    have hL1 : memLoad m a t₀ 1 = .ok (linkWord nL) :=
      memLoad_cellsAt m a t₀ 1 [w, linkWord nL] (linkWord nL)
        hcell (by simp)
    have hdec : addrOfWord (linkWord nL) = nL :=
      nodeAt_link_roundtrip hnode hinv.hex
        (ListSeg_start_alloc (BoundedSeg.toListSeg t2B))
    have hmfresh : memFind m m.next = none :=
      hinv.hmark _ (Nat.le_refl _)
    have hnd : (memAlloc m 2).2 = m.next := memAlloc_next m 2
    have h1next : (memAlloc m 2).1.next = m.next + 1 := rfl
    have hbridge : (memAlloc m 2).1 =
        (memAllocData m (List.replicate 2 0)).1 := rfl
    have hmark1 : Mark (memAlloc m 2).1 :=
      freshAbove_alloc m 2 hinv.hmark
    have hex1 : ∀ x, (memFind (memAlloc m 2).1 x).isSome = true →
        x + 1 < 2 ^ 32 := by
      have h := hex_alloc hinv.hex hinv.hroom0 hinv.hroom
        (List.replicate 2 0)
      rwa [← hbridge] at h
    have hfindN : memFind (memAlloc m 2).1 (memAlloc m 2).2 =
        some ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ :=
      memFind_memAlloc m 2
    have hcell0 : cellsAt (memAlloc m 2).1 (memAlloc m 2).2
        ((memAlloc m 2).2) [0, 0] := hfindN
    obtain ⟨m2, hS1⟩ := memStore_cellsAt_ok (i := 0) hcell0
      (by decide)
    have hcell1 : cellsAt m2 (memAlloc m 2).2
        ((memAlloc m 2).2) [w, 0] := by
      have h := memFind_cellsAt_store _ _ _ _ _ _ _ hcell0
        (by decide) hS1
      simpa using h
    obtain ⟨m3, hS2⟩ := memStore_cellsAt_ok (i := 1) hcell1
      (by simp)
    have hcell2 : cellsAt m3 (memAlloc m 2).2
        ((memAlloc m 2).2) [w, linkWord none] := by
      have h := memFind_cellsAt_store _ _ _ _ _ _ _ hcell1
        (by simp) hS2
      simpa using h
    have hndN : nodeAt m3 (memAlloc m 2).2 ((memAlloc m 2).2)
        w none := hcell2
    have hmark2 : Mark m2 := freshAbove_store hmark1 hS1
    have hmark3 : Mark m3 := freshAbove_store hmark2 hS2
    have ha1 : (memFind (memAlloc m 2).1
        (memAlloc m 2).2).isSome = true := by
      rw [hfindN]
      rfl
    have hex2 : ∀ x, (memFind m2 x).isSome = true →
        x + 1 < 2 ^ 32 :=
      hex_store hex1 hS1 ha1
    have hfind2 : memFind m2 (memAlloc m 2).2 = some _ := hcell1
    have ha2 : (memFind m2 (memAlloc m 2).2).isSome = true := by
      rw [hfind2]
      rfl
    have hex3 : ∀ x, (memFind m3 x).isSome = true →
        x + 1 < 2 ^ 32 :=
      hex_store hex2 hS2 ha2
    have h2next : m2.next = (memAlloc m 2).1.next :=
      memStore_next hS1
    have h3next : m3.next = m2.next := memStore_next hS2
    have hfull3 := BoundedSeg.alloc_stores_other hinv.hfullB
      hmfresh hnd rfl hS1 hS2
    have hsrc3pre := BoundedSeg.alloc_stores_other t2B hmfresh
      hnd rfl hS1 hS2
    have hsrc3 : BoundedSeg m3 n₀ (· < n₀)
        (addrOfWord (linkWord nL)) ws := by
      rw [hdec]
      exact hsrc3pre
    have hPnd : n₀ ≤ (memAlloc m 2).2 := by
      rw [hnd]
      exact hnextge
    have hdst3 : BoundedSeg m3 n₀ (n₀ ≤ ·)
        (some ((memAlloc m 2).2)) [w] :=
      .cons hndN hPnd .nil
    have hmemtail3 :
        ∀ p, (some ((memAlloc m 2).2)) = some p →
          SegMem (m := m3) (some ((memAlloc m 2).2)) p := by
      intro p hp
      cases hp
      exact .here hndN
    have hlastP3 :
        ∀ p, (some ((memAlloc m 2).2)) = some p →
          ∃ tp wp, nodeAt m3 p tp wp none := by
      intro p hp
      cases hp
      exact ⟨_, _, hndN⟩
    have htailt3 :
        ∀ p, (some ((memAlloc m 2).2)) = some p →
          p < m3.next := by
      intro p hp
      cases hp
      rw [hnd, h3next, h2next, h1next]
      exact Nat.lt_succ_self _
    have hnextge3 : n₀ ≤ m3.next := by
      rw [h3next, h2next, h1next]
      exact Nat.le_succ_of_le hnextge
    have hlen_eq : (w :: ws).length = ws.length + 1 := rfl
    have hroom3 : m3.next + ws.length ≤ n₀ + vs₀.length := by
      have hr := hroom
      rw [hlen_eq] at hr
      rw [h3next, h2next, h1next]
      omega
    have hlen3 : ws.length ≤ F := by
      have hl := hlen
      rw [hlen_eq] at hl
      omega
    have hsplit3 : ([w] : List (BitVec 32)) ++ ws = vs₀ := by
      have h := hinv.hsplit
      simpa using h
    exact ⟨_, _, m2, m3, _, _,
      rfl, hL0, hL1, hS1, hS2, hcell1,
      { hfullB := hfull3
        hsrcB := hsrc3
        hdstB := hdst3
        hmemtail := hmemtail3
        hlastP := hlastP3
        htailt := htailt3
        hmark := hmark3
        hex := hex3
        hnextge := hnextge3
        hroom := hroom3
        hlen := hlen3
        hsplit := hsplit3
        hcoh := fun h => by cases h
        hroom0 := hinv.hroom0 }⟩

/-- One copy iteration with a nonempty destination: load,
    allocate, copy the payload, clear the link, then swing the
    old tail's link to the fresh cell. -/
theorem copy_step_some {n₀ : Nat} {vs₀ : List (BitVec 32)} {F : Nat}
    {m : Mem} {head : Option Addr} {a p : Addr} {w : BitVec 32}
    {ws pref : List (BitVec 32)} {nh : Option Addr}
    (hinv : CopyInv n₀ vs₀ (F + 1) m head (some a) nh (some p) pref
      (w :: ws)) :
    ∃ (nd : Addr) (m1 m2 m3 m4 : Mem) (t tp : Nat)
      (lw wp : BitVec 32),
      memAlloc m 2 = (m1, nd) ∧
      memLoad m a t 0 = .ok w ∧
      memLoad m a t 1 = .ok lw ∧
      memStore m1 nd nd 0 w = .ok m2 ∧
      memStore m2 nd nd 1 (linkWord none) = .ok m3 ∧
      cellsAt m2 (memAlloc m 2).2 ((memAlloc m 2).2) [w, 0] ∧
      memStore m3 p tp 1 (linkWord (some nd)) = .ok m4 ∧
      nodeAt m3 p tp wp none ∧
      CopyInv n₀ vs₀ F m4 head (addrOfWord lw) nh (some nd)
        (pref ++ [w]) ws := by
  have hsrcB := hinv.hsrcB
  have hnextge := hinv.hnextge
  have hroom := hinv.hroom
  have hlen := hinv.hlen
  have hmem0 := hinv.hmemtail _ rfl
  obtain ⟨tp, wp, hlast⟩ := hinv.hlastP _ rfl
  have htailtP : p < m.next := hinv.htailt _ rfl
  cases hsrcB with
  | @cons a₀ t₀ v₀ nL vs₀ hnode hltB t2B =>
    have hcell : cellsAt m a t₀ [w, linkWord nL] := hnode
    have hL0 : memLoad m a t₀ 0 = .ok w :=
      memLoad_cellsAt m a t₀ 0 [w, linkWord nL] w hcell
        (by simp)
    have hL1 : memLoad m a t₀ 1 = .ok (linkWord nL) :=
      memLoad_cellsAt m a t₀ 1 [w, linkWord nL] (linkWord nL)
        hcell (by simp)
    have hdec : addrOfWord (linkWord nL) = nL :=
      nodeAt_link_roundtrip hnode hinv.hex
        (ListSeg_start_alloc (BoundedSeg.toListSeg t2B))
    have hmfresh : memFind m m.next = none :=
      hinv.hmark _ (Nat.le_refl _)
    have hnd : (memAlloc m 2).2 = m.next := memAlloc_next m 2
    have h1next : (memAlloc m 2).1.next = m.next + 1 := rfl
    have hbridge : (memAlloc m 2).1 =
        (memAllocData m (List.replicate 2 0)).1 := rfl
    have hmark1 : Mark (memAlloc m 2).1 :=
      freshAbove_alloc m 2 hinv.hmark
    have hex1 : ∀ x, (memFind (memAlloc m 2).1 x).isSome = true →
        x + 1 < 2 ^ 32 := by
      have h := hex_alloc hinv.hex hinv.hroom0 hinv.hroom
        (List.replicate 2 0)
      rwa [← hbridge] at h
    have hfindN : memFind (memAlloc m 2).1 (memAlloc m 2).2 =
        some ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ :=
      memFind_memAlloc m 2
    have hcell0 : cellsAt (memAlloc m 2).1 (memAlloc m 2).2
        ((memAlloc m 2).2) [0, 0] := hfindN
    obtain ⟨m2, hS1⟩ := memStore_cellsAt_ok (i := 0) hcell0
      (by decide)
    have hcell1 : cellsAt m2 (memAlloc m 2).2
        ((memAlloc m 2).2) [w, 0] := by
      have h := memFind_cellsAt_store _ _ _ _ _ _ _ hcell0
        (by decide) hS1
      simpa using h
    obtain ⟨m3, hS2⟩ := memStore_cellsAt_ok (i := 1) hcell1
      (by simp)
    have hcell2 : cellsAt m3 (memAlloc m 2).2
        ((memAlloc m 2).2) [w, linkWord none] := by
      have h := memFind_cellsAt_store _ _ _ _ _ _ _ hcell1
        (by simp) hS2
      simpa using h
    have hndN : nodeAt m3 (memAlloc m 2).2 ((memAlloc m 2).2)
        w none := hcell2
    have hmark2 : Mark m2 := freshAbove_store hmark1 hS1
    have hmark3 : Mark m3 := freshAbove_store hmark2 hS2
    have ha1 : (memFind (memAlloc m 2).1
        (memAlloc m 2).2).isSome = true := by
      rw [hfindN]
      rfl
    have hex2 : ∀ x, (memFind m2 x).isSome = true →
        x + 1 < 2 ^ 32 :=
      hex_store hex1 hS1 ha1
    have hfind2 : memFind m2 (memAlloc m 2).2 = some _ := hcell1
    have ha2 : (memFind m2 (memAlloc m 2).2).isSome = true := by
      rw [hfind2]
      rfl
    have hex3 : ∀ x, (memFind m3 x).isSome = true →
        x + 1 < 2 ^ 32 :=
      hex_store hex2 hS2 ha2
    have h2next : m2.next = (memAlloc m 2).1.next :=
      memStore_next hS1
    have h3next : m3.next = m2.next := memStore_next hS2
    have hdiff : ∀ (c t : Nat) (v : BitVec 32) (n : Option Addr),
        nodeAt m c t v n → c ≠ m.next := by
      intro c t v n hc heq
      have hfind : memFind m c = some _ := hc
      rw [heq] at hfind
      rw [hmfresh] at hfind
      simp at hfind
    have hfull3 := BoundedSeg.alloc_stores_other hinv.hfullB
      hmfresh hnd rfl hS1 hS2
    have hsrc3pre := BoundedSeg.alloc_stores_other t2B hmfresh
      hnd rfl hS1 hS2
    have hsrc3 : BoundedSeg m3 n₀ (· < n₀)
        (addrOfWord (linkWord nL)) ws := by
      rw [hdec]
      exact hsrc3pre
    have hPnd : n₀ ≤ (memAlloc m 2).2 := by
      rw [hnd]
      exact hnextge
    have hdstB3 := BoundedSeg.alloc_stores_other hinv.hdstB
      hmfresh hnd rfl hS1 hS2
    -- The old tail rides the allocation plus the two
    -- fresh-cell stores (its address is shared, so the
    -- freshness side conditions rewrite to `hdiff`).
    have hneP : p ≠ (memAlloc m 2).2 := by
      rw [hnd]
      exact Nat.ne_of_lt htailtP
    have hlast1 := nodeAt_alloc_other hlast (List.replicate 2 0)
      (Nat.ne_of_lt htailtP)
    rw [← hbridge] at hlast1
    have hlast2 := nodeAt_store_other_fwd hlast1 hS1 hneP
    have hlast3 : nodeAt m3 p tp wp none :=
      nodeAt_store_other_fwd hlast2 hS2 hneP
    -- Destination reachability rides the allocation plus the
    -- two fresh-cell stores (three-step transport kit lemma).
    have hmem3 : SegMem (m := m3) nh p :=
      SegMem_alloc_stores_other_fwd hmem0 hmfresh hnd rfl hS1 hS2
    -- The swing store into the old tail's link cell.
    have hcellP : cellsAt m3 p tp [wp, linkWord none] := hlast3
    obtain ⟨m4, hS4⟩ := memStore_cellsAt_ok (i := 1) hcellP
      (by simp)
    have hcellP' : cellsAt m4 p tp
        [wp, linkWord (some ((memAlloc m 2).2))] := by
      have h := memFind_cellsAt_store _ _ _ _ _ _ _ hcellP
        (by simp) hS4
      simpa using h
    have hswingP : nodeAt m4 p tp wp (some ((memAlloc m 2).2)) :=
      hcellP'
    have h4next : m4.next = m3.next := memStore_next hS4
    have hnd4 := nodeAt_store_other_fwd hndN hS4 (by
      rw [hnd]
      exact Ne.symm (Nat.ne_of_lt htailtP))
    have hPp : n₀ ≤ p :=
      BoundedSeg_mem hinv.hex hinv.hdstB hmem0
    have hdst4 := BoundedSeg_swing_snoc hex3 hdstB3 hlast3
      hmem3 hS4 hswingP hnd4 hPp hPnd
    -- Source segments ride the swing store (per-node bounds
    -- from the derivation separate every node from `p`).
    have hfull4 : BoundedSeg m4 n₀ (· < n₀) head vs₀ :=
      BoundedSeg.store_other_sep hfull3
        (fun a ha => Nat.ne_of_lt (Nat.lt_of_lt_of_le ha hPp)) hS4
    have hsrc4 : BoundedSeg m4 n₀ (· < n₀)
        (addrOfWord (linkWord nL)) ws :=
      BoundedSeg.store_other_sep hsrc3
        (fun a ha => Nat.ne_of_lt (Nat.lt_of_lt_of_le ha hPp)) hS4
    have hmark4 : Mark m4 := freshAbove_store hmark3 hS4
    have hfindP : memFind m3 p = some _ := hlast3
    have ha3 : (memFind m3 p).isSome = true := by
      rw [hfindP]
      rfl
    have hex4 : ∀ x, (memFind m4 x).isSome = true →
        x + 1 < 2 ^ 32 :=
      hex_store hex3 hS4 ha3
    have hnextge3 : n₀ ≤ m3.next := by
      rw [h3next, h2next, h1next]
      exact Nat.le_succ_of_le hnextge
    have hnextge4 : n₀ ≤ m4.next := by
      rw [h4next]
      exact hnextge3
    have hlen_eq : (w :: ws).length = ws.length + 1 := rfl
    have hroom3 : m3.next + ws.length ≤ n₀ + vs₀.length := by
      have hr := hroom
      rw [hlen_eq] at hr
      rw [h3next, h2next, h1next]
      omega
    have hroom4 : m4.next + ws.length ≤ n₀ + vs₀.length := by
      rw [h4next]
      exact hroom3
    have hlen3 : ws.length ≤ F := by
      have hl := hlen
      rw [hlen_eq] at hl
      omega
    have hsplit4 : (pref ++ [w]) ++ ws = vs₀ := by
      rw [List.append_assoc]
      exact hinv.hsplit
    have htailt3 :
        ∀ q, (some ((memAlloc m 2).2)) = some q →
          q < m3.next := by
      intro q hq
      cases hq
      rw [hnd, h3next, h2next, h1next]
      exact Nat.lt_succ_self _
    have hmemtail4 :
        ∀ q, (some ((memAlloc m 2).2)) = some q →
          SegMem (m := m4) nh q := by
      intro q hq
      cases hq
      exact SegMem_snoc
        (SegMem_swing_replace hex3 hdstB3.toListSeg hmem3 hS4
          hswingP)
        hswingP hnd4
    have hlastP4 :
        ∀ q, (some ((memAlloc m 2).2)) = some q →
          ∃ tp wp, nodeAt m4 q tp wp none := by
      intro q hq
      cases hq
      exact ⟨_, _, hnd4⟩
    have htailt4 :
        ∀ q, (some ((memAlloc m 2).2)) = some q →
          q < m4.next := by
      intro q hq
      cases hq
      rw [h4next]
      exact htailt3 _ rfl
    exact ⟨_, _, m2, m3, m4, _, _, _, _,
      rfl, hL0, hL1, hS1, hS2, hcell1, hS4, hlast3,
      { hfullB := hfull4
        hsrcB := hsrc4
        hdstB := hdst4
        hmemtail := hmemtail4
        hlastP := hlastP4
        htailt := htailt4
        hmark := hmark4
        hex := hex4
        hnextge := hnextge4
        hroom := hroom4
        hlen := hlen3
        hsplit := hsplit4
        hcoh := fun h => by cases h
        hroom0 := hinv.hroom0 }⟩

/-- A live segment sits below the high-water mark (entry
    bridge: `ListSeg` plus `Mark` gives the below-mark bounded
    segment — every node is live, hence below `next`). -/
theorem ListSeg.toBoundedSeg_lt {m : Mem} {head : Option Addr}
    {vs : List (BitVec 32)} (h : ListSeg m head vs)
    (hmark : Mark m) :
    BoundedSeg m m.next (· < m.next) head vs := by
  induction h with
  | nil => exact .nil
  | cons hnode _ ih =>
      exact .cons hnode (live_lt_of_memFind hmark hnode) ih

/-- The copy invariant lifts to larger fuel (only the length
    bound mentions fuel — one step down the bound). -/
theorem CopyInv.lift {n₀ : Nat} {vs₀ : List (BitVec 32)} {F : Nat}
    {m : Mem} {head cur nh tail : Option Addr}
    {pref suf : List (BitVec 32)}
    (h : CopyInv n₀ vs₀ F m head cur nh tail pref suf) :
    CopyInv n₀ vs₀ (F + 1) m head cur nh tail pref suf :=
  { h with hlen := Nat.le_succ_of_le h.hlen }

/-- The copy chase is correct: from any reachable invariant it
    returns `ok`, exhausts the source, and leaves the full
    destination behind (`pref ++ suf`). -/
theorem listCopyChase_ok {n₀ : Nat} {vs₀ : List (BitVec 32)}
    (F : Nat) :
    ∀ (m : Mem) (head cur nh tail : Option Addr)
      (pref suf : List (BitVec 32))
      (hinv : CopyInv n₀ vs₀ F m head cur nh tail pref suf),
    ∃ m' nh' tail' pref',
      listCopyChase F m cur nh tail = .ok (m', nh', tail') ∧
      CopyInv n₀ vs₀ F m' head none nh' tail' pref' [] ∧
      pref' = pref ++ suf := by
  induction F with
  | zero =>
      intro m head cur nh tail pref suf hinv
      cases hinv.hsrcB with
      | nil =>
          refine ⟨m, nh, tail, pref, ?_, hinv, by simp⟩
          simp [listCopyChase]
      | cons hnode hP t2 =>
          have h := hinv.hlen
          simp only [List.length_cons] at h
          omega
  | succ F ih =>
      intro m head cur nh tail pref suf hinv
      cases hinv.hsrcB with
      | nil =>
          refine ⟨m, nh, tail, pref, ?_, hinv, by simp⟩
          simp [listCopyChase]
      | cons hnode hltB t2B =>
          rename_i a₀ t₀ v₀ nL vs₀
          have hcell : cellsAt m a₀ t₀ [v₀, linkWord nL] := hnode
          have hfb : memFind m a₀ =
              some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode
          have hL0' : memLoad m a₀ t₀ 0 = .ok v₀ :=
            memLoad_cellsAt m a₀ t₀ 0 [v₀, linkWord nL] v₀
              hcell (by simp)
          cases tail with
          | none =>
              obtain ⟨hpref0, hnh0⟩ := hinv.hcoh rfl
              subst hpref0
              subst hnh0
              obtain ⟨nd, m1, m2, m3, t, lw, hA, hL0, hL1, hS1,
                hS2, _hcellS, hinv'⟩ := copy_step_none hinv
              have hteq : t = t₀ := memLoad_tag hL0 hfb
              subst hteq
              obtain ⟨m', nh', tail', pref'', hC', hinv'',
                hpref''⟩ :=
                ih m3 head (addrOfWord lw) (some nd) (some nd)
                  ([] ++ [v₀]) vs₀ hinv'
              refine ⟨m', nh', tail', pref'', ?_, hinv''.lift,
                ?_⟩
              · unfold listCopyChase
                simp only [hfb]
                simp only [hL0, hL1, hA, hS1, hS2, hC']
              · rw [hpref'']
                simp
          | some p =>
              obtain ⟨nd, m1, m2, m3, m4, t, tp, lw, wp, hA, hL0,
                hL1, hS1, hS2, _hcellS, hS4, hlast3, hinv'⟩ :=
                copy_step_some hinv
              have hteq : t = t₀ := memLoad_tag hL0 hfb
              subst hteq
              have hfindP : memFind m3 p =
                  some ⟨tp, true, [wp, linkWord none]⟩ := hlast3
              obtain ⟨m', nh', tail', pref'', hC', hinv'',
                hpref''⟩ :=
                ih m4 head (addrOfWord lw) nh (some nd)
                  (pref ++ [v₀]) vs₀ hinv'
              refine ⟨m', nh', tail', pref'', ?_, hinv''.lift,
                ?_⟩
              · unfold listCopyChase
                simp only [hfb]
                simp only [hL0, hL1, hA, hS1, hS2, hfindP, hS4,
                  hC']
              · rw [hpref'']
                simp

/-- The entry invariant: full source below the mark, empty
    destination, cursor at the head (all freshness bounds hold
    with room to spare). -/
theorem copyEntryInv {vs₀ : List (BitVec 32)} {F : Nat}
    {m : Mem} {head : Option Addr}
    (hmark : Mark m)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hseg : ListSeg m head vs₀)
    (hlen : vs₀.length ≤ F)
    (hroom0 : m.next + vs₀.length + 1 < 2 ^ 32) :
    CopyInv m.next vs₀ F m head head none none [] vs₀ :=
  { hfullB := ListSeg.toBoundedSeg_lt hseg hmark
    hsrcB := ListSeg.toBoundedSeg_lt hseg hmark
    hdstB := .nil
    hmemtail := fun p h => by cases h
    hlastP := fun p h => by cases h
    htailt := fun p h => by cases h
    hmark := hmark
    hex := hex
    hnextge := Nat.le_refl _
    hroom := Nat.le_refl _
    hlen := hlen
    hsplit := by simp
    hcoh := fun _ => ⟨rfl, rfl⟩
    hroom0 := hroom0 }

/-- The forward mirror is correct: the returned chain holds the
    input payloads in order, the input chain is untouched, every
    returned cell is fresh (at or above the entry high-water
    mark), and the two chains are disjoint. -/
theorem listCopyFwd_correct {vs₀ : List (BitVec 32)} {F : Nat}
    {m : Mem} {head : Option Addr} {m' : Mem} {nh' : Option Addr}
    (hmark : Mark m)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hseg : ListSeg m head vs₀)
    (hlen : vs₀.length ≤ F)
    (hroom0 : m.next + vs₀.length + 1 < 2 ^ 32)
    (hfwd : listCopyFwd F m head = .ok (m', nh')) :
    ListSeg m' nh' vs₀ ∧ ListSeg m' head vs₀ ∧
      (∀ a, SegMem (m := m') nh' a → m.next ≤ a) ∧
      (∀ a, SegMem (m := m') head a →
        SegMem (m := m') nh' a → False) := by
  have hinv := copyEntryInv hmark hex hseg hlen hroom0
  obtain ⟨mC', nhC', tail', pref', hC, hinv', hpref'⟩ :=
    listCopyChase_ok F m head head none none [] vs₀ hinv
  unfold listCopyFwd at hfwd
  rw [hC] at hfwd
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
  obtain ⟨e1, e2⟩ := hfwd
  subst e1
  subst e2
  have hdst : ListSeg mC' nhC' pref' := hinv'.hdstB.toListSeg
  rw [hpref'] at hdst
  simp only [List.nil_append] at hdst
  refine ⟨hdst, hinv'.hfullB.toListSeg, ?_, ?_⟩
  · intro a hmem
    exact BoundedSeg_mem hinv'.hex hinv'.hdstB hmem
  · intro a hs hd
    have h1 : a < m.next := BoundedSeg_mem hinv'.hex hinv'.hfullB hs
    have h2 : m.next ≤ a := BoundedSeg_mem hinv'.hex hinv'.hdstB hd
    exact absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.lt_irrefl _)


/-- The loop agrees with the chase: from any reachable invariant
    the evaluator runs the loop to fall-through, threading the
    `nd` shadows, and lands in the chase's final memory with the
    new head, the final tail, and an exhausted cursor. -/
theorem listCopyLoop_agree {n₀ : Nat} {vs₀ : List (BitVec 32)}
    (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (head : Option Addr)
      (cur nh tail : Option Addr) (nds : List Addr)
      (pref suf : List (BitVec 32))
      (hinv : CopyInv n₀ vs₀ F m head cur nh tail pref suf)
      (m' : Mem) (nh' tail' : Option Addr)
      (hC : listCopyChase F m cur nh tail = .ok (m', nh', tail')),
    ∃ nds',
      memEvalStmtFuel F listCopyLoop
        (mkListCopyEnv head nh tail cur nds) m π =
        .ok (((mkListCopyEnv head nh' tail' none nds'), m', π),
          .fellThrough) := by
  induction F with
  | zero =>
      intro m π hex head cur nh tail nds pref suf hinv
        m' nh' tail' hC
      cases hinv.hsrcB with
      | nil =>
          have hC' : listCopyChase 0 m none nh tail =
              .ok (m, nh, tail) := by
            simp [listCopyChase]
          rw [hC'] at hC
          simp only [Except.ok.injEq, Prod.mk.injEq] at hC
          obtain ⟨e1, e2, e3⟩ := hC
          subst e1
          subst e2
          subst e3
          refine ⟨nds, ?_⟩
          have hcurE : memEvalExpr (.var "cur")
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (.ptrVal none) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListCopyEnv_cur _ _ _ _ _)
          have hnullE : memEvalExpr (.lit .nullptr)
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (.ptrVal none) := by
            simp [memEvalExpr, litVal]
          have hgF : memEvalExpr
              (.une (.var "cur") (.lit .nullptr))
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (.b false) := by
            have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
              hcurE hnullE
            have hbe : ((none : Option Addr) != none) = false := by
              simp
            rw [hbe] at hg
            exact hg
          have hw : memEvalStmtFuel 0 listCopyLoop
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (((mkListCopyEnv head nh tail none nds, m, π)),
                .fellThrough) :=
            memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
          exact hw
      | cons hnode hP t2 =>
          have h := hinv.hlen
          simp only [List.length_cons] at h
          omega
  | succ F ih =>
      intro m π hex head cur nh tail nds pref suf hinv
        m' nh' tail' hC
      cases hinv.hsrcB with
      | nil =>
          have hC' : listCopyChase (F + 1) m none nh tail =
              .ok (m, nh, tail) := by
            simp [listCopyChase]
          rw [hC'] at hC
          simp only [Except.ok.injEq, Prod.mk.injEq] at hC
          obtain ⟨e1, e2, e3⟩ := hC
          subst e1
          subst e2
          subst e3
          refine ⟨nds, ?_⟩
          have hcurE : memEvalExpr (.var "cur")
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (.ptrVal none) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListCopyEnv_cur _ _ _ _ _)
          have hnullE : memEvalExpr (.lit .nullptr)
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (.ptrVal none) := by
            simp [memEvalExpr, litVal]
          have hgF : memEvalExpr
              (.une (.var "cur") (.lit .nullptr))
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (.b false) := by
            have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
              hcurE hnullE
            have hbe : ((none : Option Addr) != none) = false := by
              simp
            rw [hbe] at hg
            exact hg
          have hw : memEvalStmtFuel (F + 1) listCopyLoop
              (mkListCopyEnv head nh tail none nds) m π =
              .ok (((mkListCopyEnv head nh tail none nds, m, π)),
                .fellThrough) :=
            memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
          exact hw
      | cons hnode hltB t2B =>
          rename_i a₀ t₀ v₀ nL vs₀
          have hcell : cellsAt m a₀ t₀ [v₀, linkWord nL] := hnode
          have hfb : memFind m a₀ =
              some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode
          have hL0' : memLoad m a₀ t₀ 0 = .ok v₀ :=
            memLoad_cellsAt m a₀ t₀ 0 [v₀, linkWord nL] v₀
              hcell (by simp)
          have hL1' : memLoad m a₀ t₀ 1 = .ok (linkWord nL) :=
            memLoad_cellsAt m a₀ t₀ 1 [v₀, linkWord nL]
              (linkWord nL) hcell (by simp)
          have hltA : a₀ < m.next :=
            live_lt_of_memFind hinv.hmark hnode
          cases tail with
          | none =>
              obtain ⟨hpref0, hnh0⟩ := hinv.hcoh rfl
              subst hpref0
              subst hnh0
              obtain ⟨nd, m1, m2, m3, t, lw, hA, hL0, hL1, hS1,
                hS2, hcellS, hinv'⟩ := copy_step_none hinv
              have hteq : t = t₀ := memLoad_tag hL0 hfb
              subst t
              have hlweq : lw = linkWord nL := by
                have h := hL1.symm.trans hL1'
                simpa using h
              subst hlweq
              have hAfst : (memAlloc m 2).1 = m1 :=
                congrArg Prod.fst hA
              have hAsnd : (memAlloc m 2).2 = nd :=
                congrArg Prod.snd hA
              have hndM : (memAlloc m 2).2 = m.next :=
                memAlloc_next m 2
              have hfindN : memFind m1 nd =
                  some ⟨nd, true, List.replicate 2 0⟩ := by
                rw [← hAfst, ← hAsnd]
                exact memFind_memAlloc m 2
              have hfind2 : memFind m2 nd =
                  some ⟨nd, true, [v₀, 0]⟩ := by
                rw [hAsnd] at hcellS
                exact hcellS
              have hbridge : (memAlloc m 2).1 =
                  (memAllocData m (List.replicate 2 0)).1 := rfl
              have hnode1 : nodeAt m1 a₀ t₀ v₀ nL := by
                have h := nodeAt_alloc_other hnode
                  (List.replicate 2 0) (Nat.ne_of_lt hltA)
                rw [← hbridge, hAfst] at h
                exact h
              have hnode3 : nodeAt m3 a₀ t₀ v₀ nL := by
                have h2 := nodeAt_store_other_fwd hnode1 hS1 (by
                  rw [← hAsnd, hndM]
                  exact Nat.ne_of_lt hltA)
                exact nodeAt_store_other_fwd h2 hS2 (by
                  rw [← hAsnd, hndM]
                  exact Nat.ne_of_lt hltA)
              have hC' : listCopyChase F m3
                  (addrOfWord (linkWord nL)) (some nd)
                  (some nd) = .ok (m', nh', tail') := by
                unfold listCopyChase at hC
                simp only [hfb, hL0, hL1, hA, hS1, hS2] at hC
                exact hC
              obtain ⟨nds', hIH⟩ :=
                ih m3 π hinv'.hex head (addrOfWord (linkWord nL))
                  (some nd) (some nd) (nd :: nds) ([] ++ [v₀])
                  vs₀ hinv' m' nh' tail' hC'
              refine ⟨nds', ?_⟩
              have hcurE : memEvalExpr (.var "cur")
                  (mkListCopyEnv head none none (some a₀) nds)
                  m π = .ok (.ptrVal (some a₀)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_cur _ _ _ _ _)
              have hnullE : memEvalExpr (.lit .nullptr)
                  (mkListCopyEnv head none none (some a₀) nds)
                  m π = .ok (.ptrVal none) := by
                simp [memEvalExpr, litVal]
              have hgT : memEvalExpr
                  (.une (.var "cur") (.lit .nullptr))
                  (mkListCopyEnv head none none (some a₀) nds)
                  m π = .ok (.b true) := by
                have hg := memEvalExpr_une_ptrVal _ _ _ _ _
                  (some a₀) none hcurE hnullE
                have hbe : ((some a₀) != none) = true := by simp
                rw [hbe] at hg
                exact hg
              have hE1 : (("nd", .ptrVal (some nd)) ::
                  mkListCopyEnv head none none (some a₀) nds) =
                  mkListCopyEnv head none none (some a₀)
                    (nd :: nds) := rfl
              have hlet : memEvalStmtFuel F
                  (.let_ "nd" nodeTy .nnew)
                  (mkListCopyEnv head none none (some a₀) nds)
                  m π =
                  .ok (((mkListCopyEnv head none none (some a₀)
                    (nd :: nds), m1, π)), .fellThrough) := by
                have h := memEvalStmtFuel_let_nnew F "nd" nodeTy
                  (mkListCopyEnv head none none (some a₀) nds)
                  m π
                simp only [hA] at h
                rw [hE1] at h
                exact h
              have hdN : memEvalExpr (.var "nd")
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (.ptrVal (some nd)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hcurE1 : memEvalExpr (.var "cur")
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (.ptrVal (some a₀)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_cur _ _ _ _ _)
              have hfb1 : memFind m1 a₀ =
                  some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode1
              have hcellA1 : cellsAt m1 a₀ t₀
                  [v₀, linkWord nL] := hnode1
              have hLd0 : memLoad m1 a₀ t₀ 0 = .ok v₀ :=
                memLoad_cellsAt m1 a₀ t₀ 0 [v₀, linkWord nL] v₀
                  hcellA1 (by simp)
              have hvP : memEvalExpr
                  (.pgetVal (.var "cur"))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m1 π = .ok (.i32 v₀) :=
                memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE1
                  hfb1 hLd0
              have hpsetV : memEvalStmtFuel F
                  (.psetVal (.var "nd") (.pgetVal (.var "cur")))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (((mkListCopyEnv head none none (some a₀)
                    (nd :: nds), m2, π)), .fellThrough) :=
                memEvalStmtFuel_psetVal_ok F (.var "nd")
                  (.pgetVal (.var "cur"))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m1 π nd v₀
                  ⟨nd, true, List.replicate 2 0⟩ m2 hdN hvP
                  hfindN hS1
              have hdN2 : memEvalExpr (.var "nd")
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (.ptrVal (some nd)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hnullE2 : memEvalExpr (.lit .nullptr)
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (.ptrVal none) := by
                simp [memEvalExpr, litVal]
              have hpsetN : memEvalStmtFuel F
                  (.psetNext (.var "nd") (.lit .nullptr))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (((mkListCopyEnv head none none (some a₀)
                    (nd :: nds), m3, π)), .fellThrough) :=
                memEvalStmtFuel_psetNext_ok F (.var "nd")
                  (.lit .nullptr)
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m2 π nd none
                  ⟨nd, true, [v₀, 0]⟩ m3 hdN2 hnullE2 hfind2 hS2
              have htailE : memEvalExpr (.var "tail")
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (.ptrVal none) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_tail _ _ _ _ _)
              have hnullE3 : memEvalExpr (.lit .nullptr)
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (.ptrVal none) := by
                simp [memEvalExpr, litVal]
              have hueqT : memEvalExpr
                  (.ueq (.var "tail") (.lit .nullptr))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π = .ok (.b true) := by
                have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _
                  none none htailE hnullE3
                have hbe : ((none : Option Addr) == none) =
                    true := by simp
                rw [hbe] at hg
                exact hg
              have hubaseH : envUpdate
                  (mkListCopyBase head none none (some a₀))
                  "new_head" (.ptrVal (some nd)) =
                  some [("cur", .ptrVal (some a₀)),
                    ("tail", .ptrVal none),
                    ("new_head", .ptrVal (some nd)),
                    ("head", .ptrVal head)] := by
                simp [mkListCopyBase, envUpdate]
              have hmissH : ∀ k w, (k, w) ∈ ndShadows (nd :: nds) →
                  k ≠ "new_head" := by
                intro k w hmem hcon
                have hk := ndShadows_keys (nd :: nds) k w hmem
                rw [hk] at hcon
                exact absurd hcon (by decide)
              have huH : envUpdate
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) "new_head"
                  (.ptrVal (some nd)) =
                  some (mkListCopyEnv head (some nd) none
                    (some a₀) (nd :: nds)) := by
                simp only [mkListCopyEnv]
                exact envUpdate_append_miss _ _ _ _ _
                  hmissH hubaseH
              have hdN3eq : memEvalExpr (.var "nd")
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π =
                  evalExpr (.var "nd")
                    (mkListCopyEnv head none none (some a₀)
                      (nd :: nds)) :=
                memEvalExpr_var _ _ _ _
              have hvnd : evalExpr (.var "nd")
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) =
                  .ok (.ptrVal (some nd)) :=
                evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hassignH : memEvalStmtFuel F
                  (.assign "new_head" (.var "nd"))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head (some nd) none
                    (some a₀) (nd :: nds), m3, π)),
                    .fellThrough) :=
                memEvalStmtFuel_assign F "new_head"
                  (.var "nd")
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π (.ptrVal (some nd))
                  (mkListCopyEnv head (some nd) none
                    (some a₀) (nd :: nds)) hdN3eq hvnd huH
              have hifT : memEvalStmtFuel F
                  (.if_ (.ueq (.var "tail") (.lit .nullptr))
                    (.assign "new_head" (.var "nd"))
                    (.psetNext (.var "tail") (.var "nd")))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head (some nd) none
                    (some a₀) (nd :: nds), m3, π)),
                    .fellThrough) :=
                (memEvalStmtFuel_if_true F _ _ _ _ _ _ hueqT).trans
                  hassignH
              have hubaseT : envUpdate
                  (mkListCopyBase head (some nd) none
                    (some a₀)) "tail" (.ptrVal (some nd)) =
                  some [("cur", .ptrVal (some a₀)),
                    ("tail", .ptrVal (some nd)),
                    ("new_head", .ptrVal (some nd)),
                    ("head", .ptrVal head)] := by
                simp [mkListCopyBase, envUpdate]
              have hmissT : ∀ k w, (k, w) ∈ ndShadows (nd :: nds) →
                  k ≠ "tail" := by
                intro k w hmem hcon
                have hk := ndShadows_keys (nd :: nds) k w hmem
                rw [hk] at hcon
                exact absurd hcon (by decide)
              have huT : envUpdate
                  (mkListCopyEnv head (some nd) none (some a₀)
                    (nd :: nds)) "tail" (.ptrVal (some nd)) =
                  some (mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds)) := by
                simp only [mkListCopyEnv]
                exact envUpdate_append_miss _ _ _ _ _
                  hmissT hubaseT
              have hdN4eq : memEvalExpr (.var "nd")
                  (mkListCopyEnv head (some nd) none (some a₀)
                    (nd :: nds)) m3 π =
                  evalExpr (.var "nd")
                    (mkListCopyEnv head (some nd) none
                      (some a₀) (nd :: nds)) :=
                memEvalExpr_var _ _ _ _
              have hvnd2 : evalExpr (.var "nd")
                  (mkListCopyEnv head (some nd) none (some a₀)
                    (nd :: nds)) =
                  .ok (.ptrVal (some nd)) :=
                evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hassignT : memEvalStmtFuel F
                  (.assign "tail" (.var "nd"))
                  (mkListCopyEnv head (some nd) none (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds), m3, π)),
                    .fellThrough) :=
                memEvalStmtFuel_assign F "tail" (.var "nd")
                  (mkListCopyEnv head (some nd) none (some a₀)
                    (nd :: nds)) m3 π (.ptrVal (some nd))
                  (mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds)) hdN4eq hvnd2 huT
              have hcurE3 : memEvalExpr (.var "cur")
                  (mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds)) m3 π =
                  .ok (.ptrVal (some a₀)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_cur _ _ _ _ _)
              have hfb3 : memFind m3 a₀ =
                  some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode3
              have hcellA3 : cellsAt m3 a₀ t₀
                  [v₀, linkWord nL] := hnode3
              have hLd1 : memLoad m3 a₀ t₀ 1 =
                  .ok (linkWord nL) :=
                memLoad_cellsAt m3 a₀ t₀ 1 [v₀, linkWord nL]
                  (linkWord nL) hcellA3 (by simp)
              have hpgn : memEvalExpr
                  (.pgetNext (.var "cur"))
                  (mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds)) m3 π =
                  .ok (.ptrVal (addrOfWord (linkWord nL))) :=
                memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE3
                  hfb3 hLd1
              have hubaseC : envUpdate
                  (mkListCopyBase head (some nd) (some nd)
                    (some a₀)) "cur"
                  (.ptrVal (addrOfWord (linkWord nL))) =
                  some [("cur",
                    .ptrVal (addrOfWord (linkWord nL))),
                    ("tail", .ptrVal (some nd)),
                    ("new_head", .ptrVal (some nd)),
                    ("head", .ptrVal head)] := by
                simp [mkListCopyBase, envUpdate]
              have hmissC : ∀ k w, (k, w) ∈ ndShadows (nd :: nds) →
                  k ≠ "cur" := by
                intro k w hmem hcon
                have hk := ndShadows_keys (nd :: nds) k w hmem
                rw [hk] at hcon
                exact absurd hcon (by decide)
              have huC : envUpdate
                  (mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds)) "cur"
                  (.ptrVal (addrOfWord (linkWord nL))) =
                  some (mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL))
                    (nd :: nds)) := by
                simp only [mkListCopyEnv]
                exact envUpdate_append_miss _ _ _ _ _
                  hmissC hubaseC
              have hassignC : memEvalStmtFuel F
                  (.assign "cur" (.pgetNext (.var "cur")))
                  (mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m3, π)), .fellThrough) :=
                memEvalStmtFuel_assign_mem F "cur"
                  (.pgetNext (.var "cur"))
                  (mkListCopyEnv head (some nd) (some nd)
                    (some a₀) (nd :: nds)) m3 π
                  (.ptrVal (addrOfWord (linkWord nL)))
                  (mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds))
                  hpgn huC
              have h34 : memEvalStmtFuel F
                  (.seq (.assign "tail" (.var "nd"))
                    (.assign "cur" (.pgetNext (.var "cur"))))
                  (mkListCopyEnv head (some nd) none (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m3, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hassignT hassignC
              have h234 : memEvalStmtFuel F
                  (.seq (.if_ (.ueq (.var "tail")
                      (.lit .nullptr))
                      (.assign "new_head" (.var "nd"))
                      (.psetNext (.var "tail") (.var "nd")))
                    (.seq (.assign "tail" (.var "nd"))
                      (.assign "cur"
                        (.pgetNext (.var "cur")))))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m3, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hifT h34
              have h1234 : memEvalStmtFuel F
                  (.seq (.psetNext (.var "nd")
                      (.lit .nullptr))
                    (.seq (.if_ (.ueq (.var "tail")
                        (.lit .nullptr))
                        (.assign "new_head" (.var "nd"))
                        (.psetNext (.var "tail") (.var "nd")))
                      (.seq (.assign "tail" (.var "nd"))
                        (.assign "cur"
                          (.pgetNext (.var "cur"))))))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (((mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m3, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hpsetN h234
              have h01234 : memEvalStmtFuel F
                  (.seq (.psetVal (.var "nd")
                      (.pgetVal (.var "cur")))
                    (.seq (.psetNext (.var "nd")
                        (.lit .nullptr))
                      (.seq (.if_ (.ueq (.var "tail")
                          (.lit .nullptr))
                          (.assign "new_head" (.var "nd"))
                          (.psetNext (.var "tail")
                            (.var "nd")))
                        (.seq (.assign "tail" (.var "nd"))
                          (.assign "cur"
                            (.pgetNext (.var "cur")))))))
                  (mkListCopyEnv head none none (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (((mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m3, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hpsetV h1234
              have hbody : memEvalStmtFuel F listCopyLoopBody
                  (mkListCopyEnv head none none (some a₀) nds)
                  m π =
                  .ok (((mkListCopyEnv head (some nd) (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m3, π)), .fellThrough) := by
                unfold listCopyLoopBody
                exact memEvalStmtFuel_seq_fallthrough_trans F _ _
                  _ _ _ _ _ _ _ hlet h01234
              unfold listCopyLoop
              rw [memEvalStmtFuel_while_true F _ _ _ _ _ hgT,
                hbody]
              exact hIH
          | some p =>
              obtain ⟨nd, m1, m2, m3, m4, t, tp, lw, wp, hA, hL0,
                hL1, hS1, hS2, hcellS, hS4, hlast3, hinv'⟩ :=
                copy_step_some hinv
              have hteq : t = t₀ := memLoad_tag hL0 hfb
              subst t
              have hlweq : lw = linkWord nL := by
                have h := hL1.symm.trans hL1'
                simpa using h
              subst hlweq
              have hAfst : (memAlloc m 2).1 = m1 :=
                congrArg Prod.fst hA
              have hAsnd : (memAlloc m 2).2 = nd :=
                congrArg Prod.snd hA
              have hndM : (memAlloc m 2).2 = m.next :=
                memAlloc_next m 2
              have hfindN : memFind m1 nd =
                  some ⟨nd, true, List.replicate 2 0⟩ := by
                rw [← hAfst, ← hAsnd]
                exact memFind_memAlloc m 2
              have hfind2 : memFind m2 nd =
                  some ⟨nd, true, [v₀, 0]⟩ := by
                rw [hAsnd] at hcellS
                exact hcellS
              have hfindP : memFind m3 p =
                  some ⟨tp, true, [wp, linkWord none]⟩ := hlast3
              have hltB' : a₀ < n₀ := hltB
              have hPp' : n₀ ≤ p :=
                BoundedSeg_mem hinv.hex hinv.hdstB
                  (hinv.hmemtail _ rfl)
              have hbridge : (memAlloc m 2).1 =
                  (memAllocData m (List.replicate 2 0)).1 := rfl
              have hnode1 : nodeAt m1 a₀ t₀ v₀ nL := by
                have h := nodeAt_alloc_other hnode
                  (List.replicate 2 0) (Nat.ne_of_lt hltA)
                rw [← hbridge, hAfst] at h
                exact h
              have hside12 : a₀ ≠ nd := by
                rw [← hAsnd, hndM]
                exact Nat.ne_of_lt hltA
              have hnode2 : nodeAt m2 a₀ t₀ v₀ nL :=
                nodeAt_store_other_fwd hnode1 hS1 hside12
              have hnode3 : nodeAt m3 a₀ t₀ v₀ nL :=
                nodeAt_store_other_fwd hnode2 hS2 hside12
              have hside4 : a₀ ≠ p :=
                Nat.ne_of_lt (Nat.lt_of_lt_of_le hltB' hPp')
              have hnode4 : nodeAt m4 a₀ t₀ v₀ nL :=
                nodeAt_store_other_fwd hnode3 hS4 hside4
              have hC' : listCopyChase F m4
                  (addrOfWord (linkWord nL)) nh (some nd) =
                  .ok (m', nh', tail') := by
                unfold listCopyChase at hC
                simp only [hfb, hL0, hL1, hA, hS1, hS2, hfindP,
                  hS4] at hC
                exact hC
              obtain ⟨nds', hIH⟩ :=
                ih m4 π hinv'.hex head (addrOfWord (linkWord nL))
                  nh (some nd) (nd :: nds) (pref ++ [v₀])
                  vs₀ hinv' m' nh' tail' hC'
              refine ⟨nds', ?_⟩
              have hcurE : memEvalExpr (.var "cur")
                  (mkListCopyEnv head nh (some p) (some a₀) nds)
                  m π = .ok (.ptrVal (some a₀)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_cur _ _ _ _ _)
              have hnullE : memEvalExpr (.lit .nullptr)
                  (mkListCopyEnv head nh (some p) (some a₀) nds)
                  m π = .ok (.ptrVal none) := by
                simp [memEvalExpr, litVal]
              have hgT : memEvalExpr
                  (.une (.var "cur") (.lit .nullptr))
                  (mkListCopyEnv head nh (some p) (some a₀) nds)
                  m π = .ok (.b true) := by
                have hg := memEvalExpr_une_ptrVal _ _ _ _ _
                  (some a₀) none hcurE hnullE
                have hbe : ((some a₀) != none) = true := by simp
                rw [hbe] at hg
                exact hg
              have hE1 : (("nd", .ptrVal (some nd)) ::
                  mkListCopyEnv head nh (some p) (some a₀)
                    nds) =
                  mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds) := rfl
              have hlet : memEvalStmtFuel F
                  (.let_ "nd" nodeTy .nnew)
                  (mkListCopyEnv head nh (some p) (some a₀) nds)
                  m π =
                  .ok (((mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds), m1, π)), .fellThrough) := by
                have h := memEvalStmtFuel_let_nnew F "nd" nodeTy
                  (mkListCopyEnv head nh (some p) (some a₀) nds)
                  m π
                simp only [hA] at h
                rw [hE1] at h
                exact h
              have hdN : memEvalExpr (.var "nd")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (.ptrVal (some nd)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hcurE1 : memEvalExpr (.var "cur")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (.ptrVal (some a₀)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_cur _ _ _ _ _)
              have hfb1 : memFind m1 a₀ =
                  some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode1
              have hcellA1 : cellsAt m1 a₀ t₀
                  [v₀, linkWord nL] := hnode1
              have hLd0 : memLoad m1 a₀ t₀ 0 = .ok v₀ :=
                memLoad_cellsAt m1 a₀ t₀ 0 [v₀, linkWord nL] v₀
                  hcellA1 (by simp)
              have hvP : memEvalExpr
                  (.pgetVal (.var "cur"))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m1 π = .ok (.i32 v₀) :=
                memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE1
                  hfb1 hLd0
              have hpsetV : memEvalStmtFuel F
                  (.psetVal (.var "nd") (.pgetVal (.var "cur")))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (((mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds), m2, π)), .fellThrough) :=
                memEvalStmtFuel_psetVal_ok F (.var "nd")
                  (.pgetVal (.var "cur"))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m1 π nd v₀
                  ⟨nd, true, List.replicate 2 0⟩ m2 hdN hvP
                  hfindN hS1
              have hdN2 : memEvalExpr (.var "nd")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (.ptrVal (some nd)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hnullE2 : memEvalExpr (.lit .nullptr)
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (.ptrVal none) := by
                simp [memEvalExpr, litVal]
              have hpsetN : memEvalStmtFuel F
                  (.psetNext (.var "nd") (.lit .nullptr))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (((mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds), m3, π)), .fellThrough) :=
                memEvalStmtFuel_psetNext_ok F (.var "nd")
                  (.lit .nullptr)
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m2 π nd none
                  ⟨nd, true, [v₀, 0]⟩ m3 hdN2 hnullE2 hfind2 hS2
              have htailE : memEvalExpr (.var "tail")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (.ptrVal (some p)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_tail _ _ _ _ _)
              have hnullE3 : memEvalExpr (.lit .nullptr)
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (.ptrVal none) := by
                simp [memEvalExpr, litVal]
              have hueqF : memEvalExpr
                  (.ueq (.var "tail") (.lit .nullptr))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π = .ok (.b false) := by
                have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _
                  (some p) none htailE hnullE3
                have hbe : (((some p) == none) = false) := by simp
                rw [hbe] at hg
                exact hg
              have hdN3 : memEvalExpr (.var "tail")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (.ptrVal (some p)) := htailE
              have hnd3 : memEvalExpr (.var "nd")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (.ptrVal (some nd)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hswing : memEvalStmtFuel F
                  (.psetNext (.var "tail") (.var "nd"))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds), m4, π)), .fellThrough) :=
                memEvalStmtFuel_psetNext_ok F (.var "tail")
                  (.var "nd")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π p (some nd)
                  ⟨tp, true, [wp, linkWord none]⟩ m4 hdN3 hnd3
                  hfindP hS4
              have hifF : memEvalStmtFuel F
                  (.if_ (.ueq (.var "tail") (.lit .nullptr))
                    (.assign "new_head" (.var "nd"))
                    (.psetNext (.var "tail") (.var "nd")))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds), m4, π)), .fellThrough) :=
                (memEvalStmtFuel_if_false F _ _ _ _ _ _ hueqF).trans
                  hswing
              have hubaseT : envUpdate
                  (mkListCopyBase head nh (some p) (some a₀))
                  "tail" (.ptrVal (some nd)) =
                  some [("cur", .ptrVal (some a₀)),
                    ("tail", .ptrVal (some nd)),
                    ("new_head", .ptrVal nh),
                    ("head", .ptrVal head)] := by
                simp [mkListCopyBase, envUpdate]
              have hmissT : ∀ k w, (k, w) ∈ ndShadows (nd :: nds) →
                  k ≠ "tail" := by
                intro k w hmem hcon
                have hk := ndShadows_keys (nd :: nds) k w hmem
                rw [hk] at hcon
                exact absurd hcon (by decide)
              have huT : envUpdate
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) "tail" (.ptrVal (some nd)) =
                  some (mkListCopyEnv head nh (some nd)
                    (some a₀) (nd :: nds)) := by
                simp only [mkListCopyEnv]
                exact envUpdate_append_miss _ _ _ _ _
                  hmissT hubaseT
              have hdN4eq : memEvalExpr (.var "nd")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m4 π =
                  evalExpr (.var "nd")
                    (mkListCopyEnv head nh (some p) (some a₀)
                      (nd :: nds)) :=
                memEvalExpr_var _ _ _ _
              have hvnd2 : evalExpr (.var "nd")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) =
                  .ok (.ptrVal (some nd)) :=
                evalExpr_var_hit _ _ _
                  (mkListCopyEnv_nd_latest _ _ _ _ _ _)
              have hassignT : memEvalStmtFuel F
                  (.assign "tail" (.var "nd"))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m4 π =
                  .ok (((mkListCopyEnv head nh (some nd)
                    (some a₀) (nd :: nds), m4, π)),
                    .fellThrough) :=
                memEvalStmtFuel_assign F "tail" (.var "nd")
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m4 π (.ptrVal (some nd))
                  (mkListCopyEnv head nh (some nd)
                    (some a₀) (nd :: nds)) hdN4eq hvnd2 huT
              have hcurE4 : memEvalExpr (.var "cur")
                  (mkListCopyEnv head nh (some nd) (some a₀)
                    (nd :: nds)) m4 π =
                  .ok (.ptrVal (some a₀)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListCopyEnv_cur _ _ _ _ _)
              have hfb4 : memFind m4 a₀ =
                  some ⟨t₀, true, [v₀, linkWord nL]⟩ := hnode4
              have hcellA4 : cellsAt m4 a₀ t₀
                  [v₀, linkWord nL] := hnode4
              have hLd1 : memLoad m4 a₀ t₀ 1 =
                  .ok (linkWord nL) :=
                memLoad_cellsAt m4 a₀ t₀ 1 [v₀, linkWord nL]
                  (linkWord nL) hcellA4 (by simp)
              have hpgn : memEvalExpr
                  (.pgetNext (.var "cur"))
                  (mkListCopyEnv head nh (some nd) (some a₀)
                    (nd :: nds)) m4 π =
                  .ok (.ptrVal (addrOfWord (linkWord nL))) :=
                memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE4
                  hfb4 hLd1
              have hubaseC : envUpdate
                  (mkListCopyBase head nh (some nd) (some a₀))
                  "cur" (.ptrVal (addrOfWord (linkWord nL))) =
                  some [("cur",
                    .ptrVal (addrOfWord (linkWord nL))),
                    ("tail", .ptrVal (some nd)),
                    ("new_head", .ptrVal nh),
                    ("head", .ptrVal head)] := by
                simp [mkListCopyBase, envUpdate]
              have hmissC : ∀ k w, (k, w) ∈ ndShadows (nd :: nds) →
                  k ≠ "cur" := by
                intro k w hmem hcon
                have hk := ndShadows_keys (nd :: nds) k w hmem
                rw [hk] at hcon
                exact absurd hcon (by decide)
              have huC : envUpdate
                  (mkListCopyEnv head nh (some nd) (some a₀)
                    (nd :: nds)) "cur"
                  (.ptrVal (addrOfWord (linkWord nL))) =
                  some (mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL))
                    (nd :: nds)) := by
                simp only [mkListCopyEnv]
                exact envUpdate_append_miss _ _ _ _ _
                  hmissC hubaseC
              have hassignC : memEvalStmtFuel F
                  (.assign "cur" (.pgetNext (.var "cur")))
                  (mkListCopyEnv head nh (some nd) (some a₀)
                    (nd :: nds)) m4 π =
                  .ok (((mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m4, π)), .fellThrough) :=
                memEvalStmtFuel_assign_mem F "cur"
                  (.pgetNext (.var "cur"))
                  (mkListCopyEnv head nh (some nd) (some a₀)
                    (nd :: nds)) m4 π
                  (.ptrVal (addrOfWord (linkWord nL)))
                  (mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds))
                  hpgn huC
              have h34 : memEvalStmtFuel F
                  (.seq (.assign "tail" (.var "nd"))
                    (.assign "cur" (.pgetNext (.var "cur"))))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m4 π =
                  .ok (((mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m4, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hassignT hassignC
              have h234 : memEvalStmtFuel F
                  (.seq (.if_ (.ueq (.var "tail")
                      (.lit .nullptr))
                      (.assign "new_head" (.var "nd"))
                      (.psetNext (.var "tail") (.var "nd")))
                    (.seq (.assign "tail" (.var "nd"))
                      (.assign "cur"
                        (.pgetNext (.var "cur")))))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m3 π =
                  .ok (((mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m4, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hifF h34
              have h1234 : memEvalStmtFuel F
                  (.seq (.psetNext (.var "nd")
                      (.lit .nullptr))
                    (.seq (.if_ (.ueq (.var "tail")
                        (.lit .nullptr))
                        (.assign "new_head" (.var "nd"))
                        (.psetNext (.var "tail") (.var "nd")))
                      (.seq (.assign "tail" (.var "nd"))
                        (.assign "cur"
                          (.pgetNext (.var "cur"))))))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m2 π =
                  .ok (((mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m4, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hpsetN h234
              have h01234 : memEvalStmtFuel F
                  (.seq (.psetVal (.var "nd")
                      (.pgetVal (.var "cur")))
                    (.seq (.psetNext (.var "nd")
                        (.lit .nullptr))
                      (.seq (.if_ (.ueq (.var "tail")
                          (.lit .nullptr))
                          (.assign "new_head" (.var "nd"))
                          (.psetNext (.var "tail")
                            (.var "nd")))
                        (.seq (.assign "tail" (.var "nd"))
                          (.assign "cur"
                            (.pgetNext (.var "cur")))))))
                  (mkListCopyEnv head nh (some p) (some a₀)
                    (nd :: nds)) m1 π =
                  .ok (((mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m4, π)), .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                  _ _ _ _ hpsetV h1234
              have hbody : memEvalStmtFuel F listCopyLoopBody
                  (mkListCopyEnv head nh (some p) (some a₀) nds)
                  m π =
                  .ok (((mkListCopyEnv head nh (some nd)
                    (addrOfWord (linkWord nL)) (nd :: nds),
                    m4, π)), .fellThrough) := by
                unfold listCopyLoopBody
                exact memEvalStmtFuel_seq_fallthrough_trans F _ _
                  _ _ _ _ _ _ _ hlet h01234
              unfold listCopyLoop
              rw [memEvalStmtFuel_while_true F _ _ _ _ _ hgT,
                hbody]
              exact hIH

/-- The entry triple: seeding the three lets and running the loop
    evaluates the copy body to the chase's new head, with the
    full contract. -/
theorem listCopyFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hmark : Mark m)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (vs₀ : List (BitVec 32))
    (m' : Mem) (nh' : Option Addr)
    (hseg : ListSeg m head vs₀)
    (hlen : vs₀.length ≤ F)
    (hroom0 : m.next + vs₀.length + 1 < 2 ^ 32)
    (hfwd : listCopyFwd F m head = .ok (m', nh')) :
    ∃ ρ', memEvalStmtFuel F listCopyFunc.body
      [("head", .ptrVal head)] m π =
      .ok ((ρ', m', π), .returned (.ptrVal nh')) ∧
      ListSeg m' nh' vs₀ ∧ ListSeg m' head vs₀ ∧
      (∀ a, SegMem (m := m') nh' a → m.next ≤ a) ∧
      (∀ a, SegMem (m := m') head a →
        SegMem (m := m') nh' a → False) := by
  have hcon := listCopyFwd_correct hmark hex hseg hlen hroom0 hfwd
  obtain ⟨hdest, hsrc, hfresh, hdisj⟩ := hcon
  have hinv := copyEntryInv hmark hex hseg hlen hroom0
  obtain ⟨mC', nhC', tail', pref', hC, hinv', hpref'⟩ :=
    listCopyChase_ok F m head head none none [] vs₀ hinv
  unfold listCopyFwd at hfwd
  rw [hC] at hfwd
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
  obtain ⟨e1, e2⟩ := hfwd
  subst e1
  subst e2
  obtain ⟨nds', hloop⟩ :=
    listCopyLoop_agree F m π hinv.hex head head none none []
      [] vs₀ hinv mC' nhC' tail' hC
  have eH : memEvalExpr (.lit .nullptr)
      [("head", .ptrVal head)] m π =
      evalExpr (.lit .nullptr) [("head", .ptrVal head)] :=
    memEvalExpr_lit _ _ _ _
  have vH : evalExpr (.lit .nullptr) [("head", .ptrVal head)] =
      .ok (.ptrVal none) := by
    simp [evalExpr, litVal]
  have hletH : memEvalStmtFuel F
      (.let_ "new_head" nodeTy (.lit .nullptr))
      [("head", .ptrVal head)] m π =
      .ok (((("new_head", .ptrVal none) ::
        [("head", .ptrVal head)], m, π)), .fellThrough) :=
    memEvalStmtFuel_let_pure F "new_head" nodeTy
      (.lit .nullptr) [("head", .ptrVal head)] m π
      (.ptrVal none) (by simp) (by simp) (by simp) (by simp)
      eH vH
  have eT : memEvalExpr (.lit .nullptr)
      (("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π =
      evalExpr (.lit .nullptr)
        (("new_head", .ptrVal none) ::
          [("head", .ptrVal head)]) :=
    memEvalExpr_lit _ _ _ _
  have vT : evalExpr (.lit .nullptr)
      (("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) =
      .ok (.ptrVal none) := by
    simp [evalExpr, litVal]
  have hletT : memEvalStmtFuel F
      (.let_ "tail" nodeTy (.lit .nullptr))
      (("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π =
      .ok (((("tail", .ptrVal none) :: ("new_head", .ptrVal none) ::
        [("head", .ptrVal head)], m, π)), .fellThrough) :=
    memEvalStmtFuel_let_pure F "tail" nodeTy
      (.lit .nullptr)
      (("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π
      (.ptrVal none) (by simp) (by simp) (by simp) (by simp)
      eT vT
  have eC : memEvalExpr (.var "head")
      (("tail", .ptrVal none) :: ("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π =
      evalExpr (.var "head")
        (("tail", .ptrVal none) :: ("new_head", .ptrVal none) ::
          [("head", .ptrVal head)]) :=
    memEvalExpr_var _ _ _ _
  have vC : evalExpr (.var "head")
      (("tail", .ptrVal none) :: ("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) =
      .ok (.ptrVal head) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hletC : memEvalStmtFuel F
      (.let_ "cur" nodeTy (.var "head"))
      (("tail", .ptrVal none) :: ("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π =
      .ok (((("cur", .ptrVal head) :: ("tail", .ptrVal none) ::
        ("new_head", .ptrVal none) ::
        [("head", .ptrVal head)], m, π)), .fellThrough) :=
    memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
      (("tail", .ptrVal none) :: ("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π
      (.ptrVal head) (by simp) (by simp) (by simp) (by simp)
      eC vC
  have hretE : memEvalExpr (.var "new_head")
      (mkListCopyEnv head nhC' tail' none nds') mC' π =
      evalExpr (.var "new_head")
        (mkListCopyEnv head nhC' tail' none nds') :=
    memEvalExpr_var _ _ _ _
  have hretV : evalExpr (.var "new_head")
      (mkListCopyEnv head nhC' tail' none nds') =
      .ok (.ptrVal nhC') :=
    evalExpr_var_hit _ _ _
      (mkListCopyEnv_new_head _ _ _ _ _)
  have hret : memEvalStmtFuel F
      (.return_ (.var "new_head"))
      (mkListCopyEnv head nhC' tail' none nds') mC' π =
      .ok (((mkListCopyEnv head nhC' tail' none nds', mC', π)),
        .returned (.ptrVal nhC')) :=
    memEvalStmtFuel_return F (.var "new_head")
      (mkListCopyEnv head nhC' tail' none nds') mC' π _
      hretE hretV
  have hR3 : memEvalStmtFuel F
      (.seq listCopyLoop (.return_ (.var "new_head")))
      (mkListCopyEnv head none none head []) m π =
      .ok (((mkListCopyEnv head nhC' tail' none nds', mC', π)),
        .returned (.ptrVal nhC')) := by
    have hρ : mkListCopyEnv head none none head [] =
        (("cur", .ptrVal head) :: ("tail", .ptrVal none) ::
          ("new_head", .ptrVal none) ::
          [("head", .ptrVal head)]) := rfl
    rw [hρ]
    exact memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hloop hret
  have hR2 : memEvalStmtFuel F
      (.seq (.let_ "cur" nodeTy (.var "head"))
        (.seq listCopyLoop (.return_ (.var "new_head"))))
      (("tail", .ptrVal none) :: ("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π =
      .ok (((mkListCopyEnv head nhC' tail' none nds', mC', π)),
        .returned (.ptrVal nhC')) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hletC hR3
  have hR1 : memEvalStmtFuel F
      (.seq (.let_ "tail" nodeTy (.lit .nullptr))
        (.seq (.let_ "cur" nodeTy (.var "head"))
          (.seq listCopyLoop (.return_ (.var "new_head")))))
      (("new_head", .ptrVal none) ::
        [("head", .ptrVal head)]) m π =
      .ok (((mkListCopyEnv head nhC' tail' none nds', mC', π)),
        .returned (.ptrVal nhC')) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hletT hR2
  have hB : memEvalStmtFuel F
      (.seq (.let_ "new_head" nodeTy (.lit .nullptr))
        (.seq (.let_ "tail" nodeTy (.lit .nullptr))
          (.seq (.let_ "cur" nodeTy (.var "head"))
            (.seq listCopyLoop
              (.return_ (.var "new_head"))))))
      [("head", .ptrVal head)] m π =
      .ok (((mkListCopyEnv head nhC' tail' none nds', mC', π)),
        .returned (.ptrVal nhC')) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hletH hR1
  have hfunc : listCopyFunc.body = listCopyBody := rfl
  rw [hfunc]
  unfold listCopyBody
  refine ⟨_, hB, hdest, hsrc, hfresh, hdisj⟩
