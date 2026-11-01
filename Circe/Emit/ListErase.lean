/-
Circe.Emit.ListErase — pillar-1 goal #2: node unlink with `free`
(`list_erase`) over caller-owned `Node {val, next}`.

The corpus (`tests/cpp/list_erase.cpp`, entry
`Node *list_erase(Node *head, int val)`) chases with a trailing
pointer, unlinks the first node whose payload matches (head case:
`head = cur->next`; interior case: `prev->next = cur->next`),
frees exactly that cell, and returns the (possibly new) head. A
miss (or empty input) returns the head untouched with no `free` —
silent legs, covered by the loop guard, not a branch. Faults are
loud, not branched: freeing a null, missing, or already-freed
cell aborts in the model (`memFree` miss/tag/liveness checks),
exactly the L-ptr miss discipline.

The mirror chases with `listEraseChase` (fuel-indexed, read-only:
each step reads the payload at `[0]` with the new `.pgetVal`
and the link at `[1]`), then unlinks and frees. The contract is
a removal: `ListSeg m' hd' (vs.erase v)` with the victim cell
dead (live flag cleared — contents kept but unusable, so any
later dereference misses loudly). Freshness-style hypotheses
are unnecessary (nothing allocates); the fuel bound rules out
exhaustion and exactness decodes the links, as in the append
chase. The hard proof is segment surgery around a dead cell:
the surviving members avoid the victim by acyclicity
(`ListSeg_acyclic_aux` both directions), and the unlink store
plus the free ride the prefix and suffix node by node.
-/
import Circe.Emit.LinkedReverse

/-! ## P3: `list_erase` entry -/

/-- Mangled name of the erase entry. -/
def listEraseName : String :=
  "_Z10list_eraseP4Nodei"

/-- The chase-loop body (guard, hit-or-step): named so the
    agreement proof can rewrite it without literals. -/
def listEraseLoopBody : CStmt :=
  (.seq (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
            (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                    (.assign "head" (.pgetNext (.var "cur")))
                    (.psetNext (.var "prev")
                      (.pgetNext (.var "cur"))))
              (.seq (.nfree (.var "cur"))
                (.return_ (.var "head"))))
            .skip)
    (.seq (.assign "prev" (.var "cur"))
      (.assign "cur" (.pgetNext (.var "cur")))))

/-- The chase loop (isolated for the loop/evaluator
    agreement: guard, hit-or-step body). -/
def listEraseLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) listEraseLoopBody)

/-- Canonical CoreIR for `list_erase`: seed the cursors, chase
    while `cur != nullptr`, unlink + free + return on the first
    payload hit, step both cursors otherwise, return the head on
    exhaustion. -/
def listEraseBody : CStmt :=
  (.seq (.let_ "prev" nodeTy (.lit .nullptr))
    (.seq (.let_ "cur" nodeTy (.var "head"))
      (.seq listEraseLoop
        (.return_ (.var "head")))))

/-- The erase entry: `Node*` + `i32` in, `Node*` out. -/
def listEraseFunc : Func :=
  ⟨listEraseName,
   [{ name := "head", ty := nodeTy, role := .owned },
    { name := "val", ty := (.i 32), role := .owned }],
   nodeTy,
   listEraseBody⟩

/-- Erase environment: head and payload slots, then the two
    cursor slots (the entry binds `head` and `val` first, then
    the lets cons `prev` and `cur` on the front). -/
def mkListEraseEnv (head : Option Addr) (v : BitVec 32)
    (prev cur : Option Addr) : Env :=
  [("cur", .ptrVal cur), ("prev", .ptrVal prev),
    ("head", .ptrVal head), ("val", .i32 v)]

theorem mkListEraseEnv_cur (head : Option Addr) (v : BitVec 32)
    (prev cur : Option Addr) :
    envLookup (mkListEraseEnv head v prev cur) "cur" =
      some (.ptrVal cur) := by
  simp [mkListEraseEnv, envLookup]

theorem mkListEraseEnv_prev (head : Option Addr) (v : BitVec 32)
    (prev cur : Option Addr) :
    envLookup (mkListEraseEnv head v prev cur) "prev" =
      some (.ptrVal prev) := by
  simp [mkListEraseEnv, envLookup]

theorem mkListEraseEnv_head (head : Option Addr) (v : BitVec 32)
    (prev cur : Option Addr) :
    envLookup (mkListEraseEnv head v prev cur) "head" =
      some (.ptrVal head) := by
  simp [mkListEraseEnv, envLookup]

theorem mkListEraseEnv_val (head : Option Addr) (v : BitVec 32)
    (prev cur : Option Addr) :
    envLookup (mkListEraseEnv head v prev cur) "val" =
      some (.i32 v) := by
  simp [mkListEraseEnv, envLookup]

/-! ## Forward mirror (read-only chase, then unlink + free) -/

/-- Chase for the first payload hit: read-only (each step reads
    the payload at `[0]` and the link at `[1]`), returning the
    memory unchanged with the predecessor and the match (`none`
    on exhaustion). Misses, dangling links, and short blocks
    abort loudly at any fuel; each visit consumes fuel (like the
    evaluator's loop iteration — a hit needs fuel too). -/
def listEraseChase (F : Nat) (m : Mem) (prev cur : Option Addr)
    (v : BitVec 32) : Result (Mem × Option Addr × Option Addr) :=
  match cur with
  | none => .ok (m, prev, none)
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
          if w == v then .ok (m, prev, cur)
          else match memLoad m a b.tag 1 with
               | .error e => .error e
               | .ok w' =>
                 listEraseChase F m (some a) (addrOfWord w') v

/-- Entry mirror: chase, then unlink the match (`head` case
    updates the return only; interior case stores the victim's
    link through `prev`), free the victim, and return. A miss
    returns the head with the memory untouched. -/
def listEraseFwd (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) : Result (Mem × Option Addr) :=
  match listEraseChase F m none head v with
  | .error e => .error e
  | .ok (m1, prev, cur) =>
    match cur with
    | none => .ok (m1, head)
    | some c =>
      match memFind m1 c with
      | none => .error .AssertFail
      | some bc =>
        match memLoad m1 c bc.tag 1 with
        | .error e => .error e
        | .ok w =>
          match prev with
          | none =>
            match memFree m1 c bc.tag with
            | .error e => .error e
            | .ok m2 => .ok (m2, addrOfWord w)
          | some p =>
            match memFind m1 p with
            | none => .error .AssertFail
            | some bp =>
              match memStore m1 p bp.tag 1 w with
              | .error e => .error e
              | .ok m2 =>
                match memFree m2 c bc.tag with
                | .error e => .error e
                | .ok m3 => .ok (m3, head)

/-! ## Erase at the value level -/

/-- Erasing an absent payload removes nothing. -/
theorem List.erase_self_of_not_mem (l : List (BitVec 32)) (v : BitVec 32)
    (h : v ∉ l) : l.erase v = l := by
  induction l with
  | nil => exact List.erase_nil v
  | cons w ws ih =>
    have hne : w ≠ v := by
      intro heq
      apply h
      rw [heq]
      exact .head _
    have hnin : v ∉ ws := fun hmem => h (List.mem_cons_of_mem w hmem)
    have hbe : (w == v) = false := by
      cases heq : (w == v) with
      | true => exact absurd (beq_iff_eq.mp heq) hne
      | false => rfl
    simp [List.erase_cons, hbe, ih hnin]

/-- Erasing the first hit past a clean prefix drops exactly
    that hit. -/
theorem List.erase_append_hit (l₁ : List (BitVec 32)) (v : BitVec 32)
    (l₂ : List (BitVec 32)) (h : ∀ w ∈ l₁, w ≠ v) :
    (l₁ ++ v :: l₂).erase v = l₁ ++ l₂ := by
  induction l₁ with
  | nil => simp [List.erase_cons]
  | cons w ws ih =>
    have hne : w ≠ v := h w (.head _)
    have hrest : ∀ x ∈ ws, x ≠ v := fun x hx => h x (.tail _ hx)
    have hbe : (w == v) = false := by
      cases heq : (w == v) with
      | true => exact absurd (beq_iff_eq.mp heq) hne
      | false => rfl
    simp [List.erase_cons, List.cons_append, hbe, ih hrest]

/-! ## Chase invariant -/

/-- Miss leg: the chase ran off the end (`cur = none`), so the
    visited payloads are the whole list and the victim is
    absent. Fuel plays no role. -/
theorem listEraseChase_miss_nil (m : Mem)
    (top : Option Addr) (nodes : List (Addr × Nat × BitVec 32))
    (prev : Option Addr) (v : BitVec 32)
    (suf : List (BitVec 32))
    (hchain : PrefixChain m top nodes none)
    (hseg : ListSeg m none suf)
    (hclean : ∀ w ∈ preVals nodes, w ≠ v)
    (F : Nat) (m' : Mem) (prev' cur' : Option Addr)
    (hchase : listEraseChase F m prev none v = .ok (m', prev', cur')) :
    m' = m ∧
    ((cur' = none ∧ (preVals nodes ++ suf).erase v = preVals nodes ++ suf) ∨
     (∃ nodes₁ c t n rest, cur' = some c ∧
        PrefixChain m top nodes₁ (some c) ∧ nodeAt m c t v n ∧
        ListSeg m n rest ∧ (∀ w ∈ preVals nodes₁, w ≠ v) ∧
        (preVals nodes ++ suf).erase v = preVals nodes₁ ++ rest ∧
        (prev' = none → nodes₁ = []) ∧
        (∀ p, prev' = some p → ∃ init lt lw, nodes₁ = init ++ [(p, lt, lw)]) ∧
        (prev' = none ∨ ∃ p tp wp, prev' = some p ∧ nodeAt m p tp wp (some c)))) := by
  simp only [listEraseChase] at hchase
  cases hchase
  cases hseg with
  | nil =>
    refine ⟨rfl, .inl ⟨rfl, ?_⟩⟩
    rw [List.append_nil]
    apply List.erase_self_of_not_mem
    intro hmem
    exact hclean v hmem rfl

/-- Hit leg: the chase stopped at a payload match, so the
    visited prefix is clean, the victim cell is pinned, and the
    tail starts at the victim's link. Fuel plays no role. -/
theorem listEraseChase_hit_found (m : Mem)
    (top : Option Addr) (nodes : List (Addr × Nat × BitVec 32))
    (prev : Option Addr) (a : Addr) (v : BitVec 32)
    (hchain : PrefixChain m top nodes (some a))
    (v₀ : BitVec 32) (nxt : Option Addr) (vs' : List (BitVec 32))
    {t' : Nat} (hnode : nodeAt m a t' v₀ nxt)
    (t2 : ListSeg m nxt vs')
    (hvv : v₀ = v)
    (hclean : ∀ w ∈ preVals nodes, w ≠ v)
    (hplink : ∀ p, prev = some p → ∃ tp wp, nodeAt m p tp wp (some a))
    (hprevnil : prev = none → nodes = [])
    (hprevnodes : ∀ p, prev = some p →
      ∃ init lt lw, nodes = init ++ [(p, lt, lw)])
    (m' : Mem) (prev' cur' : Option Addr)
    (hchase : (.ok (m, prev, some a) : Result (Mem × Option Addr × Option Addr)) =
      .ok (m', prev', cur')) :
    m' = m ∧
    ((cur' = none ∧ (preVals nodes ++ v₀ :: vs').erase v = preVals nodes ++ v₀ :: vs') ∨
     (∃ nodes₁ c t n rest, cur' = some c ∧
        PrefixChain m top nodes₁ (some c) ∧ nodeAt m c t v n ∧
        ListSeg m n rest ∧ (∀ w ∈ preVals nodes₁, w ≠ v) ∧
        (preVals nodes ++ v₀ :: vs').erase v = preVals nodes₁ ++ rest ∧
        (prev' = none → nodes₁ = []) ∧
        (∀ p, prev' = some p → ∃ init lt lw, nodes₁ = init ++ [(p, lt, lw)]) ∧
        (prev' = none ∨ ∃ p tp wp, prev' = some p ∧ nodeAt m p tp wp (some c)))) := by
  cases hchase
  subst hvv
  refine ⟨rfl, .inr ⟨nodes, a, t', nxt, vs', rfl, hchain, hnode, t2,
    hclean, List.erase_append_hit _ _ _ hclean, hprevnil, hprevnodes, ?_⟩⟩
  cases prev with
  | none => exact .inl rfl
  | some p =>
    obtain ⟨tp, wp, hnp⟩ := hplink p rfl
    exact .inr ⟨p, tp, wp, rfl, hnp⟩

/-- Erase chase invariant: the read-only chase returns the
    memory unchanged, and either misses (victim absent, visited
    prefix clean) or pins the first hit with its predecessor,
    suffix, and clean visited prefix. Induction is on fuel; the
    miss and hit legs are the fuel-free facts above. -/
theorem listEraseChase_invariant (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (top : Option Addr) (nodes : List (Addr × Nat × BitVec 32))
      (prev cur : Option Addr)
      (hchain : PrefixChain m top nodes cur) (v : BitVec 32)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hclean : ∀ w ∈ preVals nodes, w ≠ v)
      (hplink : ∀ p, prev = some p → ∃ tp wp, nodeAt m p tp wp cur)
      (hprevnil : prev = none → nodes = [])
      (hprevnodes : ∀ p, prev = some p →
        ∃ init lt lw, nodes = init ++ [(p, lt, lw)])
      (hlen : suf.length ≤ F)
      (m' : Mem) (prev' cur' : Option Addr),
    listEraseChase F m prev cur v = .ok (m', prev', cur') →
    m' = m ∧
    ((cur' = none ∧ (preVals nodes ++ suf).erase v = preVals nodes ++ suf) ∨
     (∃ nodes₁ c t n rest, cur' = some c ∧
        PrefixChain m top nodes₁ (some c) ∧ nodeAt m c t v n ∧
        ListSeg m n rest ∧ (∀ w ∈ preVals nodes₁, w ≠ v) ∧
        (preVals nodes ++ suf).erase v = preVals nodes₁ ++ rest ∧
        (prev' = none → nodes₁ = []) ∧
        (∀ p, prev' = some p → ∃ init lt lw, nodes₁ = init ++ [(p, lt, lw)]) ∧
        (prev' = none ∨ ∃ p tp wp, prev' = some p ∧ nodeAt m p tp wp (some c)))) := by
  induction F with
  | zero =>
    intro m hex top nodes prev cur hchain v suf hseg hclean hplink hprevnil
      hprevnodes hlen m' prev' cur' hchase
    cases cur with
    | none =>
      exact listEraseChase_miss_nil m top nodes prev v suf hchain hseg
        hclean _ m' prev' cur' hchase
    | some a =>
      unfold listEraseChase at hchase
      simp only at hchase
      cases hchase
  | succ F ih =>
    intro m hex top nodes prev cur hchain v suf hseg hclean hplink hprevnil
      hprevnodes hlen m' prev' cur' hchase
    cases cur with
    | none =>
      exact listEraseChase_miss_nil m top nodes prev v suf hchain hseg
        hclean _ m' prev' cur' hchase
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a t' 0 = .ok _ := nodeLoadVal hnode
        have hmem1 : memLoad m a t' 1 = .ok _ := nodeLoadNext hnode
        unfold listEraseChase at hchase
        simp only [hfb, hmem0, hmem1] at hchase
        by_cases heq2 : (v₀ == v) = true
        · rw [if_pos heq2] at hchase
          exact listEraseChase_hit_found m top nodes prev a v hchain v₀
            nxt vs' hnode t2 (beq_iff_eq.mp heq2) hclean hplink
            hprevnil hprevnodes m' prev' cur' hchase
        · rw [if_neg heq2] at hchase
          have halloc : ∀ c', nxt = some c' → (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : nxt with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact ListSeg_head_alloc t2
          have hdec : addrOfWord (linkWord nxt) = nxt :=
            nodeAt_link_roundtrip hnode hex halloc
          rw [hdec] at hchase
          have hnev : v₀ ≠ v := fun heq => heq2 (by rw [heq]; simp)
          have hchain' : PrefixChain m top (nodes ++ [(a, t', v₀)]) nxt :=
            PrefixChain.snoc_extend hchain hnode rfl rfl
          have hvals : preVals (nodes ++ [(a, t', v₀)]) =
              preVals nodes ++ [v₀] := by
            simp [preVals]
          have hclean' : ∀ w ∈ preVals (nodes ++ [(a, t', v₀)]), w ≠ v := by
            intro w hw
            rw [hvals, List.mem_append] at hw
            cases hw with
            | inl hmem => exact hclean w hmem
            | inr hmem =>
              simp only [List.mem_singleton] at hmem
              subst hmem
              exact hnev
          have hplink' : ∀ p, (some a) = some p →
              ∃ tp wp, nodeAt m p tp wp nxt := by
            intro p hp
            cases hp
            exact ⟨t', v₀, hnode⟩
          have hprevnil' : (some a) = none →
              nodes ++ [(a, t', v₀)] = [] := by
            intro h
            cases h
          have hprevnodes' : ∀ p, (some a) = some p →
              ∃ init lt lw,
                (nodes ++ [(a, t', v₀)]) = init ++ [(p, lt, lw)] := by
            intro p hp
            cases hp
            exact ⟨nodes, t', v₀, rfl⟩
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          have heqAppend : preVals nodes ++ v₀ :: vs' =
              preVals (nodes ++ [(a, t', v₀)]) ++ vs' := by
            simp [preVals, List.map_append]
          have hIH := ih m hex top (nodes ++ [(a, t', v₀)]) (some a) nxt
            hchain' v vs' t2 hclean' hplink' hprevnil' hprevnodes'
            hlen' m' prev' cur' hchase
          obtain ⟨hm'm, hdisj⟩ := hIH
          refine ⟨hm'm, ?_⟩
          cases hdisj with
          | inl hmiss =>
            obtain ⟨hcnone, herase⟩ := hmiss
            exact .inl ⟨hcnone, by rw [heqAppend]; exact herase⟩
          | inr hhit =>
            obtain ⟨nodes₁, c, t, n, rest, hcur', hch, hvic, hsuf,
              hcl1, herase, hpnil, hpnodes, hprev⟩ := hhit
            exact .inr ⟨nodes₁, c, t, n, rest, hcur', hch, hvic, hsuf,
              hcl1, by rw [heqAppend]; exact herase, hpnil, hpnodes,
              hprev⟩

/-! ## Forward contract: unlink + free -/

/-- Erasing a present payload strictly shrinks the value list,
    so a miss (erase is the identity) means absence. -/
theorem List.not_mem_of_erase_self (vs : List (BitVec 32)) (v : BitVec 32)
    (h : vs.erase v = vs) : v ∉ vs := by
  intro hmem
  have hlen : (vs.erase v).length = vs.length - 1 :=
    List.length_erase_of_mem hmem
  have hpos : 0 < vs.length := by
    cases vs with
    | nil => cases hmem
    | cons _ _ => simp
  rw [h] at hlen
  omega

/-- Erase forward contract: the result holds the list with the
    first payload hit removed, and a hit leaves its cell dead
    (present with the live flag cleared, so any later
    dereference misses loudly). The miss leg returns the head
    with the memory untouched. -/
theorem listEraseFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hlen : vs.length ≤ F)
    (hfwd : listEraseFwd F m head v = .ok (m', hd')) :
    ListSeg m' hd' (vs.erase v) ∧
    (v ∈ vs → ∃ c t n, memFind m' c =
      some ⟨t, false, [v, linkWord n]⟩) := by
  unfold listEraseFwd at hfwd
  cases hC : listEraseChase F m none head v with
  | error e =>
    simp only [hC] at hfwd
    cases hfwd
  | ok res =>
    obtain ⟨m1, prev', cur'⟩ := res
    simp only [hC] at hfwd
    have hI := listEraseChase_invariant F m hex head [] none head
      PrefixChain.nil v vs hseg (by simp [preVals])
      (by intro p hp; cases hp) (fun _ => rfl)
      (by intro p hp; cases hp) hlen m1 prev' cur' hC
    obtain ⟨hm'm, hdisj⟩ := hI
    subst m1
    cases hdisj with
    | inl hmiss =>
      obtain ⟨hcnone, herase⟩ := hmiss
      simp only [hcnone] at hfwd
      cases hfwd
      have herase' : vs.erase v = vs := herase
      refine ⟨by rw [herase']; exact hseg, ?_⟩
      intro hmem
      exact absurd hmem (List.not_mem_of_erase_self vs v herase')
    | inr hhit =>
      obtain ⟨nodes₁, c, t, n, rest, hcur'eq, hch, hvic, hsuf,
        hcl1, herase, hpnil, hpnodes, hprev⟩ := hhit
      simp only [hcur'eq] at hfwd
      have herase' : vs.erase v = preVals nodes₁ ++ rest := herase
      cases hF1 : memFind m c with
      | none =>
        simp only [hF1] at hfwd
        cases hfwd
      | some bc =>
        simp only [hF1] at hfwd
        cases hL1 : memLoad m c bc.tag 1 with
        | error e =>
          simp only [hL1] at hfwd
          cases hfwd
        | ok w =>
          simp only [hL1] at hfwd
          have hfindC : memFind m c = some _ := hvic
          rw [hfindC] at hF1
          have hbc : bc = ⟨t, true, [v, linkWord n]⟩ := by
            cases hF1.symm
            rfl
          rw [hbc] at hL1
          have hw : w = linkWord n := by
            have h2 := nodeLoadNext hvic
            have h3 := hL1.symm.trans h2
            cases h3
            rfl
          have hallocN : ∀ c'', n = some c'' →
              (memFind m c'').isSome = true := by
            intro c'' hc''
            cases hc''
            exact ListSeg_head_alloc hsuf
          have hdecN : addrOfWord (linkWord n) = n :=
            nodeAt_link_roundtrip hvic hex hallocN
          cases hprev with
          | inl hprevNone =>
            simp only [hprevNone] at hfwd
            cases hFR : memFree m c bc.tag with
            | error e =>
              simp only [hFR] at hfwd
              cases hfwd
            | ok m2 =>
              simp only [hFR] at hfwd
              cases hfwd
              have herase0 : vs.erase v = rest := by
                have h := herase'
                rw [hpnil hprevNone] at h
                exact h
              have hhd : addrOfWord w = n := by
                rw [hw]; exact hdecN
              have hsuf3 : ListSeg m' n rest :=
                hsuf.free_other hFR (by
                  intro b hmemB
                  exact ListSeg_head_notin_tail hvic hsuf hex b hmemB)
              rw [hbc] at hFR
              have hdead : memFind m' c =
                  some ⟨t, false, [v, linkWord n]⟩ :=
                memFind_memFree_dead hvic hFR
              rw [herase0, hhd]
              exact ⟨hsuf3, fun _ => ⟨c, t, n, hdead⟩⟩
          | inr hprevSome =>
            obtain ⟨p, tp, wp, hpeq, hnp⟩ := hprevSome
            simp only [hpeq] at hfwd
            cases hFp : memFind m p with
            | none =>
              simp only [hFp] at hfwd
              cases hfwd
            | some bp2 =>
              simp only [hFp] at hfwd
              cases hFS : memStore m p bp2.tag 1 w with
              | error e =>
                simp only [hFS] at hfwd
                cases hfwd
              | ok m2' =>
                simp only [hFS] at hfwd
                cases hFR2 : memFree m2' c bc.tag with
                | error e =>
                  simp only [hFR2] at hfwd
                  cases hfwd
                | ok m3 =>
                  simp only [hFR2] at hfwd
                  cases hfwd
                  have hfindP : memFind m p = some _ := hnp
                  rw [hfindP] at hFp
                  cases hFp
                  obtain ⟨initP, lt, lw, hsplitEq⟩ :=
                    hpnodes p hpeq
                  rw [hsplitEq] at hch
                  obtain ⟨midp, hinit, hplast⟩ :=
                    PrefixChain.split hch
                  cases hplast with
                  | cons hnodeP' hrestP =>
                    cases hrestP
                    have hfindP2 : memFind m p = some _ := hnodeP'
                    rw [hfindP2] at hfindP
                    cases hfindP
                    rw [hw] at hFS
                    have hpNew : nodeAt m2' p tp wp n :=
                      nodeStoreNext_nodeAt hnp hFS
                    have hnePC : p ≠ c := by
                      intro hcon
                      have hnpC : nodeAt m c tp wp (some c) :=
                        hcon ▸ hnp
                      have hmem : SegMem (m := m) (some c) c :=
                        SegMem.here hvic
                      have hsegP : ListSeg m (some c) (v :: rest) :=
                        ListSeg.cons hvic hsuf
                      have hcontra :=
                        ListSeg_head_notin_tail hnpC hsegP hex c hmem
                      exact hcontra rfl
                    have hneCP : c ≠ p := Ne.symm hnePC
                    have hvic2 : nodeAt m2' c t v n :=
                      nodeAt_store_other_fwd hvic hFS hneCP
                    have hfindP' : memFind m p = some _ := hnp
                    have hliveP : (memFind m p).isSome = true := by
                      have h := congrArg Option.isSome hfindP'
                      simpa using h
                    have hex2 : ∀ x, (memFind m2' x).isSome = true →
                        x + 1 < 2 ^ 32 :=
                      hex_store hex hFS hliveP
                    have hout_p : ∀ b, SegMem (m := m) n b → b ≠ p := by
                      intro b hmemB
                      have hmemC : SegMem (m := m) (some c) b :=
                        hmemB.victimCons hvic
                      have htailP : ListSeg m (some c) (v :: rest) :=
                        ListSeg.cons hvic hsuf
                      exact ListSeg_head_notin_tail hnp htailP hex b hmemC
                    have hsuf2 : ListSeg m2' n rest :=
                      hsuf.store_other hFS hout_p
                    have hout_c : ∀ b, SegMem (m := m2') n b → b ≠ c := by
                      intro b hmemB
                      exact ListSeg_head_notin_tail hvic2 hsuf2 hex2 b hmemB
                    have hsuf3 : ListSeg m' n rest :=
                      hsuf2.free_other hFR2 hout_c
                    have hpNew3 : nodeAt m' p tp wp n :=
                      nodeAt_free_other hpNew hFR2 hnePC
                    have hpre3 : PrefixChain m' head initP (some p) :=
                      hinit.transport_erase hnp hvic hsuf rfl hex
                        hFS hFR2
                    have hres : ListSeg m' head
                        (preVals initP ++ wp :: rest) :=
                      PrefixChain.appendSeg hpre3
                        (ListSeg.cons hpNew3 hsuf3)
                    have herase0 : vs.erase v =
                        preVals initP ++ wp :: rest := by
                      have h := herase'
                      rw [hsplitEq] at h
                      simpa [preVals] using h
                    rw [hbc] at hFR2
                    have hdead : memFind m' c =
                        some ⟨t, false, [v, linkWord n]⟩ :=
                      memFind_memFree_dead hvic2 hFR2
                    rw [herase0]
                    exact ⟨hres, fun _ => ⟨c, t, n, hdead⟩⟩

/-! ## Evaluator agreement -/

/-- The read-only chase succeeds on a well-formed segment with
    enough fuel (errors need a missing block or exhaustion,
    both ruled out). Induction on fuel, mirroring the
    invariant's case skeleton. -/
theorem listEraseChase_ok (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (v : BitVec 32) (prev cur : Option Addr)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hlen : suf.length ≤ F),
    ∃ m' prev' cur', listEraseChase F m prev cur v = .ok (m', prev', cur') := by
  induction F with
  | zero =>
    intro m hex v prev cur suf hseg hlen
    cases cur with
    | none => exact ⟨m, prev, none, by simp [listEraseChase]⟩
    | some a =>
      cases hseg with
      | cons _ t2 =>
        obtain ⟨vs', rfl⟩ := listSegVals t2
        exact False.elim (by
          simp only [List.length_cons] at hlen
          omega)
  | succ F ih =>
    intro m hex v prev cur suf hseg hlen
    cases cur with
    | none => exact ⟨m, prev, none, by simp [listEraseChase]⟩
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a t' 0 = .ok _ := nodeLoadVal hnode
        have hmem1 : memLoad m a t' 1 = .ok _ := nodeLoadNext hnode
        by_cases heq2 : (v₀ == v) = true
        · exact ⟨m, prev, some a, by
            unfold listEraseChase
            simp only [hfb, hmem0, hmem1, if_pos heq2]⟩
        · have halloc : ∀ c', nxt = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : nxt with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact ListSeg_head_alloc t2
          have hdec : addrOfWord (linkWord nxt) = nxt :=
            nodeAt_link_roundtrip hnode hex halloc
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨m'', p'', c'', hC''⟩ :=
            ih m hex v (some a) nxt vs' t2 hlen'
          exact ⟨m'', p'', c'', by
            unfold listEraseChase
            simp only [hfb, hmem0, hmem1, if_neg heq2, hdec, hC'']⟩

/-- Loop/evaluator agreement: the chase loop evaluates exactly
    as the read-only chase directs — miss falls through, hit
    unlinks, frees, and returns. The hit legs expose the unlink
    equations so the body wrap can match the forward function
    arm-for-arm. Induction on fuel, reusing the invariant's case
    skeleton (segment hypotheses rule out faults; fuel rules
    out exhaustion). -/
theorem listEraseLoop_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (head : Option Addr) (v : BitVec 32)
      (prev cur : Option Addr)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hplink : ∀ p, prev = some p → ∃ tp wp, nodeAt m p tp wp cur)
      (hlen : suf.length ≤ F)
      (m' : Mem) (prev' cur' : Option Addr)
      (hC : listEraseChase F m prev cur v = .ok (m', prev', cur')),
    (cur' = none →
      memEvalStmtFuel F listEraseLoop (mkListEraseEnv head v prev cur) m π =
        .ok ((mkListEraseEnv head v prev' none, m', π), .fellThrough)) ∧
    (∀ c, cur' = some c →
      ∃ hd' m'F,
        memEvalStmtFuel F listEraseLoop (mkListEraseEnv head v prev cur) m π =
          .ok ((mkListEraseEnv hd' v prev' (some c), m'F, π), .returned (.ptrVal hd')) ∧
        ((prev' = none ∧ ∃ t n, nodeAt m c t v n ∧ memFree m c t = .ok m'F ∧ hd' = n ∧
          addrOfWord (linkWord n) = n) ∨
         (∃ p tp wp t n m2', prev' = some p ∧ nodeAt m c t v n ∧
            nodeAt m p tp wp (some c) ∧ hd' = head ∧
            memStore m p tp 1 (linkWord n) = .ok m2' ∧
            memFree m2' c t = .ok m'F ∧
            addrOfWord (linkWord n) = n))) := by
  induction F with
  | zero =>
    intro m π hex head v prev cur suf hseg hplink hlen m' prev' cur' hC
    cases cur with
    | none =>
      have hC' : listEraseChase 0 m prev none v = .ok (m, prev, none) := by
        simp [listEraseChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      obtain ⟨e1, e2, e3⟩ := hC
      subst m'; subst prev'; subst cur'
      refine ⟨?_, ?_⟩
      · intro _
        have hcurE : memEvalExpr (.var "cur") (mkListEraseEnv head v prev none) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListEraseEnv_cur _ _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr) (mkListEraseEnv head v prev none) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListEraseEnv head v prev none) m π = .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel 0 listEraseLoop (mkListEraseEnv head v prev none) m π =
            .ok ((mkListEraseEnv head v prev none, m, π), .fellThrough) :=
          memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
        exact hw
      · intro c hcon
        cases hcon
    | some a =>
      unfold listEraseChase at hC
      simp only at hC
      cases hC
  | succ F ih =>
    intro m π hex head v prev cur suf hseg hplink hlen m' prev' cur' hC
    cases cur with
    | none =>
      have hC' : listEraseChase (F + 1) m prev none v = .ok (m, prev, none) := by
        simp [listEraseChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      obtain ⟨e1, e2, e3⟩ := hC
      subst m'; subst prev'; subst cur'
      refine ⟨?_, ?_⟩
      · intro _
        have hcurE : memEvalExpr (.var "cur") (mkListEraseEnv head v prev none) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListEraseEnv_cur _ _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr) (mkListEraseEnv head v prev none) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListEraseEnv head v prev none) m π = .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel (F + 1) listEraseLoop (mkListEraseEnv head v prev none) m π =
            .ok ((mkListEraseEnv head v prev none, m, π), .fellThrough) :=
          memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
        exact hw
      · intro c hcon
        cases hcon
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a t' 0 = .ok _ := nodeLoadVal hnode
        have hmem1 : memLoad m a t' 1 = .ok _ := nodeLoadNext hnode
        have hcurE : memEvalExpr (.var "cur") (mkListEraseEnv head v prev (some a)) m π =
            .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListEraseEnv_cur _ _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr) (mkListEraseEnv head v prev (some a)) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListEraseEnv head v prev (some a)) m π = .ok (.b true) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none hcurE hnullE
          have hbe : ((some a) != none) = true := by simp
          rw [hbe] at hg
          exact hg
        have hpget : memEvalExpr (.pgetVal (.var "cur")) (mkListEraseEnv head v prev (some a)) m π =
            .ok (.i32 v₀) :=
          memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE hfb hmem0
        have hvalE : memEvalExpr (.var "val") (mkListEraseEnv head v prev (some a)) m π =
            .ok (.i32 v) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListEraseEnv_val _ _ _ _)
        have hueq : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
            (mkListEraseEnv head v prev (some a)) m π = .ok (.b (v₀ == v)) := by
          unfold memEvalExpr
          simp only [hpget, hvalE]
        by_cases heq2 : (v₀ == v) = true
        · have hC' : listEraseChase (F + 1) m prev (some a) v =
              .ok (m, prev, some a) := by
            unfold listEraseChase
            simp only [hfb, hmem0, hmem1, if_pos heq2]
          rw [hC'] at hC
          simp only [Except.ok.injEq, Prod.mk.injEq] at hC
          obtain ⟨e1, e2, e3⟩ := hC
          subst m'; subst prev'; subst cur'
          have hvv : v₀ = v := beq_iff_eq.mp heq2
          subst v₀
          rw [heq2] at hueq
          refine ⟨?_, ?_⟩
          · intro hcon
            cases hcon
          intro c hcon
          cases hcon
          cases prev with
          | none =>
            have hprevE : memEvalExpr (.var "prev") (mkListEraseEnv head v none (some a)) m π =
                .ok (.ptrVal none) := by
              rw [memEvalExpr_var]
              exact evalExpr_var_hit _ _ _ (mkListEraseEnv_prev _ _ _ _)
            have hinnerT : memEvalExpr (.ueq (.var "prev") (.lit .nullptr))
                (mkListEraseEnv head v none (some a)) m π = .ok (.b true) := by
              have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _ none none hprevE hnullE
              have hbe : ((none : Option Addr) == none) = true := by simp
              rw [hbe] at hg
              exact hg
            have hpgn : memEvalExpr (.pgetNext (.var "cur")) (mkListEraseEnv head v none (some a)) m π =
                .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
              memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE hfb hmem1
            have huH : envUpdate (mkListEraseEnv head v none (some a)) "head"
                (.ptrVal (addrOfWord (linkWord nxt))) =
                some [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] := by
              simp [mkListEraseEnv, envUpdate]
            have hassignH := memEvalStmtFuel_assign_mem F "head" (.pgetNext (.var "cur"))
              (mkListEraseEnv head v none (some a)) m π _ _ hpgn huH
            have hfindC : memFind m a = some ⟨t', true, [v, linkWord nxt]⟩ := hnode
            obtain ⟨m2, hfree⟩ : ∃ m2, memFree m a t' = .ok m2 :=
              ⟨⟨m.next, (a, (⟨t', false, [v, linkWord nxt]⟩ : Block)) :: m.blocks,
                m.blocks64⟩, by simp [memFree, hfindC]⟩
            have hcurE2 : memEvalExpr (.var "cur")
                [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] m π =
                .ok (.ptrVal (some a)) := by
              rw [memEvalExpr_var]
              exact evalExpr_var_hit _ _ _ (by simp [envLookup])
            have hnfree := memEvalStmtFuel_nfree_ok F (.var "cur")
              [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] m π
              a ⟨t', true, [v, linkWord nxt]⟩ m2 hcurE2 hfindC hfree
            have hretE2 : memEvalExpr (.var "head")
                [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] m2 π =
                evalExpr (.var "head")
                  [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                    ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] :=
              memEvalExpr_var _ _ _ _
            have hretV2 : evalExpr (.var "head")
                [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] =
                .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
              evalExpr_var_hit _ _ _ (by simp [envLookup])
            have hret := memEvalStmtFuel_return F (.var "head")
              [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] m2 π
              _ hretE2 hretV2
            have hallocN : ∀ c'', nxt = some c'' → (memFind m c'').isSome = true := by
              intro c'' hc''
              cases hc''
              exact ListSeg_head_alloc t2
            have hdecN : addrOfWord (linkWord nxt) = nxt :=
              nodeAt_link_roundtrip hnode hex hallocN
            have hseqNR := memEvalStmtFuel_seq_fallthrough_trans F (.nfree (.var "cur")) (.return_ (.var "head"))
              [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] m π
              [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] m2 π _
              hnfree hret
            have hifInner : memEvalStmtFuel F
                (.if_ (.ueq (.var "prev") (.lit .nullptr))
                  (.assign "head" (.pgetNext (.var "cur")))
                  (.psetNext (.var "prev") (.pgetNext (.var "cur"))))
                (mkListEraseEnv head v none (some a)) m π =
                .ok (([("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)], m, π),
                  .fellThrough) :=
              (memEvalStmtFuel_if_true F _ _ _ _ _ _ hinnerT).trans hassignH
            have hunlink : memEvalStmtFuel F
                (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                        (.assign "head" (.pgetNext (.var "cur")))
                        (.psetNext (.var "prev") (.pgetNext (.var "cur"))))
                  (.seq (.nfree (.var "cur")) (.return_ (.var "head"))))
                (mkListEraseEnv head v none (some a)) m π =
                .ok (([("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)], m2, π),
                  .returned (.ptrVal (addrOfWord (linkWord nxt)))) :=
              memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                [("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)] _ _ _
                hifInner hseqNR
            have hueqT : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
                (mkListEraseEnv head v none (some a)) m π = .ok (.b true) := hueq
            have hifOuter : memEvalStmtFuel F
                (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
                  (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                          (.assign "head" (.pgetNext (.var "cur")))
                          (.psetNext (.var "prev") (.pgetNext (.var "cur"))))
                    (.seq (.nfree (.var "cur")) (.return_ (.var "head"))))
                  .skip)
                (mkListEraseEnv head v none (some a)) m π =
                .ok (([("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)], m2, π),
                  .returned (.ptrVal (addrOfWord (linkWord nxt)))) :=
              (memEvalStmtFuel_if_true F _ _ _ _ _ _ hueqT).trans hunlink
            have hbodyEv : memEvalStmtFuel F listEraseLoopBody
                (mkListEraseEnv head v none (some a)) m π =
                .ok (([("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)], m2, π),
                  .returned (.ptrVal (addrOfWord (linkWord nxt)))) :=
              memEvalStmtFuel_seq_return F _ _ _ _ _ _ _ _ _ hifOuter
            have hW : memEvalStmtFuel (F + 1) listEraseLoop
                (mkListEraseEnv head v none (some a)) m π =
                .ok (([("cur", .ptrVal (some a)), ("prev", .ptrVal none),
                  ("head", .ptrVal (addrOfWord (linkWord nxt))), ("val", .i32 v)], m2, π),
                  .returned (.ptrVal (addrOfWord (linkWord nxt)))) := by
              have h := memEvalStmtFuel_while_true F _ listEraseLoopBody _ _ _ hgT
              simp only [hbodyEv] at h
              exact h
            rw [hdecN] at hW
            exact ⟨nxt, m2, hW,
              .inl ⟨rfl, t', nxt, hnode, hfree, rfl, hdecN⟩⟩
          | some p =>
            obtain ⟨tp, wp, hpp⟩ := hplink p rfl
            have hne : p ≠ a := by
              intro hpa
              rw [hpa] at hpp
              have e1 : memFind m a = some ⟨t', true, [v, linkWord nxt]⟩ := hnode
              have e2 : memFind m a = some ⟨tp, true, [wp, linkWord (some a)]⟩ := hpp
              rw [e1] at e2
              simp only [Option.some.injEq, Block.mk.injEq] at e2
              have hlink : linkWord nxt = linkWord (some a) := by
                have hd := congrArg List.tail e2.2.2
                simpa using congrArg List.head? hd
              cases hnxt : nxt with
              | none =>
                rw [hnxt] at hlink
                exact linkWord_none_ne_some
                  (hex a (by rw [hfb]; rfl)) hlink
              | some c'' =>
                rw [hnxt] at hlink
                rw [hnxt] at t2
                have ha : c'' + 1 < 2 ^ 32 :=
                  hex c'' (ListSeg_head_alloc t2)
                have hb : a + 1 < 2 ^ 32 :=
                  hex a (by rw [hfb]; rfl)
                have hcc : c'' = a := linkWord_some_inj ha hb hlink
                rw [←hnxt] at t2
                have hmem : SegMem (m := m) nxt a := by
                  have hnxta : nxt = some a :=
                    hnxt.trans (congrArg some hcc)
                  rw [hnxta]
                  exact SegMem.here hpp
                exact ListSeg_head_notin_tail hnode t2 hex a hmem rfl
            have hallocN : ∀ c'', nxt = some c'' →
                (memFind m c'').isSome = true := by
              intro c'' hc''
              cases hc''
              exact ListSeg_head_alloc t2
            have hdecN : addrOfWord (linkWord nxt) = nxt :=
              nodeAt_link_roundtrip hnode hex hallocN
            obtain ⟨m1, hstore⟩ : ∃ m1, memStore m p tp 1
                (linkWord (addrOfWord (linkWord nxt))) = .ok m1 :=
              ⟨_, by have h := nodeStoreNext hpp nxt; rwa [← hdecN] at h⟩
            have hstoreN : memStore m p tp 1 (linkWord nxt) = .ok m1 := by
              have hw : linkWord (addrOfWord (linkWord nxt)) = linkWord nxt :=
                congrArg linkWord hdecN
              rw [hw] at hstore
              exact hstore
            have hfindM1 : memFind m1 a = some ⟨t', true, [v, linkWord nxt]⟩ := by
              have h := memFind_memStore_other m m1 p a tp 1
                (linkWord (addrOfWord (linkWord nxt))) hstore (Ne.symm hne)
              rw [hfb] at h
              exact h
            obtain ⟨m2, hfree2⟩ : ∃ m2, memFree m1 a t' = .ok m2 :=
              ⟨⟨m1.next, (a, (⟨t', false, [v, linkWord nxt]⟩ : Block)) ::
                m1.blocks, m1.blocks64⟩, by simp [memFree, hfindM1]⟩
            have hprevE : memEvalExpr (.var "prev")
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (.ptrVal (some p)) := by
              rw [memEvalExpr_var]
              exact evalExpr_var_hit _ _ _ (mkListEraseEnv_prev _ _ _ _)
            have hinnerF : memEvalExpr (.ueq (.var "prev") (.lit .nullptr))
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (.b false) := by
              have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _ (some p) none
                hprevE hnullE
              have hbe : (((some p) : Option Addr) == none) = false := by simp
              rw [hbe] at hg
              exact hg
            have hlinkE : memEvalExpr (.pgetNext (.var "cur"))
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
              memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE hfb hmem1
            have hfindP : memFind m p = some _ := hpp
            have hsetNext := memEvalStmtFuel_psetNext_ok F (.var "prev")
              (.pgetNext (.var "cur"))
              (mkListEraseEnv head v (some p) (some a)) m π p
              (addrOfWord (linkWord nxt)) _ m1
              hprevE hlinkE hfindP hstore
            have hcurE1 : memEvalExpr (.var "cur")
                (mkListEraseEnv head v (some p) (some a)) m1 π =
                .ok (.ptrVal (some a)) := by
              rw [memEvalExpr_var]
              exact evalExpr_var_hit _ _ _ (mkListEraseEnv_cur _ _ _ _)
            have hnfree2 := memEvalStmtFuel_nfree_ok F (.var "cur")
              (mkListEraseEnv head v (some p) (some a)) m1 π
              a ⟨t', true, [v, linkWord nxt]⟩ m2 hcurE1 hfindM1 hfree2
            have hretE : memEvalExpr (.var "head")
                (mkListEraseEnv head v (some p) (some a)) m2 π =
                evalExpr (.var "head")
                  (mkListEraseEnv head v (some p) (some a)) :=
              memEvalExpr_var _ _ _ _
            have hretV : evalExpr (.var "head")
                (mkListEraseEnv head v (some p) (some a)) =
                .ok (.ptrVal head) :=
              evalExpr_var_hit _ _ _ (mkListEraseEnv_head _ _ _ _)
            have hretI := memEvalStmtFuel_return F (.var "head")
              (mkListEraseEnv head v (some p) (some a)) m2 π
              _ hretE hretV
            have hseqNR := memEvalStmtFuel_seq_fallthrough_trans
              F (.nfree (.var "cur")) (.return_ (.var "head"))
              (mkListEraseEnv head v (some p) (some a)) m1 π
              (mkListEraseEnv head v (some p) (some a)) m2 π _
              hnfree2 hretI
            have hifInner : memEvalStmtFuel F
                (.if_ (.ueq (.var "prev") (.lit .nullptr))
                  (.assign "head" (.pgetNext (.var "cur")))
                  (.psetNext (.var "prev") (.pgetNext (.var "cur"))))
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (((mkListEraseEnv head v (some p) (some a)), m1, π),
                  .fellThrough) :=
              (memEvalStmtFuel_if_false F _ _ _ _ _ _ hinnerF).trans hsetNext
            have hunlink : memEvalStmtFuel F
                (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                        (.assign "head" (.pgetNext (.var "cur")))
                        (.psetNext (.var "prev") (.pgetNext (.var "cur"))))
                  (.seq (.nfree (.var "cur")) (.return_ (.var "head"))))
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (((mkListEraseEnv head v (some p) (some a)), m2, π),
                  .returned (.ptrVal head)) :=
              memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _
                (mkListEraseEnv head v (some p) (some a)) _ _ _
                hifInner hseqNR
            have hueqT : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (.b true) := hueq
            have hifOuter : memEvalStmtFuel F
                (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
                  (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                          (.assign "head" (.pgetNext (.var "cur")))
                          (.psetNext (.var "prev") (.pgetNext (.var "cur"))))
                    (.seq (.nfree (.var "cur")) (.return_ (.var "head"))))
                  .skip)
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (((mkListEraseEnv head v (some p) (some a)), m2, π),
                  .returned (.ptrVal head)) :=
              (memEvalStmtFuel_if_true F _ _ _ _ _ _ hueqT).trans hunlink
            have hbodyEv : memEvalStmtFuel F listEraseLoopBody
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (((mkListEraseEnv head v (some p) (some a)), m2, π),
                  .returned (.ptrVal head)) :=
              memEvalStmtFuel_seq_return F _ _ _ _ _ _ _ _ _ hifOuter
            have hW : memEvalStmtFuel (F + 1) listEraseLoop
                (mkListEraseEnv head v (some p) (some a)) m π =
                .ok (((mkListEraseEnv head v (some p) (some a)), m2, π),
                  .returned (.ptrVal head)) := by
              have h := memEvalStmtFuel_while_true F _ listEraseLoopBody _ _ _ hgT
              simp only [hbodyEv] at h
              exact h
            exact ⟨head, m2, hW,
              .inr ⟨p, tp, wp, t', nxt, m1,
                rfl, hnode, hpp, rfl, hstoreN, hfree2, hdecN⟩⟩
        · have heqF : (v₀ == v) = false := by
            cases h : (v₀ == v) with
            | true => exact absurd h heq2
            | false => rfl
          have hueqF : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
              (mkListEraseEnv head v prev (some a)) m π =
              .ok (.b false) := by
            rw [heqF] at hueq
            exact hueq
          have hskip : memEvalStmtFuel F .skip
              (mkListEraseEnv head v prev (some a)) m π =
              .ok (((mkListEraseEnv head v prev (some a)), m, π),
                .fellThrough) := by
            cases F <;> rfl
          have hifOuterF : memEvalStmtFuel F
              (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
                (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                        (.assign "head" (.pgetNext (.var "cur")))
                        (.psetNext (.var "prev") (.pgetNext (.var "cur"))))
                  (.seq (.nfree (.var "cur")) (.return_ (.var "head"))))
                .skip)
              (mkListEraseEnv head v prev (some a)) m π =
              .ok (((mkListEraseEnv head v prev (some a)), m, π),
                .fellThrough) :=
            (memEvalStmtFuel_if_false F _ _ _ _ _ _ hueqF).trans hskip
          have hstep1 : memEvalStmtFuel F (.assign "prev" (.var "cur"))
              (mkListEraseEnv head v prev (some a)) m π =
              .ok (((mkListEraseEnv head v (some a) (some a)), m, π),
                .fellThrough) :=
            memEvalStmtFuel_assign_mem F "prev" (.var "cur")
              (mkListEraseEnv head v prev (some a)) m π _ _ hcurE
              (by simp [mkListEraseEnv, envUpdate])
          have hcurE1 : memEvalExpr (.var "cur")
              (mkListEraseEnv head v (some a) (some a)) m π =
              .ok (.ptrVal (some a)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ (mkListEraseEnv_cur _ _ _ _)
          have hlinkE1 : memEvalExpr (.pgetNext (.var "cur"))
              (mkListEraseEnv head v (some a) (some a)) m π =
              .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE1 hfb hmem1
          have hstep2 : memEvalStmtFuel F
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkListEraseEnv head v (some a) (some a)) m π =
              .ok (((mkListEraseEnv head v (some a)
                  (addrOfWord (linkWord nxt))), m, π),
                .fellThrough) :=
            memEvalStmtFuel_assign_mem F "cur" (.pgetNext (.var "cur"))
              (mkListEraseEnv head v (some a) (some a)) m π _ _ hlinkE1
              (by simp [mkListEraseEnv, envUpdate])
          have hstep : memEvalStmtFuel F
              (.seq (.assign "prev" (.var "cur"))
                (.assign "cur" (.pgetNext (.var "cur"))))
              (mkListEraseEnv head v prev (some a)) m π =
              .ok (((mkListEraseEnv head v (some a)
                  (addrOfWord (linkWord nxt))), m, π),
                .fellThrough) :=
            memEvalStmtFuel_seq_fallthrough_trans F
              (.assign "prev" (.var "cur"))
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkListEraseEnv head v prev (some a)) m π
              (mkListEraseEnv head v (some a) (some a)) m π _
              hstep1 hstep2
          have hbodyEv : memEvalStmtFuel F listEraseLoopBody
              (mkListEraseEnv head v prev (some a)) m π =
              .ok (((mkListEraseEnv head v (some a)
                  (addrOfWord (linkWord nxt))), m, π),
                .fellThrough) :=
            memEvalStmtFuel_seq_fallthrough_trans F _ _
              (mkListEraseEnv head v prev (some a)) _ _
              (mkListEraseEnv head v prev (some a)) _ _ _
              hifOuterF hstep
          have hWh : memEvalStmtFuel (F + 1) listEraseLoop
              (mkListEraseEnv head v prev (some a)) m π =
              memEvalStmtFuel F listEraseLoop
                (mkListEraseEnv head v (some a)
                  (addrOfWord (linkWord nxt))) m π := by
            have h := memEvalStmtFuel_while_true F _ listEraseLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          have hallocN : ∀ c'', nxt = some c'' →
              (memFind m c'').isSome = true := by
            intro c'' hc''
            cases hc''
            exact ListSeg_head_alloc t2
          have hdecN : addrOfWord (linkWord nxt) = nxt :=
            nodeAt_link_roundtrip hnode hex hallocN
          have hnode' : nodeAt m a t' v₀ (addrOfWord (linkWord nxt)) := by
            rw [hdecN]
            exact hnode
          have hplink' : ∀ p, (some a) = some p →
              ∃ tp wp, nodeAt m p tp wp (addrOfWord (linkWord nxt)) := by
            intro p hp
            cases hp
            exact ⟨t', v₀, hnode'⟩
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          have hC'' : listEraseChase F m (some a) (addrOfWord (linkWord nxt)) v =
              .ok (m', prev', cur') := by
            have hch := hC
            unfold listEraseChase at hch
            simp only [hfb, hmem0, hmem1] at hch
            rw [if_neg heq2] at hch
            exact hch
          have t2' : ListSeg m (addrOfWord (linkWord nxt)) vs' := by
            rw [hdecN]
            exact t2
          have hIH := ih m π hex head v (some a) (addrOfWord (linkWord nxt))
            vs' t2' hplink' hlen' m' prev' cur' hC''
          refine ⟨?_, ?_⟩
          · intro hcon
            have hstep := hIH.1 hcon
            rw [hWh]
            exact hstep
          · intro c hcon
            obtain ⟨hd', m'F, hev, hdisj⟩ := hIH.2 c hcon
            exact ⟨hd', m'F, by rw [hWh]; exact hev, hdisj⟩

/-- The chase never writes: every `.ok` return carries the input
    memory (errors abort loudly; the recursive leg threads `m`
    through unchanged). The entry proof uses this to identify the
    forward mirror's memory with the evaluator's. -/
theorem listEraseChase_mem (F : Nat) :
    ∀ (m : Mem) (prev cur : Option Addr) (v : BitVec 32)
      (m' : Mem) (prev' cur' : Option Addr),
      listEraseChase F m prev cur v = .ok (m', prev', cur') → m' = m := by
  induction F with
  | zero =>
    intro m prev cur v m' prev' cur' h
    cases cur with
    | none =>
      simp only [listEraseChase, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2, e3⟩ := h
      exact e1.symm
    | some a => simp [listEraseChase] at h
  | succ F ih =>
    intro m prev cur v m' prev' cur' h
    cases cur with
    | none =>
      simp only [listEraseChase, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2, e3⟩ := h
      exact e1.symm
    | some a =>
      have hch := h
      unfold listEraseChase at hch
      cases hF : memFind m a with
      | none => simp [hF] at hch
      | some b =>
        simp only [hF] at hch
        cases hL0 : memLoad m a b.tag 0 with
        | error e => simp [hL0] at hch
        | ok w =>
          simp only [hL0] at hch
          by_cases heq : (w == v) = true
          · rw [if_pos heq] at hch
            simp only [Except.ok.injEq, Prod.mk.injEq] at hch
            obtain ⟨e1, e2, e3⟩ := hch
            exact e1.symm
          · rw [if_neg heq] at hch
            cases hL1 : memLoad m a b.tag 1 with
            | error e => simp [hL1] at hch
            | ok w' =>
              simp only [hL1] at hch
              exact ih m (some a) (addrOfWord w') v m' prev' cur' hch

/-- The erase entry evaluates as the mirror and returns the
    unlinked head with the victim freed. Seed lets build the chase
    environment, the loop agree fires the chase result (miss falls
    through to the final return, hit returns early), and the
    forward contract supplies the segment fact. -/
theorem listEraseFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hlen : vs.length ≤ F)
    (hfwd : listEraseFwd F m head v = .ok (m', hd')) :
    ∃ ρ', memEvalStmtFuel F listEraseFunc.body
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      .ok ((ρ', m', π), .returned (.ptrVal hd')) ∧
      ListSeg m' hd' (vs.erase v) ∧
      (v ∈ vs → ∃ c t n, memFind m' c =
        some ⟨t, false, [v, linkWord n]⟩) := by
  have hsegF := listEraseFwd_correct F m hex head v vs m' hd'
    hseg hlen hfwd
  obtain ⟨m1, prevC, curC, hC⟩ :=
    listEraseChase_ok F m hex v none head vs hseg hlen
  have hmem : m1 = m :=
    listEraseChase_mem F m none head v m1 prevC curC hC
  subst m1
  have hplink0 : ∀ p, none = some p →
      ∃ tp wp, nodeAt m p tp wp head := by
    intro p hp
    cases hp
  -- Seed: the two cursor lets build the chase environment.
  have eP : memEvalExpr (.lit .nullptr)
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      evalExpr (.lit .nullptr)
        [("head", .ptrVal head), ("val", .i32 v)] :=
    memEvalExpr_lit _ _ _ _
  have vP : evalExpr (.lit .nullptr)
      [("head", .ptrVal head), ("val", .i32 v)] =
      .ok (.ptrVal none) := by simp [evalExpr, litVal]
  have hA := memEvalStmtFuel_let_pure F "prev" nodeTy (.lit .nullptr)
    _ _ _ (.ptrVal none)
    (by simp) (by simp) (by simp) (by simp) eP vP
  have eC : memEvalExpr (.var "head")
      ([("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) m π =
      evalExpr (.var "head")
        ([("prev", .ptrVal none),
          ("head", .ptrVal head), ("val", .i32 v)]) :=
    memEvalExpr_var _ _ _ _
  have vC : evalExpr (.var "head")
      ([("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) =
      .ok (.ptrVal head) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hB := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
    _ _ _ (.ptrVal head)
    (by simp) (by simp) (by simp) (by simp) eC vC
  have hloop := listEraseLoop_agree F m π hex head v none head vs
    hseg hplink0 hlen m prevC curC hC
  have hbody : listEraseFunc.body = listEraseBody := rfl
  rw [hbody]
  cases curC with
  | none =>
    have hmiss := hloop.1 rfl
    have hfwd' : listEraseFwd F m head v = .ok (m, head) := by
      simp only [listEraseFwd, hC]
    have h1 := hfwd
    rw [hfwd'] at h1
    simp only [Except.ok.injEq, Prod.mk.injEq] at h1
    obtain ⟨e1, e2⟩ := h1
    rw [←e1, ←e2] at hsegF ⊢
    have hretE : memEvalExpr (.var "head")
        (mkListEraseEnv head v prevC none) m π =
        evalExpr (.var "head") (mkListEraseEnv head v prevC none) :=
      memEvalExpr_var _ _ _ _
    have hretV : evalExpr (.var "head")
        (mkListEraseEnv head v prevC none) =
        .ok (.ptrVal head) :=
      evalExpr_var_hit _ _ _ (mkListEraseEnv_head _ _ _ _)
    have hret := memEvalStmtFuel_return F (.var "head")
      (mkListEraseEnv head v prevC none) m π _ hretE hretV
    have hRest2 := memEvalStmtFuel_seq_fallthrough_trans F
      listEraseLoop (.return_ (.var "head"))
      (mkListEraseEnv head v none head) m π
      (mkListEraseEnv head v prevC none) m π _
      hmiss hret
    have hRest := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "head"))
      (.seq listEraseLoop (.return_ (.var "head")))
      ([("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) m π
      (mkListEraseEnv head v none head) m π _
      hB hRest2
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "prev" nodeTy (.lit .nullptr))
      (.seq (.let_ "cur" nodeTy (.var "head"))
        (.seq listEraseLoop (.return_ (.var "head"))))
      ([("head", .ptrVal head), ("val", .i32 v)]) m π
      ([("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) m π _
      hA hRest
    exact ⟨_, hTop, hsegF.1, hsegF.2⟩
  | some c =>
    obtain ⟨hd'', m'F, hev, hdisj⟩ := hloop.2 c rfl
    cases hdisj with
    | inl h =>
      obtain ⟨rfl, t, n, hnodeC, hfreeC, hhd, hrd⟩ := h
      have hfindC : memFind m c = some ⟨t, true, [v, linkWord n]⟩ :=
        hnodeC
      have hmemL : memLoad m c t 1 = .ok (linkWord n) :=
        nodeLoadNext hnodeC
      have hfwd' : listEraseFwd F m head v = .ok (m'F, n) := by
        simp only [listEraseFwd, hC, hfindC, hmemL, hfreeC, hrd]
      have h1 := hfwd
      rw [hfwd'] at h1
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨e1, e2⟩ := h1
      rw [←e1, ←e2] at hsegF ⊢
      rw [hhd] at hev
      have hRest2 := memEvalStmtFuel_seq_return F
        listEraseLoop (.return_ (.var "head"))
        (mkListEraseEnv head v none head) m π
        (mkListEraseEnv n v none (some c)) m'F π _ hev
      have hRest := memEvalStmtFuel_seq_fallthrough_trans F
        (.let_ "cur" nodeTy (.var "head"))
        (.seq listEraseLoop (.return_ (.var "head")))
        ([("prev", .ptrVal none),
          ("head", .ptrVal head), ("val", .i32 v)]) m π
        (mkListEraseEnv head v none head) m π _
        hB hRest2
      have hTop := memEvalStmtFuel_seq_fallthrough_trans F
        (.let_ "prev" nodeTy (.lit .nullptr))
        (.seq (.let_ "cur" nodeTy (.var "head"))
          (.seq listEraseLoop (.return_ (.var "head"))))
        ([("head", .ptrVal head), ("val", .i32 v)]) m π
        ([("prev", .ptrVal none),
          ("head", .ptrVal head), ("val", .i32 v)]) m π _
        hA hRest
      exact ⟨_, hTop, hsegF.1, hsegF.2⟩
    | inr h =>
      obtain ⟨p, tp, wp, t, n, m2', rfl, hnodeC, hpp, hhdC, hstore,
        hfreeC, hrd⟩ := h
      have hfindC : memFind m c = some ⟨t, true, [v, linkWord n]⟩ :=
        hnodeC
      have hmemL : memLoad m c t 1 = .ok (linkWord n) :=
        nodeLoadNext hnodeC
      have hfindP : memFind m p = some _ := hpp
      have hfwd' : listEraseFwd F m head v = .ok (m'F, head) := by
        simp only [listEraseFwd, hC, hfindC, hmemL, hfindP, hstore, hfreeC]
      have h1 := hfwd
      rw [hfwd'] at h1
      simp only [Except.ok.injEq, Prod.mk.injEq] at h1
      obtain ⟨e1, e2⟩ := h1
      rw [←e1, ←e2] at hsegF ⊢
      rw [hhdC] at hev
      have hRest2 := memEvalStmtFuel_seq_return F
        listEraseLoop (.return_ (.var "head"))
        (mkListEraseEnv head v none head) m π
        (mkListEraseEnv head v (some p) (some c)) m'F π _ hev
      have hRest := memEvalStmtFuel_seq_fallthrough_trans F
        (.let_ "cur" nodeTy (.var "head"))
        (.seq listEraseLoop (.return_ (.var "head")))
        ([("prev", .ptrVal none),
          ("head", .ptrVal head), ("val", .i32 v)]) m π
        (mkListEraseEnv head v none head) m π _
        hB hRest2
      have hTop := memEvalStmtFuel_seq_fallthrough_trans F
        (.let_ "prev" nodeTy (.lit .nullptr))
        (.seq (.let_ "cur" nodeTy (.var "head"))
          (.seq listEraseLoop (.return_ (.var "head"))))
        ([("head", .ptrVal head), ("val", .i32 v)]) m π
        ([("prev", .ptrVal none),
          ("head", .ptrVal head), ("val", .i32 v)]) m π _
        hA hRest
      exact ⟨_, hTop, hsegF.1, hsegF.2⟩
