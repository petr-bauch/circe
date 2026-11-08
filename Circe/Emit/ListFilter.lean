/-
Circe.Emit.ListFilter — pillar-1 remove-if: unlink every matching
node and `free` it (`list_filter`) over caller-owned
`Node {val, next}`.

The corpus (`tests/cpp/list_filter.cpp`, entry
`Node *list_filter(Node *head, int val)`) chases with a trailing
pointer and, for every node whose payload matches, swings the
predecessor link (head case: `head = next`; interior case:
`prev->next = next`), frees the victim, and advances only the
cursor; keeps advance both cursors. Survivors keep their
relative order. A miss (or empty input) returns the head
untouched with no `free` — silent legs, covered by the loop
guard, not a branch. Faults are loud, not branched: freeing a
null, missing, or already-freed cell aborts in the model
(`memFree`/`memStore` miss/tag/liveness checks), exactly the
L-ptr miss discipline. The single pointer param needs no
`__restrict__` (single-pointer exemption); cycles are out of
scope.

The mirror sweeps with `listFilterSweep` (fuel-indexed: each
visit reads the payload at `[0]`, on a match reads the link at
`[1]`, restitches, frees, and recurses; a keep recurses past
the node). The contract is a removal of every match:
`ListSeg m' hd' (vs.filter (· != v))` with every original
victim cell dead (live flag cleared — contents kept but
unusable, so any later dereference misses loudly).
Freshness-style hypotheses are unnecessary (nothing
allocates); the fuel bound rules out exhaustion and exactness
decodes the links. The hard proof is repeated segment surgery
around dead cells: the survivor prefix is rebuilt step by step
(`PrefixChain` snoc/restitch), the freed prefix grows like the
clear chase, and the untouched suffix rides `store_other` +
`free_other` with the victim kept out by acyclicity.
-/
import Circe.Emit.LinkedReverse

/-! ## P3: `list_filter` entry -/

/-- Mangled name of the filter entry. -/
def listFilterName : String :=
  "_Z11list_filterP4Nodei"

/-- The chase-loop body (guard, hit-or-step): named so the
    agreement proof can rewrite it without literals. On a match
    the link is saved, the predecessor (or the head) is swung
    past the victim, the victim is freed, and only the cursor
    advances; on a keep both cursors advance. -/
def listFilterLoopBody : CStmt :=
  (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
    (.seq (.assign "next" (.pgetNext (.var "cur")))
      (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
              (.assign "head" (.var "next"))
              (.psetNext (.var "prev") (.var "next")))
        (.seq (.nfree (.var "cur"))
          (.assign "cur" (.var "next")))))
    (.seq (.assign "prev" (.var "cur"))
      (.assign "cur" (.pgetNext (.var "cur")))))

/-- The chase loop (isolated for the loop/evaluator
    agreement: guard, hit-or-step body). -/
def listFilterLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) listFilterLoopBody)

/-- Canonical CoreIR for `list_filter`: seed the cursors, chase
    while `cur != nullptr`, unlink + free + advance-only-cursor
    on every payload hit, step both cursors otherwise, return
    the (possibly new) head on exhaustion. -/
def listFilterBody : CStmt :=
  (.seq (.let_ "prev" nodeTy (.lit .nullptr))
    (.seq (.let_ "cur" nodeTy (.var "head"))
      (.seq (.let_ "next" nodeTy (.lit .nullptr))
        (.seq listFilterLoop
          (.return_ (.var "head"))))))

/-- The filter entry: `Node*` + `i32` in, `Node*` out. -/
def listFilterFunc : Func :=
  ⟨listFilterName,
   [{ name := "head", ty := nodeTy, role := .owned },
    { name := "val", ty := (.i 32), role := .owned }],
   nodeTy,
   listFilterBody⟩

/-- Filter environment: head and payload slots, then the two
    cursor slots plus the link spare (the entry binds `head`
    and `val` first, then the lets cons `prev`, `cur`, and
    `next` on the front; assigns rewrite slots in place). -/
def mkListFilterEnv (head : Option Addr) (v : BitVec 32)
    (prev cur nxt : Option Addr) : Env :=
  [("next", .ptrVal nxt), ("cur", .ptrVal cur),
    ("prev", .ptrVal prev),
    ("head", .ptrVal head), ("val", .i32 v)]

theorem mkListFilterEnv_next (head : Option Addr) (v : BitVec 32)
    (prev cur nxt : Option Addr) :
    envLookup (mkListFilterEnv head v prev cur nxt) "next" =
      some (.ptrVal nxt) := by
  simp [mkListFilterEnv, envLookup]

theorem mkListFilterEnv_cur (head : Option Addr) (v : BitVec 32)
    (prev cur nxt : Option Addr) :
    envLookup (mkListFilterEnv head v prev cur nxt) "cur" =
      some (.ptrVal cur) := by
  simp [mkListFilterEnv, envLookup]

theorem mkListFilterEnv_prev (head : Option Addr) (v : BitVec 32)
    (prev cur nxt : Option Addr) :
    envLookup (mkListFilterEnv head v prev cur nxt) "prev" =
      some (.ptrVal prev) := by
  simp [mkListFilterEnv, envLookup]

theorem mkListFilterEnv_head (head : Option Addr) (v : BitVec 32)
    (prev cur nxt : Option Addr) :
    envLookup (mkListFilterEnv head v prev cur nxt) "head" =
      some (.ptrVal head) := by
  simp [mkListFilterEnv, envLookup]

theorem mkListFilterEnv_val (head : Option Addr) (v : BitVec 32)
    (prev cur nxt : Option Addr) :
    envLookup (mkListFilterEnv head v prev cur nxt) "val" =
      some (.i32 v) := by
  simp [mkListFilterEnv, envLookup]

/-! ## Forward mirror (single sweep, unlink inline) -/

/-- Sweep every payload match out of the chain: read-only until
    the link read (payload at `[0]`, then link at `[1]` on a
    match), restitch the predecessor (or the head), free the
    victim, and recurse past it; a keep recurses past the node
    with the memory untouched. Each visit consumes fuel (like
    the evaluator's loop iteration — a drop needs fuel too).
    Misses, dangling links, and short blocks abort loudly at
    any fuel. -/
def listFilterSweep (F : Nat) (m : Mem)
    (head prev cur : Option Addr) (v : BitVec 32)
    (dropped : List (Addr × Nat × List (BitVec 32))) :
    Result (Mem × Option Addr × List (Addr × Nat × List (BitVec 32))) :=
  match cur with
  | none => .ok (m, head, dropped)
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
          if w == v then
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' =>
              match prev with
              | none =>
                match memFree m a b.tag with
                | .error e => .error e
                | .ok m1 =>
                  listFilterSweep F m1 (addrOfWord w') none
                    (addrOfWord w') v (dropped ++ [(a, b.tag, [w, w'])])
              | some p =>
                match memFind m p with
                | none => .error .AssertFail
                | some bp =>
                  match memStore m p bp.tag 1 w' with
                  | .error e => .error e
                  | .ok m1 =>
                    match memFree m1 a b.tag with
                    | .error e => .error e
                    | .ok m2 =>
                      listFilterSweep F m2 head (some p)
                        (addrOfWord w') v (dropped ++ [(a, b.tag, [w, w'])])
          else
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' =>
              listFilterSweep F m head (some a) (addrOfWord w') v dropped

/-- Entry mirror: sweep from the entry head with no predecessor.
    -/
def listFilterFwd (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) : Result (Mem × Option Addr) :=
  match listFilterSweep F m head none head v [] with
  | .error e => .error e
  | .ok (m', hd', _) => .ok (m', hd')

/-! ## Sweep invariant: every visit is kept or dropped -/

/-- Sweep invariant: the read-only prefix is pinned as a
    `PrefixChain` of kept nodes (all payloads differ from `v`),
    the suffix is an untouched `ListSeg`, previously dropped
    cells stay dead with `v`-payload blocks, and the result
    equation assembles the kept prefix with the filtered
    suffix. Induction is on fuel; the drop legs snoc the victim
    (head case) or restitch the predecessor (interior case) and
    recurse, the keep leg snocs the visited node. -/
theorem listFilterSweep_invariant (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (kept : List (Addr × Nat × BitVec 32))
      (head prev cur : Option Addr) (v : BitVec 32)
      (suf : List (BitVec 32))
      (dropped : List (Addr × Nat × List (BitVec 32)))
      (hchain : PrefixChain m head kept cur)
      (hseg : ListSeg m cur suf)
      (hprevnil : prev = none → kept = [])
      (hprevlast : ∀ p, prev = some p →
        ∃ init lt lw, kept = init ++ [(p, lt, lw)])
      (hplink : ∀ p, prev = some p → ∃ tp wp, nodeAt m p tp wp cur)
      (hclean : ∀ w ∈ preVals kept, w ≠ v)
      (hdead : ∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)), (a, t, blk) ∈ dropped → ∃ n, blk = [v, linkWord n] ∧
        memFind m a = some ⟨t, false, blk⟩)
      (hlen : suf.length ≤ F)
      (m' : Mem) (hd' : Option Addr)
      (droppedOut : List (Addr × Nat × List (BitVec 32)))
      (hsw : listFilterSweep F m head prev cur v dropped =
        .ok (m', hd', droppedOut)),
    ∃ kept₁,
      PrefixChain m' hd' kept₁ none ∧
      (preVals kept ++ suf.filter (· != v)) = preVals kept₁ ∧
      (∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)), (a, t, blk) ∈ droppedOut → ∃ n, blk = [v, linkWord n] ∧
        memFind m' a = some ⟨t, false, blk⟩) := by

  induction F with
  | zero =>
    intro m hex kept head prev cur v suf dropped hchain hseg
      hprevnil hprevlast hplink hclean hdead hlen m' hd'
      droppedOut hsw
    cases cur with
    | none =>
      have hC' : listFilterSweep 0 m head prev none v dropped =
          .ok (m, head, dropped) := by
        simp [listFilterSweep]
      rw [hC'] at hsw
      simp only [Except.ok.injEq, Prod.mk.injEq] at hsw
      obtain ⟨e1, e2, e3⟩ := hsw
      subst m'; subst hd'; subst droppedOut
      cases hseg with
      | nil =>
        refine ⟨kept, ?_, ?_, ?_⟩
        · exact hchain
        · simp
        · exact hdead
    | some a =>
      unfold listFilterSweep at hsw
      simp only at hsw
      cases hsw
  | succ F ih =>
    intro m hex kept head prev cur v suf dropped hchain hseg
      hprevnil hprevlast hplink hclean hdead hlen m' hd'
      droppedOut hsw
    cases cur with
    | none =>
      have hC' : listFilterSweep (F + 1) m head prev none v dropped =
          .ok (m, head, dropped) := by
        simp [listFilterSweep]
      rw [hC'] at hsw
      simp only [Except.ok.injEq, Prod.mk.injEq] at hsw
      obtain ⟨e1, e2, e3⟩ := hsw
      subst m'; subst hd'; subst droppedOut
      cases hseg with
      | nil =>
        refine ⟨kept, ?_, ?_, ?_⟩
        · exact hchain
        · simp
        · exact hdead
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
        have halloc : ∀ c', nxt = some c' →
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
        by_cases heq2 : (v₀ == v) = true
        · -- Drop leg: the payload matches, unlink + free + advance.
          have hvv : v₀ = v := beq_iff_eq.mp heq2
          subst v₀
          unfold listFilterSweep at hsw
          simp only [hfb, hmem0, hmem1, ite_eq_left heq2] at hsw
          cases prev with
          | none =>
            obtain hkept0 : kept = [] := hprevnil rfl
            cases hFR : memFree m a t' with
            | error e =>
              simp only [hFR] at hsw
              cases hsw
            | ok m1 =>
              simp only [hFR] at hsw
              rw [hdec] at hsw
              subst hkept0
              have hchain' : PrefixChain m1 nxt [] nxt := .nil
              have hsuf3 : ListSeg m1 nxt vs' :=
                t2.free_other hFR (fun b hmemB =>
                  ListSeg_head_notin_tail hnode t2 hex b hmemB)
              have hdead' : ∀ (a2 : Addr) (t2 : Nat) (blk : List (BitVec 32)), (a2, t2, blk) ∈
                  dropped ++ [(a, t', [v, linkWord nxt])] → ∃ n,
                  blk = [v, linkWord n] ∧
                  memFind m1 a2 = some ⟨t2, false, blk⟩ := by
                intro a2 t2 blk hmem2
                rw [List.mem_append] at hmem2
                cases hmem2 with
                | inl hmem2 =>
                  obtain ⟨n2, hblk, hfind⟩ := hdead _ _ _ hmem2
                  have hne2 : a2 ≠ a := by
                    intro hcon
                    rw [hcon, hfb] at hfind
                    simp only [Option.some.injEq, Block.mk.injEq] at hfind
                    obtain ⟨_, hcontra, _⟩ := hfind
                    cases hcontra
                  refine ⟨n2, hblk, ?_⟩
                  rw [memFind_memFree_other _ _ _ _ _ hFR hne2]
                  exact hfind
                | inr hmem2 =>
                  simp only [List.mem_singleton] at hmem2
                  obtain ⟨rfl, rfl, rfl⟩ := hmem2
                  exact ⟨nxt, rfl,
                    memFind_memFree_dead hnode hFR⟩
              have hex1 : ∀ x, (memFind m1 x).isSome = true →
                  x + 1 < 2 ^ 32 := by
                intro x hx
                by_cases heqx : x = a
                · rw [heqx]
                  exact hex a (by rw [hfb]; rfl)
                · rw [memFind_memFree_other _ _ _ _ _ hFR heqx] at hx
                  exact hex x hx
              have hIH := ih m1 hex1 [] nxt none nxt v vs'
                (dropped ++ [(a, t', [v, linkWord nxt])])
                hchain' hsuf3 (fun _ => rfl)
                (by intro p hp; cases hp) (by intro p hp; cases hp)
                (by simp [preVals]) hdead' hlen' m' hd' droppedOut hsw
              obtain ⟨kept₁, hch1, hbridge, hdead1⟩ := hIH
              refine ⟨kept₁, hch1, ?_, hdead1⟩
              have hflt : (v :: vs').filter (· != v) =
                  vs'.filter (· != v) := by simp
              rw [hflt]
              exact hbridge
          | some p =>
            obtain ⟨tp, wp, hnp⟩ := hplink p rfl
            cases hFp : memFind m p with
            | none =>
              simp only [hFp] at hsw
              cases hsw
            | some bp =>
              simp only [hFp] at hsw
              have hfindP : memFind m p = some _ := hnp
              rw [hfindP] at hFp
              cases hFp
              cases hFS : memStore m p tp 1 (linkWord nxt) with
              | error e =>
                simp only [hFS] at hsw
                cases hsw
              | ok m2' =>
                simp only [hFS] at hsw
                cases hFR2 : memFree m2' a t' with
                | error e =>
                  simp only [hFR2] at hsw
                  cases hsw
                | ok m3 =>
                  simp only [hFR2] at hsw
                  rw [hdec] at hsw
                  obtain ⟨init, lt, lw, hsplitEq⟩ := hprevlast p rfl
                  rw [hsplitEq] at hchain
                  obtain ⟨midp, hinit, hplast⟩ := PrefixChain.split hchain
                  cases hplast with
                  | cons hnodeP' hrestP =>
                    cases hrestP
                    have hfindP2 : memFind m p = some _ := hnodeP'
                    rw [hfindP2] at hfindP
                    cases hfindP
                    have hpNew2 : nodeAt m2' p tp wp nxt :=
                      nodeStoreNext_nodeAt hnp hFS
                    have hnePC : p ≠ a := by
                      intro hcon
                      have hnpC : nodeAt m a tp wp (some a) := hcon ▸ hnp
                      have hmemC : SegMem (m := m) (some a) a :=
                        SegMem.here hnode
                      have htailP : ListSeg m (some a) (v :: vs') :=
                        ListSeg.cons hnode t2
                      have hcontra :=
                        ListSeg_head_notin_tail hnpC htailP hex a hmemC
                      exact hcontra rfl
                    have hneCP : a ≠ p := Ne.symm hnePC
                    have hvic2 : nodeAt m2' a t' v nxt :=
                      nodeAt_store_other_fwd hnode hFS hneCP
                    have hfindP' : memFind m p = some _ := hnp
                    have hliveP : (memFind m p).isSome = true := by
                      have h := congrArg Option.isSome hfindP'
                      simpa using h
                    have hex2 : ∀ x, (memFind m2' x).isSome = true →
                        x + 1 < 2 ^ 32 :=
                      hex_store hex hFS hliveP
                    have hout_p : ∀ b, SegMem (m := m) nxt b → b ≠ p := by
                      intro b hmemB
                      have hmemC : SegMem (m := m) (some a) b :=
                        hmemB.victimCons hnode
                      have htailP : ListSeg m (some a) (v :: vs') :=
                        ListSeg.cons hnode t2
                      exact ListSeg_head_notin_tail hnp htailP hex b hmemC
                    have hsuf2 : ListSeg m2' nxt vs' :=
                      t2.store_other hFS hout_p
                    have hout_c : ∀ b, SegMem (m := m2') nxt b → b ≠ a := by
                      intro b hmemB
                      exact ListSeg_head_notin_tail hvic2 hsuf2 hex2 b hmemB
                    have hsuf3 : ListSeg m3 nxt vs' :=
                      hsuf2.free_other hFR2 hout_c
                    have hpreT : PrefixChain m3 head init (some p) :=
                      hinit.transport_erase hnp hnode t2 rfl hex hFS hFR2
                    have hpNew3 : nodeAt m3 p tp wp nxt :=
                      nodeAt_free_other hpNew2 hFR2 hnePC
                    have hchain' : PrefixChain m3 head
                        (init ++ [(p, tp, wp)]) nxt :=
                      PrefixChain.snoc_extend hpreT hpNew3 rfl rfl
                    have hprevnil' : (some p : Option Addr) = none →
                        init ++ [(p, tp, wp)] = [] := by
                      intro h
                      cases h
                    have hprevlast' : ∀ q, (some p : Option Addr) = some q →
                        ∃ init' lt' lw',
                          init ++ [(p, tp, wp)] = init' ++ [(q, lt', lw')] := by
                      intro q hq
                      cases hq
                      exact ⟨init, tp, wp, rfl⟩
                    have hplink' : ∀ q, (some p : Option Addr) = some q →
                        ∃ tq wq, nodeAt m3 q tq wq nxt := by
                      intro q hq
                      cases hq
                      exact ⟨tp, wp, hpNew3⟩
                    have happInit : preVals (init ++ [(p, tp, wp)]) =
                        preVals init ++ [wp] := by simp [preVals]
                    have hclean' : ∀ w ∈
                        preVals (init ++ [(p, tp, wp)]), w ≠ v := by
                      intro w hw
                      rw [hsplitEq] at hclean
                      rw [happInit] at hclean hw
                      cases (List.mem_append.mp hw) with
                      | inl hw => exact hclean w (List.mem_append.mpr (.inl hw))
                      | inr hw =>
                        have heqw : w = wp := List.mem_singleton.mp hw
                        rw [heqw]
                        exact hclean wp (List.mem_append.mpr (.inr
                          (List.mem_singleton.mpr rfl)))
                    have hdead' : ∀ (a2 : Addr) (t2 : Nat) (blk : List (BitVec 32)), (a2, t2, blk) ∈
                        dropped ++ [(a, t', [v, linkWord nxt])] → ∃ n,
                        blk = [v, linkWord n] ∧
                        memFind m3 a2 = some ⟨t2, false, blk⟩ := by
                      intro a2 t2 blk hmem2
                      rw [List.mem_append] at hmem2
                      cases hmem2 with
                      | inl hmem2 =>
                        obtain ⟨n2, hblk, hfind⟩ := hdead _ _ _ hmem2
                        have hne2a : a2 ≠ p := by
                          intro hcon
                          rw [hcon, hfindP'] at hfind
                          simp only [Option.some.injEq, Block.mk.injEq] at hfind
                          obtain ⟨_, hcontra, _⟩ := hfind
                          cases hcontra
                        have hne2b : a2 ≠ a := by
                          intro hcon
                          rw [hcon, hfb] at hfind
                          simp only [Option.some.injEq, Block.mk.injEq] at hfind
                          obtain ⟨_, hcontra, _⟩ := hfind
                          cases hcontra
                        have hfind2 : memFind m2' a2 =
                            some ⟨t2, false, blk⟩ := by
                          rw [memFind_memStore_other _ _ _ _ _ _ _ hFS hne2a]
                          exact hfind
                        refine ⟨n2, hblk, ?_⟩
                        rw [memFind_memFree_other _ _ _ _ _ hFR2 hne2b]
                        exact hfind2
                      | inr hmem2 =>
                        simp only [List.mem_singleton] at hmem2
                        obtain ⟨rfl, rfl, rfl⟩ := hmem2
                        exact ⟨nxt, rfl,
                          memFind_memFree_dead hvic2 hFR2⟩
                    have hex3 : ∀ x, (memFind m3 x).isSome = true →
                        x + 1 < 2 ^ 32 := by
                      intro x hx
                      by_cases heqx : x = a
                      · rw [heqx]
                        exact hex a (by rw [hfb]; rfl)
                      · rw [memFind_memFree_other _ _ _ _ _ hFR2 heqx] at hx
                        exact hex2 x hx
                    have hkeptEq : preVals (init ++ [(p, tp, wp)]) =
                        preVals kept := by
                      rw [hsplitEq]
                    have hIH := ih m3 hex3 (init ++ [(p, tp, wp)]) head
                      (some p) nxt v vs'
                      (dropped ++ [(a, t', [v, linkWord nxt])])
                      hchain' hsuf3 hprevnil' hprevlast' hplink'
                      hclean' hdead' hlen' m' hd' droppedOut hsw
                    obtain ⟨kept₁, hch1, hbridge, hdead1⟩ := hIH
                    refine ⟨kept₁, hch1, ?_, hdead1⟩
                    have hflt : (v :: vs').filter (· != v) =
                        vs'.filter (· != v) := by simp
                    rw [hflt, ← hkeptEq]
                    exact hbridge
        · -- Keep leg: payload differs, snoc the visited node.
          have hnev : v₀ ≠ v := fun heq => heq2 (by rw [heq]; simp)
          have hT : (v₀ != v) = true := bne_iff_ne.mpr hnev
          unfold listFilterSweep at hsw
          simp only [hfb, hmem0, hmem1, ite_eq_right heq2] at hsw
          rw [hdec] at hsw
          have hchain' : PrefixChain m head
              (kept ++ [(a, t', v₀)]) nxt :=
            PrefixChain.snoc_extend hchain hnode rfl rfl
          have hprevnil' : (some a : Option Addr) = none →
              kept ++ [(a, t', v₀)] = [] := by
            intro h
            cases h
          have hprevlast' : ∀ q, (some a : Option Addr) = some q →
              ∃ init lt lw,
                kept ++ [(a, t', v₀)] = init ++ [(q, lt, lw)] := by
            intro q hq
            cases hq
            exact ⟨kept, t', v₀, rfl⟩
          have hplink' : ∀ q, (some a : Option Addr) = some q →
              ∃ tq wq, nodeAt m q tq wq nxt := by
            intro q hq
            cases hq
            exact ⟨t', v₀, hnode⟩
          have hclean' : ∀ w ∈ preVals (kept ++ [(a, t', v₀)]), w ≠ v := by
            intro w hw
            simp only [preVals, List.map_append,
              List.mem_append] at hw
            cases hw with
            | inl hw => exact hclean w hw
            | inr hw =>
              rw [List.mem_singleton.mp hw]
              exact hnev
          have hIH := ih m hex (kept ++ [(a, t', v₀)]) head (some a)
            nxt v vs' dropped hchain' t2 hprevnil' hprevlast'
            hplink' hclean' hdead hlen' m' hd' droppedOut hsw
          obtain ⟨kept₁, hch1, hbridge, hdead1⟩ := hIH
          refine ⟨kept₁, hch1, ?_, hdead1⟩
          have hflt : (v₀ :: vs').filter (· != v) =
              v₀ :: vs'.filter (· != v) := by simp [hT]
          have happ : preVals (kept ++ [(a, t', v₀)]) =
              preVals kept ++ [v₀] := by simp [preVals]
          rw [happ] at hbridge
          rw [show (preVals kept ++ (v₀ :: vs').filter (· != v)) =
              (preVals kept ++ [v₀]) ++ vs'.filter (· != v) from by
            rw [hflt]; simp [List.append_assoc]]
          exact hbridge

/-- The entry mirror returns the filtered chain: every kept
    payload differs from `v`, every dropped cell is dead with a
    `v`-payload block (live flag cleared — contents kept but
    unusable, so any later dereference misses loudly). -/
theorem listFilterFwd_correct (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) (vs : List (BitVec 32))
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hseg : ListSeg m head vs) (hlen : vs.length ≤ F)
    (m' : Mem) (hd' : Option Addr)
    (hfwd : listFilterFwd F m head v = .ok (m', hd')) :
    ∃ dropped' : List (Addr × Nat × List (BitVec 32)),
      (∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ dropped' →
        ∃ n, blk = [v, linkWord n] ∧
        memFind m' a = some ⟨t, false, blk⟩) ∧
      ListSeg m' hd' (vs.filter (· != v)) := by
  unfold listFilterFwd at hfwd
  cases hsw : listFilterSweep F m head none head v [] with
  | error e =>
    simp only [hsw] at hfwd
    cases hfwd
  | ok res =>
    obtain ⟨m'', hd'', dropped'⟩ := res
    simp only [hsw] at hfwd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨e1, e2⟩ := hfwd
    subst m''; subst hd''
    have hchain : PrefixChain m head [] head := PrefixChain.nil
    have hIH := listFilterSweep_invariant F m hex [] head none head v
      vs [] hchain hseg (fun _ => rfl)
      (fun p hp => by cases hp) (fun p hp => by cases hp)
      (by simp [preVals])
      (fun (a : Addr) (t : Nat) (blk : List (BitVec 32))
        (h : (a, t, blk) ∈ ([] : List (Addr × Nat × List (BitVec 32)))) =>
        by cases (List.not_mem_nil h))
      hlen m' hd' dropped' hsw
    obtain ⟨kept₁, hch1, hbridge, hdead1⟩ := hIH
    have hbridge' : vs.filter (· != v) = preVals kept₁ := by
      simpa [preVals] using hbridge
    refine ⟨dropped', hdead1, ?_⟩
    have hlist := PrefixChain.appendSeg hch1 ListSeg.nil
    simp only [List.append_nil] at hlist
    rw [hbridge']
    exact hlist

/-! ## Loop/evaluator agreement -/

/-- Loop/evaluator agreement: when the sweep succeeds, the chase
    loop evaluates to `fellThrough` with the swept head and memory
    (final cursors: `cur = none`, `prev`/`next` existentially
    bound). Induction on fuel; the loop-exit leg evaluates the
    false guard, and each visit steps the evaluator through the
    body (save the link spare, swing the predecessor or the head,
    free, advance) before applying the IH with the transported
    prefix/suffix/dead facts. -/
theorem listFilterLoop_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (head : Option Addr) (v : BitVec 32)
      (prev cur : Option Addr)
      (kept : List (Addr × Nat × BitVec 32))
      (hchain : PrefixChain m head kept cur)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hprevnil : prev = none → kept = [])
      (hprevlast : ∀ p, prev = some p →
        ∃ init lt lw, kept = init ++ [(p, lt, lw)])
      (hplink : ∀ p, prev = some p → ∃ tp wp, nodeAt m p tp wp cur)
      (hclean : ∀ w ∈ preVals kept, w ≠ v)
      (dropped : List (Addr × Nat × List (BitVec 32)))
      (hdead : ∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ dropped →
        ∃ n, blk = [v, linkWord n] ∧
        memFind m a = some ⟨t, false, blk⟩)
      (nxt₀ : Option Addr)
      (hlen : suf.length ≤ F)
      (m' : Mem) (hd' : Option Addr)
      (droppedOut : List (Addr × Nat × List (BitVec 32)))
      (hC : listFilterSweep F m head prev cur v dropped =
        .ok (m', hd', droppedOut)),
    ∃ prev' nxt',
      memEvalStmtFuel F listFilterLoop
        (mkListFilterEnv head v prev cur nxt₀) m π =
        .ok ((mkListFilterEnv hd' v prev' none nxt', m', π), .fellThrough) := by
  induction F with
  | zero =>
    intro m π hex head v prev cur kept hchain suf hseg
      hprevnil hprevlast hplink hclean dropped hdead nxt₀ hlen
      m' hd' droppedOut hC
    cases cur with
    | none =>
      have hC' : listFilterSweep 0 m head prev none v dropped =
          .ok (m, head, dropped) := by
        simp [listFilterSweep]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      obtain ⟨e1, e2, e3⟩ := hC
      subst m'; subst hd'; subst droppedOut
      refine ⟨prev, nxt₀, ?_⟩
      have hcurE : memEvalExpr (.var "cur")
          (mkListFilterEnv head v prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListFilterEnv_cur head v prev none nxt₀)
      have hnullE : memEvalExpr (.lit .nullptr)
          (mkListFilterEnv head v prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListFilterEnv head v prev none nxt₀) m π = .ok (.b false) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcurE hnullE
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
      have hloop : listFilterLoop =
          (.while_ (.une (.var "cur") (.lit .nullptr))
            listFilterLoopBody) := rfl
      rw [hloop]
      exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
    | some a =>
      unfold listFilterSweep at hC
      simp only at hC
      cases hC
  | succ F ih =>
    intro m π hex head v prev cur kept hchain suf hseg
      hprevnil hprevlast hplink hclean dropped hdead nxt₀ hlen
      m' hd' droppedOut hC
    cases cur with
    | none =>
      have hC' : listFilterSweep (F + 1) m head prev none v dropped =
          .ok (m, head, dropped) := by
        simp [listFilterSweep]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      obtain ⟨e1, e2, e3⟩ := hC
      subst m'; subst hd'; subst droppedOut
      refine ⟨prev, nxt₀, ?_⟩
      have hcurE : memEvalExpr (.var "cur")
          (mkListFilterEnv head v prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListFilterEnv_cur head v prev none nxt₀)
      have hnullE : memEvalExpr (.lit .nullptr)
          (mkListFilterEnv head v prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListFilterEnv head v prev none nxt₀) m π = .ok (.b false) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcurE hnullE
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
      have hloop : listFilterLoop =
          (.while_ (.une (.var "cur") (.lit .nullptr))
            listFilterLoopBody) := rfl
      rw [hloop]
      exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
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
        have hmem1w : memLoad m a t' 1 = .ok (linkWord nxt) :=
          nodeLoadNext hnode
        have halloc : ∀ c', nxt = some c' →
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
        have hcurE : memEvalExpr (.var "cur")
            (mkListFilterEnv head v prev (some a) nxt₀) m π =
            .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListFilterEnv_cur head v prev (some a) nxt₀)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkListFilterEnv head v prev (some a) nxt₀) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListFilterEnv head v prev (some a) nxt₀) m π =
            .ok (.b true) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
            hcurE hnullE
          have hbe : (((some a) : Option Addr) != none) = true := by simp
          rw [hbe] at hg
          exact hg
        have hpget : memEvalExpr (.pgetVal (.var "cur"))
            (mkListFilterEnv head v prev (some a) nxt₀) m π =
            .ok (.i32 v₀) :=
          memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE hfb hmem0
        have hvalE : memEvalExpr (.var "val")
            (mkListFilterEnv head v prev (some a) nxt₀) m π =
            .ok (.i32 v) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListFilterEnv_val head v prev (some a) nxt₀)
        have hueq : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
            (mkListFilterEnv head v prev (some a) nxt₀) m π =
            .ok (.b (v₀ == v)) := by
          unfold memEvalExpr
          simp only [hpget, hvalE]
        have hpgn : memEvalExpr (.pgetNext (.var "cur"))
            (mkListFilterEnv head v prev (some a) nxt₀) m π =
            .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
          memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE hfb hmem1w
        have hloop : listFilterLoop =
            (.while_ (.une (.var "cur") (.lit .nullptr))
              listFilterLoopBody) := rfl
        have hbody : listFilterLoopBody =
            (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
              (.seq (.assign "next" (.pgetNext (.var "cur")))
                (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                        (.assign "head" (.var "next"))
                        (.psetNext (.var "prev") (.var "next")))
                  (.seq (.nfree (.var "cur"))
                    (.assign "cur" (.var "next")))))
              (.seq (.assign "prev" (.var "cur"))
                (.assign "cur" (.pgetNext (.var "cur"))))) := rfl
        by_cases heq2 : (v₀ == v) = true
        · -- Drop leg: the payload matches, unlink + free + advance.
          have hvv : v₀ = v := beq_iff_eq.mp heq2
          subst v₀
          unfold listFilterSweep at hC
          simp only [hfb, hmem0, hmem1w, ite_eq_left heq2] at hC
          have hueqT : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
              (mkListFilterEnv head v prev (some a) nxt₀) m π =
              .ok (.b true) := by
            rw [heq2] at hueq
            exact hueq
          cases prev with
          | none =>
            obtain hkept0 : kept = [] := hprevnil rfl
            cases hFR : memFree m a t' with
            | error e =>
              simp only [hFR] at hC
              cases hC
            | ok m1 =>
              simp only [hFR] at hC
              have hassN := memEvalStmtFuel_assign_mem F "next"
                (.pgetNext (.var "cur"))
                (mkListFilterEnv head v none (some a) nxt₀) m π
                (.ptrVal (addrOfWord (linkWord nxt)))
                (mkListFilterEnv head v none (some a)
                  (addrOfWord (linkWord nxt))) hpgn
                (by simp [mkListFilterEnv, envUpdate])
              have hprevE : memEvalExpr (.var "prev")
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π =
                  .ok (.ptrVal none) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListFilterEnv_prev head v none (some a)
                    (addrOfWord (linkWord nxt)))
              have hnullE1 : memEvalExpr (.lit .nullptr)
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π =
                  .ok (.ptrVal none) := by
                simp [memEvalExpr, litVal]
              have hinnerT : memEvalExpr
                  (.ueq (.var "prev") (.lit .nullptr))
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π = .ok (.b true) := by
                have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _ none none
                  hprevE hnullE1
                have hbe : ((none : Option Addr) == none) = true := by simp
                rw [hbe] at hg
                exact hg
              have hnext : memEvalExpr (.var "next")
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π =
                  .ok (.ptrVal (addrOfWord (linkWord nxt))) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListFilterEnv_next head v none (some a)
                    (addrOfWord (linkWord nxt)))
              have hassH := memEvalStmtFuel_assign_mem F "head"
                (.var "next")
                (mkListFilterEnv head v none (some a)
                  (addrOfWord (linkWord nxt))) m π
                (.ptrVal (addrOfWord (linkWord nxt)))
                (mkListFilterEnv (addrOfWord (linkWord nxt)) v none (some a)
                  (addrOfWord (linkWord nxt))) hnext
                (by simp [mkListFilterEnv, envUpdate])
              have hcurE2 : memEvalExpr (.var "cur")
                  (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt))) m π =
                  .ok (.ptrVal (some a)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListFilterEnv_cur (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt)))
              have hfindC : memFind m a =
                  some ⟨t', true, [v, linkWord nxt]⟩ := hnode
              have hnfree := memEvalStmtFuel_nfree_ok F (.var "cur")
                (mkListFilterEnv (addrOfWord (linkWord nxt)) v none (some a)
                  (addrOfWord (linkWord nxt))) m π a _ m1
                hcurE2 hfindC hFR
              have hnext2 : memEvalExpr (.var "next")
                  (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt))) m1 π =
                  .ok (.ptrVal (addrOfWord (linkWord nxt))) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListFilterEnv_next (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt)))
              have hassC := memEvalStmtFuel_assign_mem F "cur"
                (.var "next")
                (mkListFilterEnv (addrOfWord (linkWord nxt)) v none (some a)
                  (addrOfWord (linkWord nxt))) m1 π
                (.ptrVal (addrOfWord (linkWord nxt)))
                (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                  (addrOfWord (linkWord nxt))
                  (addrOfWord (linkWord nxt))) hnext2
                (by simp [mkListFilterEnv, envUpdate])
              have hifInner : memEvalStmtFuel F
                  (.if_ (.ueq (.var "prev") (.lit .nullptr))
                    (.assign "head" (.var "next"))
                    (.psetNext (.var "prev") (.var "next")))
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π =
                  .ok (((mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt)), m, π)),
                    .fellThrough) :=
                (memEvalStmtFuel_if_true F _ _ _ _ _ _ hinnerT).trans hassH
              have hseqNC : memEvalStmtFuel F
                  (.seq (.nfree (.var "cur"))
                    (.assign "cur" (.var "next")))
                  (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt))) m π =
                  .ok (((mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (addrOfWord (linkWord nxt))
                    (addrOfWord (linkWord nxt)), m1, π)),
                    .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _
                  (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt))) m π
                  (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt))) m1 π _
                  hnfree hassC
              have hrest : memEvalStmtFuel F
                  (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                          (.assign "head" (.var "next"))
                          (.psetNext (.var "prev") (.var "next")))
                    (.seq (.nfree (.var "cur"))
                      (.assign "cur" (.var "next"))))
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π =
                  .ok (((mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (addrOfWord (linkWord nxt))
                    (addrOfWord (linkWord nxt)), m1, π)),
                    .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π
                  (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (some a) (addrOfWord (linkWord nxt))) m π _
                  hifInner hseqNC
              have hthen : memEvalStmtFuel F
                  (.seq (.assign "next" (.pgetNext (.var "cur")))
                    (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                            (.assign "head" (.var "next"))
                            (.psetNext (.var "prev") (.var "next")))
                      (.seq (.nfree (.var "cur"))
                        (.assign "cur" (.var "next")))))
                  (mkListFilterEnv head v none (some a) nxt₀) m π =
                  .ok (((mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (addrOfWord (linkWord nxt))
                    (addrOfWord (linkWord nxt)), m1, π)),
                    .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F _ _
                  (mkListFilterEnv head v none (some a) nxt₀) m π
                  (mkListFilterEnv head v none (some a)
                    (addrOfWord (linkWord nxt))) m π _
                  hassN hrest
              have hbodyEv : memEvalStmtFuel F listFilterLoopBody
                  (mkListFilterEnv head v none (some a) nxt₀) m π =
                  .ok (((mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                    (addrOfWord (linkWord nxt))
                    (addrOfWord (linkWord nxt)), m1, π)),
                    .fellThrough) := by
                rw [hbody]
                exact (memEvalStmtFuel_if_true F _ _ _ _ _ _
                  hueqT).trans hthen
              have hWT : memEvalStmtFuel (F + 1) listFilterLoop
                  (mkListFilterEnv head v none (some a) nxt₀) m π =
                  memEvalStmtFuel F listFilterLoop
                    (mkListFilterEnv (addrOfWord (linkWord nxt)) v none
                      (addrOfWord (linkWord nxt))
                      (addrOfWord (linkWord nxt))) m1 π := by
                rw [hloop]
                have h := memEvalStmtFuel_while_true F _
                  listFilterLoopBody _ _ _ hgT
                simp only [hbodyEv] at h
                exact h
              have hchain' : PrefixChain m1 (addrOfWord (linkWord nxt))
                  kept (addrOfWord (linkWord nxt)) := by
                rw [hdec, hkept0]
                exact PrefixChain.nil
              have hsuf3 : ListSeg m1 (addrOfWord (linkWord nxt)) vs' := by
                rw [hdec]
                exact t2.free_other hFR (fun b hmemB =>
                  ListSeg_head_notin_tail hnode t2 hex b hmemB)
              have hdead' : ∀ (a2 : Addr) (t2 : Nat) (blk : List (BitVec 32)),
                  (a2, t2, blk) ∈
                    dropped ++ [(a, t', [v, linkWord nxt])] → ∃ n,
                  blk = [v, linkWord n] ∧
                  memFind m1 a2 = some ⟨t2, false, blk⟩ := by
                intro a2 t2 blk hmem2
                rw [List.mem_append] at hmem2
                cases hmem2 with
                | inl hmem2 =>
                  obtain ⟨n2, hblk, hfind⟩ := hdead _ _ _ hmem2
                  have hne2 : a2 ≠ a := by
                    intro hcon
                    rw [hcon, hfb] at hfind
                    simp only [Option.some.injEq, Block.mk.injEq] at hfind
                    obtain ⟨_, hcontra, _⟩ := hfind
                    cases hcontra
                  refine ⟨n2, hblk, ?_⟩
                  rw [memFind_memFree_other _ _ _ _ _ hFR hne2]
                  exact hfind
                | inr hmem2 =>
                  simp only [List.mem_singleton] at hmem2
                  obtain ⟨rfl, rfl, rfl⟩ := hmem2
                  exact ⟨nxt, rfl,
                    memFind_memFree_dead hnode hFR⟩
              have hex1 : ∀ x, (memFind m1 x).isSome = true →
                  x + 1 < 2 ^ 32 := by
                intro x hx
                by_cases heqx : x = a
                · rw [heqx]
                  exact hex a (by rw [hfb]; rfl)
                · rw [memFind_memFree_other _ _ _ _ _ hFR heqx] at hx
                  exact hex x hx
              have hIH := ih m1 π hex1 (addrOfWord (linkWord nxt)) v none
                (addrOfWord (linkWord nxt)) kept hchain'
                vs' hsuf3 (fun _ => hkept0)
                (by intro p hp; cases hp) (by intro p hp; cases hp)
                hclean (dropped ++ [(a, t', [v, linkWord nxt])])
                hdead' (addrOfWord (linkWord nxt)) hlen'
                m' hd' droppedOut hC
              obtain ⟨prev', nxt', hIH'⟩ := hIH
              refine ⟨prev', nxt', ?_⟩
              rw [hWT]
              exact hIH'
          | some p =>
            obtain ⟨tp, wp, hnp⟩ := hplink p rfl
            cases hFp : memFind m p with
            | none =>
              simp only [hFp] at hC
              cases hC
            | some bp =>
              simp only [hFp] at hC
              have hfindP : memFind m p = some _ := hnp
              rw [hfindP] at hFp
              cases hFp
              cases hFS : memStore m p tp 1 (linkWord nxt) with
              | error e =>
                simp only [hFS] at hC
                cases hC
              | ok m2' =>
                simp only [hFS] at hC
                cases hFR2 : memFree m2' a t' with
                | error e =>
                  simp only [hFR2] at hC
                  cases hC
                | ok m3 =>
                  simp only [hFR2] at hC
                  have hassN := memEvalStmtFuel_assign_mem F "next"
                    (.pgetNext (.var "cur"))
                    (mkListFilterEnv head v (some p) (some a) nxt₀) m π
                    (.ptrVal (addrOfWord (linkWord nxt)))
                    (mkListFilterEnv head v (some p) (some a)
                      (addrOfWord (linkWord nxt))) hpgn
                    (by simp [mkListFilterEnv, envUpdate])
                  have hprevE : memEvalExpr (.var "prev")
                      (mkListFilterEnv head v (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π =
                      .ok (.ptrVal (some p)) := by
                    rw [memEvalExpr_var]
                    exact evalExpr_var_hit _ _ _
                      (mkListFilterEnv_prev head v (some p) (some a)
                        (addrOfWord (linkWord nxt)))
                  have hnullE1 : memEvalExpr (.lit .nullptr)
                      (mkListFilterEnv head v (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π =
                      .ok (.ptrVal none) := by
                    simp [memEvalExpr, litVal]
                  have hinnerF : memEvalExpr
                      (.ueq (.var "prev") (.lit .nullptr))
                      (mkListFilterEnv head v (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π =
                      .ok (.b false) := by
                    have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _ (some p)
                      none hprevE hnullE1
                    have hbe : (((some p) : Option Addr) == none) =
                        false := by simp
                    rw [hbe] at hg
                    exact hg
                  have hlinkE : memEvalExpr (.var "next")
                      (mkListFilterEnv head v (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π =
                      .ok (.ptrVal (addrOfWord (linkWord nxt))) := by
                    rw [memEvalExpr_var]
                    exact evalExpr_var_hit _ _ _
                      (mkListFilterEnv_next head v (some p) (some a)
                        (addrOfWord (linkWord nxt)))
                  have hstoreW : memStore m p tp 1
                      (linkWord (addrOfWord (linkWord nxt))) = .ok m2' := by
                    have hw : linkWord (addrOfWord (linkWord nxt)) =
                        linkWord nxt := congrArg linkWord hdec
                    rw [hw]
                    exact hFS
                  have hfindP' : memFind m p = some _ := hnp
                  have hsetNext := memEvalStmtFuel_psetNext_ok F
                    (.var "prev") (.var "next")
                    (mkListFilterEnv head v (some p) (some a)
                      (addrOfWord (linkWord nxt))) m π p
                    (addrOfWord (linkWord nxt)) _ m2'
                    hprevE hlinkE hfindP hstoreW
                  obtain ⟨init, lt, lw, hsplitEq⟩ := hprevlast p rfl
                  rw [hsplitEq] at hchain
                  obtain ⟨midp, hinit, hplast⟩ := PrefixChain.split hchain
                  cases hplast with
                  | cons hnodeP' hrestP =>
                    cases hrestP
                    have hfindP2 : memFind m p = some _ := hnodeP'
                    rw [hfindP2] at hfindP
                    cases hfindP
                    have hpNew2 : nodeAt m2' p tp wp nxt :=
                      nodeStoreNext_nodeAt hnp hFS
                    have hnePC : p ≠ a := by
                      intro hcon
                      have hnpC : nodeAt m a tp wp (some a) := hcon ▸ hnp
                      have hmemC : SegMem (m := m) (some a) a :=
                        SegMem.here hnode
                      have htailP : ListSeg m (some a) (v :: vs') :=
                        ListSeg.cons hnode t2
                      have hcontra :=
                        ListSeg_head_notin_tail hnpC htailP hex a hmemC
                      exact hcontra rfl
                    have hneCP : a ≠ p := Ne.symm hnePC
                    have hvic2 : nodeAt m2' a t' v nxt :=
                      nodeAt_store_other_fwd hnode hFS hneCP
                    have hliveP : (memFind m p).isSome = true := by
                      have h := congrArg Option.isSome hfindP'
                      simpa using h
                    have hex2 : ∀ x, (memFind m2' x).isSome = true →
                        x + 1 < 2 ^ 32 :=
                      hex_store hex hFS hliveP
                    have hout_p : ∀ b, SegMem (m := m) nxt b → b ≠ p := by
                      intro b hmemB
                      have hmemC : SegMem (m := m) (some a) b :=
                        hmemB.victimCons hnode
                      have htailP : ListSeg m (some a) (v :: vs') :=
                        ListSeg.cons hnode t2
                      exact ListSeg_head_notin_tail hnp htailP hex b hmemC
                    have hsuf2 : ListSeg m2' nxt vs' :=
                      t2.store_other hFS hout_p
                    have hcurE1 : memEvalExpr (.var "cur")
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m2' π =
                        .ok (.ptrVal (some a)) := by
                      rw [memEvalExpr_var]
                      exact evalExpr_var_hit _ _ _
                        (mkListFilterEnv_cur head v (some p) (some a)
                          (addrOfWord (linkWord nxt)))
                    have hfindM1 : memFind m2' a =
                        some ⟨t', true, [v, linkWord nxt]⟩ := by
                      have h := memFind_memStore_other m m2' p a tp 1
                        (linkWord nxt) hFS hneCP
                      rw [hfb] at h
                      exact h
                    have hnfree2 := memEvalStmtFuel_nfree_ok F (.var "cur")
                      (mkListFilterEnv head v (some p) (some a)
                        (addrOfWord (linkWord nxt))) m2' π a _ m3
                      hcurE1 hfindM1 hFR2
                    have hnext2 : memEvalExpr (.var "next")
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m3 π =
                        .ok (.ptrVal (addrOfWord (linkWord nxt))) := by
                      rw [memEvalExpr_var]
                      exact evalExpr_var_hit _ _ _
                        (mkListFilterEnv_next head v (some p) (some a)
                          (addrOfWord (linkWord nxt)))
                    have hassC := memEvalStmtFuel_assign_mem F "cur"
                      (.var "next")
                      (mkListFilterEnv head v (some p) (some a)
                        (addrOfWord (linkWord nxt))) m3 π
                      (.ptrVal (addrOfWord (linkWord nxt)))
                      (mkListFilterEnv head v (some p)
                        (addrOfWord (linkWord nxt))
                        (addrOfWord (linkWord nxt))) hnext2
                      (by simp [mkListFilterEnv, envUpdate])
                    have hout_c : ∀ b, SegMem (m := m2') nxt b → b ≠ a := by
                      intro b hmemB
                      exact ListSeg_head_notin_tail hvic2 hsuf2 hex2 b hmemB
                    have hsuf3 : ListSeg m3
                        (addrOfWord (linkWord nxt)) vs' := by
                      rw [hdec]
                      exact hsuf2.free_other hFR2 hout_c
                    have hpreT : PrefixChain m3 head init (some p) :=
                      hinit.transport_erase hnp hnode t2 rfl hex hFS hFR2
                    have hpNew3 : nodeAt m3 p tp wp nxt :=
                      nodeAt_free_other hpNew2 hFR2 hnePC
                    have hchain' : PrefixChain m3 head
                        (init ++ [(p, tp, wp)])
                        (addrOfWord (linkWord nxt)) := by
                      rw [hdec]
                      exact PrefixChain.snoc_extend hpreT hpNew3 rfl rfl
                    have hprevnil' : (some p : Option Addr) = none →
                        init ++ [(p, tp, wp)] = [] := by
                      intro h
                      cases h
                    have hprevlast' : ∀ q, (some p : Option Addr) = some q →
                        ∃ init' lt' lw',
                          init ++ [(p, tp, wp)] =
                            init' ++ [(q, lt', lw')] := by
                      intro q hq
                      cases hq
                      exact ⟨init, tp, wp, rfl⟩
                    have hplink' : ∀ q, (some p : Option Addr) = some q →
                        ∃ tq wq, nodeAt m3 q tq wq
                          (addrOfWord (linkWord nxt)) := by
                      intro q hq
                      cases hq
                      rw [hdec]
                      exact ⟨tp, wp, hpNew3⟩
                    have happInit : preVals (init ++ [(p, tp, wp)]) =
                        preVals init ++ [wp] := by simp [preVals]
                    have hclean' : ∀ w ∈
                        preVals (init ++ [(p, tp, wp)]), w ≠ v := by
                      intro w hw
                      rw [hsplitEq] at hclean
                      rw [happInit] at hclean hw
                      cases (List.mem_append.mp hw) with
                      | inl hw =>
                        exact hclean w (List.mem_append.mpr (.inl hw))
                      | inr hw =>
                        have heqw : w = wp := List.mem_singleton.mp hw
                        rw [heqw]
                        exact hclean wp (List.mem_append.mpr (.inr
                          (List.mem_singleton.mpr rfl)))
                    have hdead' : ∀ (a2 : Addr) (t2 : Nat)
                        (blk : List (BitVec 32)), (a2, t2, blk) ∈
                        dropped ++ [(a, t', [v, linkWord nxt])] → ∃ n,
                        blk = [v, linkWord n] ∧
                        memFind m3 a2 = some ⟨t2, false, blk⟩ := by
                      intro a2 t2 blk hmem2
                      rw [List.mem_append] at hmem2
                      cases hmem2 with
                      | inl hmem2 =>
                        obtain ⟨n2, hblk, hfind⟩ := hdead _ _ _ hmem2
                        have hne2a : a2 ≠ p := by
                          intro hcon
                          rw [hcon, hfindP'] at hfind
                          simp only [Option.some.injEq,
                            Block.mk.injEq] at hfind
                          obtain ⟨_, hcontra, _⟩ := hfind
                          cases hcontra
                        have hne2b : a2 ≠ a := by
                          intro hcon
                          rw [hcon, hfb] at hfind
                          simp only [Option.some.injEq,
                            Block.mk.injEq] at hfind
                          obtain ⟨_, hcontra, _⟩ := hfind
                          cases hcontra
                        have hfind2 : memFind m2' a2 =
                            some ⟨t2, false, blk⟩ := by
                          rw [memFind_memStore_other _ _ _ _ _ _ _ hFS
                            hne2a]
                          exact hfind
                        refine ⟨n2, hblk, ?_⟩
                        rw [memFind_memFree_other _ _ _ _ _ hFR2 hne2b]
                        exact hfind2
                      | inr hmem2 =>
                        simp only [List.mem_singleton] at hmem2
                        obtain ⟨rfl, rfl, rfl⟩ := hmem2
                        exact ⟨nxt, rfl,
                          memFind_memFree_dead hvic2 hFR2⟩
                    have hex3 : ∀ x, (memFind m3 x).isSome = true →
                        x + 1 < 2 ^ 32 := by
                      intro x hx
                      by_cases heqx : x = a
                      · rw [heqx]
                        exact hex a (by rw [hfb]; rfl)
                      · rw [memFind_memFree_other _ _ _ _ _ hFR2 heqx] at hx
                        exact hex2 x hx
                    have hifInner : memEvalStmtFuel F
                        (.if_ (.ueq (.var "prev") (.lit .nullptr))
                          (.assign "head" (.var "next"))
                          (.psetNext (.var "prev") (.var "next")))
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m π =
                        .ok (((mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt)), m2', π)),
                          .fellThrough) :=
                      (memEvalStmtFuel_if_false F _ _ _ _ _ _
                        hinnerF).trans hsetNext
                    have hseqNC : memEvalStmtFuel F
                        (.seq (.nfree (.var "cur"))
                          (.assign "cur" (.var "next")))
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m2' π =
                        .ok (((mkListFilterEnv head v (some p)
                          (addrOfWord (linkWord nxt))
                          (addrOfWord (linkWord nxt)), m3, π)),
                          .fellThrough) :=
                      memEvalStmtFuel_seq_fallthrough_trans F _ _
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m2' π
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m3 π _
                        hnfree2 hassC
                    have hrest : memEvalStmtFuel F
                        (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                                (.assign "head" (.var "next"))
                                (.psetNext (.var "prev") (.var "next")))
                          (.seq (.nfree (.var "cur"))
                            (.assign "cur" (.var "next"))))
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m π =
                        .ok (((mkListFilterEnv head v (some p)
                          (addrOfWord (linkWord nxt))
                          (addrOfWord (linkWord nxt)), m3, π)),
                          .fellThrough) :=
                      memEvalStmtFuel_seq_fallthrough_trans F _ _
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m π
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m2' π _
                        hifInner hseqNC
                    have hthen : memEvalStmtFuel F
                        (.seq (.assign "next" (.pgetNext (.var "cur")))
                          (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                                  (.assign "head" (.var "next"))
                                  (.psetNext (.var "prev") (.var "next")))
                            (.seq (.nfree (.var "cur"))
                              (.assign "cur" (.var "next")))))
                        (mkListFilterEnv head v (some p) (some a)
                          nxt₀) m π =
                        .ok (((mkListFilterEnv head v (some p)
                          (addrOfWord (linkWord nxt))
                          (addrOfWord (linkWord nxt)), m3, π)),
                          .fellThrough) :=
                      memEvalStmtFuel_seq_fallthrough_trans F _ _
                        (mkListFilterEnv head v (some p) (some a) nxt₀) m π
                        (mkListFilterEnv head v (some p) (some a)
                          (addrOfWord (linkWord nxt))) m π _
                        hassN hrest
                    have hbodyEv : memEvalStmtFuel F listFilterLoopBody
                        (mkListFilterEnv head v (some p) (some a) nxt₀) m π =
                        .ok (((mkListFilterEnv head v (some p)
                          (addrOfWord (linkWord nxt))
                          (addrOfWord (linkWord nxt)), m3, π)),
                          .fellThrough) := by
                      rw [hbody]
                      exact (memEvalStmtFuel_if_true F _ _ _ _ _ _
                        hueqT).trans hthen
                    have hWT : memEvalStmtFuel (F + 1) listFilterLoop
                        (mkListFilterEnv head v (some p) (some a) nxt₀) m π =
                        memEvalStmtFuel F listFilterLoop
                          (mkListFilterEnv head v (some p)
                            (addrOfWord (linkWord nxt))
                            (addrOfWord (linkWord nxt))) m3 π := by
                      rw [hloop]
                      have h := memEvalStmtFuel_while_true F _
                        listFilterLoopBody _ _ _ hgT
                      simp only [hbodyEv] at h
                      exact h
                    have hIH := ih m3 π hex3 head v (some p)
                      (addrOfWord (linkWord nxt))
                      (init ++ [(p, tp, wp)]) hchain' vs' hsuf3 hprevnil'
                      hprevlast' hplink' hclean'
                      (dropped ++ [(a, t', [v, linkWord nxt])])
                      hdead' (addrOfWord (linkWord nxt)) hlen'
                      m' hd' droppedOut hC
                    obtain ⟨prev', nxt', hIH'⟩ := hIH
                    refine ⟨prev', nxt', ?_⟩
                    rw [hWT]
                    exact hIH'
        · -- Keep leg: payload differs, snoc the visited node.
          have hnev : v₀ ≠ v := fun heq => heq2 (by rw [heq]; simp)
          unfold listFilterSweep at hC
          simp only [hfb, hmem0, hmem1w, ite_eq_right heq2] at hC
          have hueqF : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
              (mkListFilterEnv head v prev (some a) nxt₀) m π =
              .ok (.b false) := by
            have hbf : (v₀ == v) = false := by
              simp_all
            rw [hbf] at hueq
            exact hueq
          have hassP := memEvalStmtFuel_assign_mem F "prev" (.var "cur")
            (mkListFilterEnv head v prev (some a) nxt₀) m π
            (.ptrVal (some a))
            (mkListFilterEnv head v (some a) (some a) nxt₀) hcurE
            (by simp [mkListFilterEnv, envUpdate])
          have hcurE1 : memEvalExpr (.var "cur")
              (mkListFilterEnv head v (some a) (some a) nxt₀) m π =
              .ok (.ptrVal (some a)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListFilterEnv_cur head v (some a) (some a) nxt₀)
          have hpgn1 : memEvalExpr (.pgetNext (.var "cur"))
              (mkListFilterEnv head v (some a) (some a) nxt₀) m π =
              .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE1 hfb hmem1w
          have hassC := memEvalStmtFuel_assign_mem F "cur"
            (.pgetNext (.var "cur"))
            (mkListFilterEnv head v (some a) (some a) nxt₀) m π
            (.ptrVal (addrOfWord (linkWord nxt)))
            (mkListFilterEnv head v (some a)
              (addrOfWord (linkWord nxt)) nxt₀) hpgn1
            (by simp [mkListFilterEnv, envUpdate])
          have helse : memEvalStmtFuel F
              (.seq (.assign "prev" (.var "cur"))
                (.assign "cur" (.pgetNext (.var "cur"))))
              (mkListFilterEnv head v prev (some a) nxt₀) m π =
              .ok (((mkListFilterEnv head v (some a)
                (addrOfWord (linkWord nxt)) nxt₀, m, π)),
                .fellThrough) :=
            memEvalStmtFuel_seq_fallthrough_trans F
              (.assign "prev" (.var "cur"))
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkListFilterEnv head v prev (some a) nxt₀) m π
              (mkListFilterEnv head v (some a) (some a) nxt₀) m π _
              hassP hassC
          have hbodyEv : memEvalStmtFuel F listFilterLoopBody
              (mkListFilterEnv head v prev (some a) nxt₀) m π =
              .ok (((mkListFilterEnv head v (some a)
                (addrOfWord (linkWord nxt)) nxt₀, m, π)),
                .fellThrough) := by
            rw [hbody]
            exact (memEvalStmtFuel_if_false F _ _ _ _ _ _
              hueqF).trans helse
          have hWT : memEvalStmtFuel (F + 1) listFilterLoop
              (mkListFilterEnv head v prev (some a) nxt₀) m π =
              memEvalStmtFuel F listFilterLoop
                (mkListFilterEnv head v (some a)
                  (addrOfWord (linkWord nxt)) nxt₀) m π := by
            rw [hloop]
            have h := memEvalStmtFuel_while_true F _
              listFilterLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          have ht2' : ListSeg m (addrOfWord (linkWord nxt)) vs' := by
            rw [hdec]
            exact t2
          have hchain' : PrefixChain m head
              (kept ++ [(a, t', v₀)])
              (addrOfWord (linkWord nxt)) := by
            rw [hdec]
            exact PrefixChain.snoc_extend hchain hnode rfl rfl
          have hprevnil' : (some a : Option Addr) = none →
              kept ++ [(a, t', v₀)] = [] := by
            intro h
            cases h
          have hprevlast' : ∀ q, (some a : Option Addr) = some q →
              ∃ init lt lw,
                kept ++ [(a, t', v₀)] = init ++ [(q, lt, lw)] := by
            intro q hq
            cases hq
            exact ⟨kept, t', v₀, rfl⟩
          have hplink' : ∀ q, (some a : Option Addr) = some q →
              ∃ tq wq, nodeAt m q tq wq
                (addrOfWord (linkWord nxt)) := by
            intro q hq
            cases hq
            rw [hdec]
            exact ⟨t', v₀, hnode⟩
          have hclean' : ∀ w ∈ preVals (kept ++ [(a, t', v₀)]),
              w ≠ v := by
            intro w hw
            simp only [preVals, List.map_append,
              List.mem_append] at hw
            cases hw with
            | inl hw => exact hclean w hw
            | inr hw =>
              rw [List.mem_singleton.mp hw]
              exact hnev
          have hIH := ih m π hex head v (some a)
            (addrOfWord (linkWord nxt)) (kept ++ [(a, t', v₀)])
            hchain' vs' ht2' hprevnil' hprevlast' hplink' hclean'
            dropped hdead nxt₀ hlen' m' hd' droppedOut hC
          obtain ⟨prev', nxt', hIH'⟩ := hIH
          refine ⟨prev', nxt', ?_⟩
          rw [hWT]
          exact hIH'

/-- Entry correctness: evaluating `list_filter` on a `ListSeg`
    returns the swept head with the filtered survivors and every
    dropped victim cell dead. The three cursor lets build the
    sweep environment, the loop agreement runs the chase, and the
    return reads back the swept head. -/
theorem listFilterFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs) (hlen : vs.length ≤ F)
    (hfwd : listFilterFwd F m head v = .ok (m', hd')) :
    ∃ dropped' : List (Addr × Nat × List (BitVec 32)), ∃ ρ',
      memEvalStmtFuel F listFilterFunc.body
        [("head", .ptrVal head), ("val", .i32 v)] m π =
        .ok ((ρ', m', π), .returned (.ptrVal hd')) ∧
      ListSeg m' hd' (vs.filter (· != v)) ∧
      (∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ dropped' →
        ∃ n, blk = [v, linkWord n] ∧
        memFind m' a = some ⟨t, false, blk⟩) := by
  unfold listFilterFwd at hfwd
  cases hsw : listFilterSweep F m head none head v [] with
  | error e =>
    simp only [hsw] at hfwd
    cases hfwd
  | ok res =>
    obtain ⟨m'', hd'', dropped''⟩ := res
    simp only [hsw] at hfwd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨e1, e2⟩ := hfwd
    subst m''; subst hd''
    have hchain0 : PrefixChain m head [] head := PrefixChain.nil
    have hIH0 := listFilterSweep_invariant F m hex [] head none head v
      vs [] hchain0 hseg (fun _ => rfl)
      (fun p hp => by cases hp) (fun p hp => by cases hp)
      (by simp [preVals])
      (fun (a : Addr) (t : Nat) (blk : List (BitVec 32))
        (h : (a, t, blk) ∈ ([] : List (Addr × Nat × List (BitVec 32)))) =>
        by cases (List.not_mem_nil h))
      hlen m' hd' dropped'' hsw
    obtain ⟨kept₁, hch1, hbridge, hdead⟩ := hIH0
    have hbridge' : vs.filter (· != v) = preVals kept₁ := by
      simpa [preVals] using hbridge
    have hlist := PrefixChain.appendSeg hch1 ListSeg.nil
    simp only [List.append_nil] at hlist
    rw [← hbridge'] at hlist
    have hloop := listFilterLoop_agree F m π hex head v none head []
      hchain0 vs hseg (fun _ => rfl)
      (fun p hp => by cases hp) (fun p hp => by cases hp)
      (by simp [preVals]) []
      (fun (a : Addr) (t : Nat) (blk : List (BitVec 32))
        (h : (a, t, blk) ∈ ([] : List (Addr × Nat × List (BitVec 32)))) =>
        by cases (List.not_mem_nil h))
      none hlen m' hd' dropped'' hsw
    obtain ⟨prev', nxt', hloop'⟩ := hloop
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
    have eN : memEvalExpr (.lit .nullptr)
        ([("cur", .ptrVal head), ("prev", .ptrVal none),
          ("head", .ptrVal head), ("val", .i32 v)]) m π =
        evalExpr (.lit .nullptr)
          ([("cur", .ptrVal head), ("prev", .ptrVal none),
            ("head", .ptrVal head), ("val", .i32 v)]) :=
      memEvalExpr_lit _ _ _ _
    have vN : evalExpr (.lit .nullptr)
        ([("cur", .ptrVal head), ("prev", .ptrVal none),
          ("head", .ptrVal head), ("val", .i32 v)]) =
        .ok (.ptrVal none) := by simp [evalExpr, litVal]
    have hN := memEvalStmtFuel_let_pure F "next" nodeTy (.lit .nullptr)
      _ _ _ (.ptrVal none)
      (by simp) (by simp) (by simp) (by simp) eN vN
    have hretE : memEvalExpr (.var "head")
        (mkListFilterEnv hd' v prev' none nxt') m' π =
        evalExpr (.var "head")
          (mkListFilterEnv hd' v prev' none nxt') :=
      memEvalExpr_var _ _ _ _
    have hretV : evalExpr (.var "head")
        (mkListFilterEnv hd' v prev' none nxt') =
        .ok (.ptrVal hd') :=
      evalExpr_var_hit _ _ _ (mkListFilterEnv_head hd' v prev' none nxt')
    have hret := memEvalStmtFuel_return F (.var "head")
      (mkListFilterEnv hd' v prev' none nxt') m' π _ hretE hretV
    have hbody : listFilterFunc.body = listFilterBody := rfl
    rw [hbody]
    have hRest2 := memEvalStmtFuel_seq_fallthrough_trans F
      listFilterLoop (.return_ (.var "head"))
      (mkListFilterEnv head v none head none) m π
      (mkListFilterEnv hd' v prev' none nxt') m' π _
      hloop' hret
    have hRest1 := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "next" nodeTy (.lit .nullptr))
      (.seq listFilterLoop (.return_ (.var "head")))
      ([("cur", .ptrVal head), ("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) m π
      (mkListFilterEnv head v none head none) m π _
      hN hRest2
    have hRest0 := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "head"))
      (.seq (.let_ "next" nodeTy (.lit .nullptr))
        (.seq listFilterLoop (.return_ (.var "head"))))
      ([("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) m π
      ([("cur", .ptrVal head), ("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) m π _
      hB hRest1
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "prev" nodeTy (.lit .nullptr))
      (.seq (.let_ "cur" nodeTy (.var "head"))
        (.seq (.let_ "next" nodeTy (.lit .nullptr))
          (.seq listFilterLoop (.return_ (.var "head")))))
      ([("head", .ptrVal head), ("val", .i32 v)]) m π
      ([("prev", .ptrVal none),
        ("head", .ptrVal head), ("val", .i32 v)]) m π _
      hA hRest0
    exact ⟨dropped'', _, hTop, hlist, hdead⟩
