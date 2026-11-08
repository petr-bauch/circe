/-
Circe.Emit.ListUnique — pillar-1 adjacent-duplicate squeeze:
unlink every node equal to its predecessor and `free` it
(`list_unique`) over caller-owned `Node {val, next}`.

The corpus (`tests/cpp/list_unique.cpp`, entry
`Node *list_unique(Node *head)`) chases with a trailing
pointer and, for every node whose payload equals its
predecessor's, swings the predecessor link past the victim,
frees the victim, and advances only the cursor; keeps advance
both cursors. The head never swings (the first node has no
predecessor, so it is always kept) and the entry returns it
unchanged; a miss (empty, singleton, or duplicate-free chain)
returns the head untouched with no `free` — silent legs,
covered by the loop guard, not a branch. The drop test is the
short-circuit `prev != nullptr && cur->val == prev->val`,
lowered by CIRGen as a `cir.ternary` feeding the single
`cir.if`. Faults are loud, not branched: freeing a null,
missing, or already-freed cell aborts in the model
(`memFree`/`memStore` miss/tag/liveness checks), exactly the
L-ptr miss discipline. The single pointer param needs no
`__restrict__` (single-pointer exemption); cycles are out of
scope.

The mirror sweeps with `listUniqueSweep` (fuel-indexed: each
visit reads the payload at `[0]`; on a drop reads the link at
`[1]`, restitches the predecessor, frees, and recurses; a keep
recurses past the node). The contract is a squeeze of every
run to its first element: `ListSeg m' head (dedupAdj vs)`
with every dropped cell dead (live flag cleared — contents
kept but unusable, so any later dereference misses loudly).
Freshness-style hypotheses are unnecessary (nothing
allocates); the fuel bound rules out exhaustion and exactness
decodes the links. The hard proof is repeated segment surgery
around dead cells: the survivor prefix is rebuilt step by step
(`PrefixChain` snoc/restitch), the freed prefix grows like the
clear chase, and the untouched suffix rides `store_other` +
`free_other` with the victim kept out by acyclicity. The
squeeze equation threads a ghost `scanned` payload history:
the kept prefix is the oracle squeeze of everything visited
(`preVals kept = dedupAdj scanned`), and each step closes
against the `dedupAdj_snoc_keep`/`_drop` boundary lemmas keyed
on the last survivor.
-/
import Circe.Emit.LinkedReverse
import Circe.Lemmas.TwoCursor

/-! ## P1: `list_unique` entry -/

/-- Mangled name of the unique entry. -/
def listUniqueName : String :=
  "_Z11list_uniqueP4Node"

/-- The chase-loop body (drop-or-step): named so the
    agreement proof can rewrite it without literals. The drop
    test is the short-circuit `&&` as the pure ternary —
    non-null predecessor and the payload equality test; the
    untaken arm never loads, so a null predecessor keeps
    silently. On a drop the link is saved, the predecessor is
    swung past the victim, the victim is freed, and only the
    cursor advances; on a keep both cursors advance. -/
def listUniqueLoopBody : CStmt :=
  (.if_ (.tif (.une (.var "prev") (.lit .nullptr))
            (.ueq (.pgetVal (.var "cur")) (.pgetVal (.var "prev")))
            (.lit (.b false)))
    (.seq (.assign "next" (.pgetNext (.var "cur")))
      (.seq (.psetNext (.var "prev") (.var "next"))
        (.seq (.nfree (.var "cur"))
          (.assign "cur" (.var "next")))))
    (.seq (.assign "prev" (.var "cur"))
      (.assign "cur" (.pgetNext (.var "cur")))))

/-- The chase loop (isolated for the loop/evaluator
    agreement: guard, drop-or-step body). -/
def listUniqueLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) listUniqueLoopBody)

/-- Canonical CoreIR for `list_unique`: seed the cursors, chase
    while `cur != nullptr`, unlink + free + advance-only-cursor
    on every predecessor-equal payload, step both cursors
    otherwise, return the (unchanged) head on exhaustion. -/
def listUniqueBody : CStmt :=
  (.seq (.let_ "prev" nodeTy (.lit .nullptr))
    (.seq (.let_ "cur" nodeTy (.var "head"))
      (.seq (.let_ "next" nodeTy (.lit .nullptr))
        (.seq listUniqueLoop
          (.return_ (.var "head"))))))

/-- The unique entry: single `Node*` in, `Node*` out (the
    unchanged head). -/
def listUniqueFunc : Func :=
  ⟨listUniqueName,
   [{ name := "head", ty := nodeTy, role := .owned }],
   nodeTy,
   listUniqueBody⟩

/-- Unique environment: head slot, then the two cursor slots
    plus the link spare (the entry binds `head` first, then
    the lets cons `prev`, `cur`, and `next` on the front;
    assigns rewrite slots in place). -/
def mkListUniqueEnv (head prev cur nxt : Option Addr) : Env :=
  [("next", .ptrVal nxt), ("cur", .ptrVal cur),
    ("prev", .ptrVal prev),
    ("head", .ptrVal head)]

theorem mkListUniqueEnv_next (head prev cur nxt : Option Addr) :
    envLookup (mkListUniqueEnv head prev cur nxt) "next" =
      some (.ptrVal nxt) := by
  simp [mkListUniqueEnv, envLookup]

theorem mkListUniqueEnv_cur (head prev cur nxt : Option Addr) :
    envLookup (mkListUniqueEnv head prev cur nxt) "cur" =
      some (.ptrVal cur) := by
  simp [mkListUniqueEnv, envLookup]

theorem mkListUniqueEnv_prev (head prev cur nxt : Option Addr) :
    envLookup (mkListUniqueEnv head prev cur nxt) "prev" =
      some (.ptrVal prev) := by
  simp [mkListUniqueEnv, envLookup]

theorem mkListUniqueEnv_head (head prev cur nxt : Option Addr) :
    envLookup (mkListUniqueEnv head prev cur nxt) "head" =
      some (.ptrVal head) := by
  simp [mkListUniqueEnv, envLookup]

/-! ## Forward mirror (single sweep, unlink inline) -/

/-- Sweep every predecessor-equal payload out of the chain:
    read-only until the link read (payload at `[0]`, then the
    predecessor payload at `[0]` on a non-null predecessor),
    then on a drop read the link at `[1]`, restitch the
    predecessor, free the victim, and recurse past it; a keep
    recurses past the node with the memory untouched. Each
    visit consumes fuel (like the evaluator's loop iteration —
    a drop needs fuel too). The ghost `scanned` accumulates
    visited payloads so the invariant can state the squeeze
    equation. Misses, dangling links, and short blocks abort
    loudly at any fuel. -/
def listUniqueSweep (F : Nat) (m : Mem)
    (head prev cur : Option Addr)
    (scanned : List (BitVec 32))
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
          match prev with
          | none =>
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' =>
              listUniqueSweep F m head (some a) (addrOfWord w')
                (scanned ++ [w]) dropped
          | some p =>
            match memFind m p with
            | none => .error .AssertFail
            | some bp =>
              match memLoad m p bp.tag 0 with
              | .error e => .error e
              | .ok u =>
                if w == u then
                  match memLoad m a b.tag 1 with
                  | .error e => .error e
                  | .ok w' =>
                    match memStore m p bp.tag 1 w' with
                    | .error e => .error e
                    | .ok m1 =>
                      match memFree m1 a b.tag with
                      | .error e => .error e
                      | .ok m2 =>
                        listUniqueSweep F m2 head (some p)
                          (addrOfWord w') (scanned ++ [w])
                          (dropped ++ [(a, b.tag, [w, w'])])
                else
                  match memLoad m a b.tag 1 with
                  | .error e => .error e
                  | .ok w' =>
                    listUniqueSweep F m head (some a) (addrOfWord w')
                      (scanned ++ [w]) dropped

/-- Entry mirror: sweep from the entry head with no predecessor
    and an empty history. -/
def listUniqueFwd (F : Nat) (m : Mem) (head : Option Addr) :
    Result (Mem × Option Addr) :=
  match listUniqueSweep F m head none head [] [] with
  | .error e => .error e
  | .ok (m', hd', _) => .ok (m', hd')

/-! ## Sweep invariant: every visit is kept or dropped -/

/-- Sweep invariant: the read-only prefix is pinned as a
    `PrefixChain` of kept nodes, the suffix is an untouched
    `ListSeg`, previously dropped cells stay dead with their
    payload blocks kept, and the kept payloads are the oracle
    squeeze of the ghost history (`preVals kept =
    `dedupAdj scanned`). The last-kept tuple always matches
    the predecessor's current node (`nodeAt`), so the drop
    test reads the recorded survivor. The head never moves.
    Induction is on fuel; the drop leg restitches the
    predecessor and recurses, the keep legs snoc the visited
    node and recurse. -/
theorem listUniqueSweep_invariant (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (kept : List (Addr × Nat × BitVec 32))
      (head prev cur : Option Addr)
      (suf : List (BitVec 32))
      (scanned : List (BitVec 32))
      (dropped : List (Addr × Nat × List (BitVec 32)))
      (hchain : PrefixChain m head kept cur)
      (hseg : ListSeg m cur suf)
      (hpre : preVals kept = dedupAdj scanned)
      (hprevnil : prev = none → kept = [] ∧ scanned = [])
      (hprevlast : ∀ p, prev = some p →
        ∃ init tp wp, kept = init ++ [(p, tp, wp)] ∧
          nodeAt m p tp wp cur)
      (hdead : ∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ dropped → ∃ w n, blk = [w, linkWord n] ∧
        memFind m a = some ⟨t, false, blk⟩)
      (hlen : suf.length ≤ F)
      (m' : Mem) (hd' : Option Addr)
      (droppedOut : List (Addr × Nat × List (BitVec 32)))
      (hsw : listUniqueSweep F m head prev cur scanned dropped =
        .ok (m', hd', droppedOut)),
    ∃ kept₁,
      PrefixChain m' hd' kept₁ none ∧
      preVals kept₁ = dedupAdj (scanned ++ suf) ∧
      hd' = head ∧
      (∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ droppedOut → ∃ w n, blk = [w, linkWord n] ∧
        memFind m' a = some ⟨t, false, blk⟩) := by

  induction F with
  | zero =>
    intro m hex kept head prev cur suf scanned dropped hchain hseg
      hpre hprevnil hprevlast hdead hlen m' hd'
      droppedOut hsw
    cases cur with
    | none =>
      have hC' : listUniqueSweep 0 m head prev none scanned dropped =
          .ok (m, head, dropped) := by
        simp [listUniqueSweep]
      rw [hC'] at hsw
      simp only [Except.ok.injEq, Prod.mk.injEq] at hsw
      obtain ⟨e1, e2, e3⟩ := hsw
      subst m'; subst hd'; subst droppedOut
      cases hseg with
      | nil =>
        refine ⟨kept, ?_, ?_, rfl, ?_⟩
        · exact hchain
        · rw [hpre]; simp
        · exact hdead
    | some a =>
      unfold listUniqueSweep at hsw
      simp only at hsw
      cases hsw
  | succ F ih =>
    intro m hex kept head prev cur suf scanned dropped hchain hseg
      hpre hprevnil hprevlast hdead hlen m' hd'
      droppedOut hsw
    cases cur with
    | none =>
      have hC' : listUniqueSweep (F + 1) m head prev none scanned
          dropped =
          .ok (m, head, dropped) := by
        simp [listUniqueSweep]
      rw [hC'] at hsw
      simp only [Except.ok.injEq, Prod.mk.injEq] at hsw
      obtain ⟨e1, e2, e3⟩ := hsw
      subst m'; subst hd'; subst droppedOut
      cases hseg with
      | nil =>
        refine ⟨kept, ?_, ?_, rfl, ?_⟩
        · exact hchain
        · rw [hpre]; simp
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
        cases prev with
        | none =>
          obtain ⟨hkept0, hscan0⟩ := hprevnil rfl
          unfold listUniqueSweep at hsw
          simp only [hfb, hmem0, hmem1] at hsw
          rw [hdec] at hsw
          subst hkept0; subst hscan0
          have hchain' : PrefixChain m head [(a, t', v₀)] nxt :=
            PrefixChain.snoc_extend hchain hnode rfl rfl
          have hpre' : preVals [(a, t', v₀)] =
              dedupAdj ([] ++ [v₀]) := by
            simp [preVals, dedupAdj]
          have hprevnil' : (some a : Option Addr) = none →
              [(a, t', v₀)] = [] ∧ ([] ++ [v₀]) = [] := by
            intro h
            cases h
          have hprevlast' : ∀ q, (some a : Option Addr) = some q →
              ∃ init tp wp, [(a, t', v₀)] = init ++ [(q, tp, wp)] ∧
                nodeAt m q tp wp nxt := by
            intro q hq
            cases hq
            exact ⟨[], t', v₀, by simp, hnode⟩
          have hIH := ih m hex [(a, t', v₀)] head (some a) nxt
            vs' ([] ++ [v₀]) dropped hchain' t2 hpre' hprevnil'
            hprevlast' hdead hlen' m' hd' droppedOut hsw
          obtain ⟨kept₁, hch1, hbridge, hpin, hdead1⟩ := hIH
          refine ⟨kept₁, hch1, ?_, hpin, hdead1⟩
          have heq : (([] ++ [v₀]) ++ vs') = ([] ++ (v₀ :: vs')) := by
            simp
          rw [heq] at hbridge
          exact hbridge
        | some p =>
          obtain ⟨init, tp, wp, hsplitEq, hnp⟩ := hprevlast p rfl
          unfold listUniqueSweep at hsw
          simp only [hfb, hmem0, hmem1] at hsw
          cases hFp : memFind m p with
          | none =>
            simp only [hFp] at hsw
            cases hsw
          | some bp =>
            simp only [hFp] at hsw
            have hfindP : memFind m p = some _ := hnp
            rw [hfindP] at hFp
            cases hFp
            have hmemP : memLoad m p tp 0 = .ok wp :=
              nodeLoadVal hnp
            simp only [hmemP] at hsw
            by_cases hcond : (v₀ == wp) = true
            · -- Drop leg: payload equals the last survivor.
              simp only [ite_eq_left hcond] at hsw
              rw [hdec] at hsw
              have heq : (v₀ != wp) = false := by
                simp [bne_eq, hcond]
              have hvv : v₀ = wp := beq_iff_eq.mp hcond
              subst v₀
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
                  rw [hsplitEq] at hchain
                  obtain ⟨midp, hinit, hplast⟩ := PrefixChain.split hchain
                  cases hplast with
                  | cons hnodeP' hrestP =>
                    cases hrestP
                    have hfindP2 : memFind m p = some _ := hnodeP'
                    rw [hfindP2] at hfindP
                    cases hfindP
                    have hfindP' : memFind m p = some _ := hnp
                    have hpNew2 : nodeAt m2' p tp wp nxt :=
                      nodeStoreNext_nodeAt hnp hFS
                    have hnePC : p ≠ a := by
                      intro hcon
                      have hnpC : nodeAt m a tp wp (some a) :=
                        hcon ▸ hnp
                      have hmemC : SegMem (m := m) (some a) a :=
                        SegMem.here hnode
                      have htailP : ListSeg m (some a) (wp :: vs') :=
                        ListSeg.cons hnode t2
                      have hcontra :=
                        ListSeg_head_notin_tail hnpC htailP hex a hmemC
                      exact hcontra rfl
                    have hneCP : a ≠ p := Ne.symm hnePC
                    have hvic2 : nodeAt m2' a t' wp nxt :=
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
                      have htailP : ListSeg m (some a) (wp :: vs') :=
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
                        init ++ [(p, tp, wp)] = [] ∧
                          (scanned ++ [wp]) = [] := by
                      intro h
                      cases h
                    have hprevlast' : ∀ q, (some p : Option Addr) = some q →
                        ∃ i2 t2 w2, init ++ [(p, tp, wp)] =
                          i2 ++ [(q, t2, w2)] ∧
                          nodeAt m3 q t2 w2 nxt := by
                      intro q hq
                      cases hq
                      exact ⟨init, tp, wp, rfl, hpNew3⟩
                    have happ : preVals (init ++ [(p, tp, wp)]) =
                        preVals init ++ [wp] := by simp [preVals]
                    have hlastK : (preVals kept).getLast? = some wp := by
                      rw [hsplitEq, happ]
                      simp
                    have hlast : (dedupAdj scanned).getLast? =
                        some wp := by
                      rw [← hpre]
                      exact hlastK
                    have hpre' : preVals (init ++ [(p, tp, wp)]) =
                        dedupAdj (scanned ++ [wp]) := by
                      rw [happ,
                        dedupAdj_snoc_drop scanned wp wp hlast heq,
                        ← hpre, hsplitEq, happ]
                    have hdead' : ∀ (a2 : Addr) (t2 : Nat)
                        (blk : List (BitVec 32)),
                        (a2, t2, blk) ∈
                          dropped ++ [(a, t', [wp, linkWord nxt])] →
                        ∃ w n, blk = [w, linkWord n] ∧
                        memFind m3 a2 = some ⟨t2, false, blk⟩ := by
                      intro a2 t2 blk hmem2
                      rw [List.mem_append] at hmem2
                      cases hmem2 with
                      | inl hmem2 =>
                        obtain ⟨w2, n2, hblk, hfind⟩ :=
                          hdead _ _ _ hmem2
                        have hne2a : a2 ≠ p := by
                          intro hcon
                          rw [hcon, hfindP'] at hfind
                          simp only [Option.some.injEq, Block.mk.injEq]
                            at hfind
                          obtain ⟨_, hcontra, _⟩ := hfind
                          cases hcontra
                        have hfind2 : memFind m2' a2 =
                            some ⟨t2, false, blk⟩ := by
                          rw [memFind_memStore_other _ _ _ _ _ _ _ hFS hne2a]
                          exact hfind
                        have hne2b : a2 ≠ a := by
                          intro hcon
                          rw [hcon, hvic2] at hfind2
                          simp only [Option.some.injEq, Block.mk.injEq]
                            at hfind2
                          obtain ⟨_, hcontra, _⟩ := hfind2
                          cases hcontra
                        refine ⟨w2, n2, hblk, ?_⟩
                        rw [memFind_memFree_other _ _ _ _ _ hFR2 hne2b]
                        exact hfind2
                      | inr hmem2 =>
                        simp only [List.mem_singleton] at hmem2
                        obtain ⟨rfl, rfl, rfl⟩ := hmem2
                        exact ⟨wp, nxt, rfl,
                          memFind_memFree_dead hvic2 hFR2⟩
                    have hex3 : ∀ x, (memFind m3 x).isSome = true →
                        x + 1 < 2 ^ 32 := by
                      intro x hx
                      by_cases heqx : x = a
                      · rw [heqx]
                        exact hex a (by rw [hfb]; rfl)
                      · rw [memFind_memFree_other _ _ _ _ _ hFR2 heqx]
                          at hx
                        exact hex2 x hx
                    have hIH := ih m3 hex3 (init ++ [(p, tp, wp)]) head
                      (some p) nxt vs' (scanned ++ [wp])
                      (dropped ++ [(a, t', [wp, linkWord nxt])])
                      hchain' hsuf3 hpre' hprevnil' hprevlast'
                      hdead' hlen' m' hd' droppedOut hsw
                    obtain ⟨kept₁, hch1, hbridge, hpin, hdead1⟩ := hIH
                    refine ⟨kept₁, hch1, ?_, hpin, hdead1⟩
                    have heqS : ((scanned ++ [wp]) ++ vs') =
                        (scanned ++ (wp :: vs')) := by simp
                    rw [heqS] at hbridge
                    exact hbridge
            · -- Keep leg: payload differs; snoc the visited node.
              simp only [ite_eq_right hcond] at hsw
              rw [hdec] at hsw
              have hnev : v₀ ≠ wp := fun heq => hcond (by rw [heq]; simp)
              have hT : (v₀ != wp) = true := bne_iff_ne.mpr hnev
              have hchain' : PrefixChain m head
                  (kept ++ [(a, t', v₀)]) nxt :=
                PrefixChain.snoc_extend hchain hnode rfl rfl
              have hprevnil' : (some a : Option Addr) = none →
                  kept ++ [(a, t', v₀)] = [] ∧
                    (scanned ++ [v₀]) = [] := by
                intro h
                cases h
              have hprevlast' : ∀ q, (some a : Option Addr) = some q →
                  ∃ init tp wp, kept ++ [(a, t', v₀)] =
                    init ++ [(q, tp, wp)] ∧ nodeAt m q tp wp nxt := by
                intro q hq
                cases hq
                exact ⟨kept, t', v₀, rfl, hnode⟩
              have happ : preVals (kept ++ [(a, t', v₀)]) =
                  preVals kept ++ [v₀] := by simp [preVals]
              have happInit : preVals (init ++ [(p, tp, wp)]) =
                  preVals init ++ [wp] := by simp [preVals]
              have hlastK : (preVals kept).getLast? = some wp := by
                rw [hsplitEq, happInit]
                simp
              have hlast : (dedupAdj scanned).getLast? = some wp := by
                rw [← hpre]
                exact hlastK
              have hpre' : preVals (kept ++ [(a, t', v₀)]) =
                  dedupAdj (scanned ++ [v₀]) := by
                rw [happ, hpre,
                  dedupAdj_snoc_keep scanned v₀ wp hlast hT]
              have hIH := ih m hex (kept ++ [(a, t', v₀)]) head
                (some a) nxt vs' (scanned ++ [v₀]) dropped
                hchain' t2 hpre' hprevnil' hprevlast' hdead hlen'
                m' hd' droppedOut hsw
              obtain ⟨kept₁, hch1, hbridge, hpin, hdead1⟩ := hIH
              refine ⟨kept₁, hch1, ?_, hpin, hdead1⟩
              have heqS : ((scanned ++ [v₀]) ++ vs') =
                  (scanned ++ (v₀ :: vs')) := by simp
              rw [heqS] at hbridge
              exact hbridge

/-- The entry mirror returns the squeezed chain: the head never
    moves, every dropped cell is dead with its payload block
    kept, and the surviving chain holds the oracle squeeze. -/
theorem listUniqueFwd_correct (F : Nat) (m : Mem) (head : Option Addr)
    (vs : List (BitVec 32))
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hseg : ListSeg m head vs) (hlen : vs.length ≤ F)
    (m' : Mem) (hd' : Option Addr)
    (hfwd : listUniqueFwd F m head = .ok (m', hd')) :
    ∃ dropped' : List (Addr × Nat × List (BitVec 32)),
      (∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ dropped' →
        ∃ w n, blk = [w, linkWord n] ∧
        memFind m' a = some ⟨t, false, blk⟩) ∧
      hd' = head ∧
      ListSeg m' hd' (dedupAdj vs) := by
  unfold listUniqueFwd at hfwd
  cases hsw : listUniqueSweep F m head none head [] [] with
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
    have hpre0 : preVals ([] : List (Addr × Nat × BitVec 32)) =
        dedupAdj [] := by
      simp [preVals, dedupAdj]
    have hIH := listUniqueSweep_invariant F m hex [] head none head
      vs [] [] hchain hseg hpre0
      (fun _ => ⟨rfl, rfl⟩)
      (fun p hp => by cases hp)
      (fun (a : Addr) (t : Nat) (blk : List (BitVec 32))
        (h : (a, t, blk) ∈ ([] : List (Addr × Nat × List (BitVec 32)))) =>
        by cases (List.not_mem_nil h))
      hlen m' hd' dropped' hsw
    obtain ⟨kept₁, hch1, hbridge, hpin, hdead1⟩ := hIH
    have hlist := PrefixChain.appendSeg hch1 ListSeg.nil
    simp only [List.append_nil] at hlist
    refine ⟨dropped', hdead1, hpin, ?_⟩
    rw [hbridge] at hlist
    simp only [List.nil_append] at hlist
    exact hlist

/-! ## Loop/evaluator agreement -/

/-- The loop agrees with the sweep: the evaluator runs the
    same guard, the same short-circuit drop test, and the same
    unlink/free/step legs, landing in the sweep's memory with
    the cursor/env in matching slots. -/
theorem listUniqueLoop_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (head : Option Addr)
      (prev cur : Option Addr)
      (scanned : List (BitVec 32))
      (kept : List (Addr × Nat × BitVec 32))
      (hchain : PrefixChain m head kept cur)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hprevnil : prev = none → kept = [])
      (hprevlast : ∀ p, prev = some p →
        ∃ init tp wp, kept = init ++ [(p, tp, wp)] ∧
          nodeAt m p tp wp cur)
      (dropped : List (Addr × Nat × List (BitVec 32)))
      (hdead : ∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ dropped → ∃ w n, blk = [w, linkWord n] ∧
        memFind m a = some ⟨t, false, blk⟩)
      (nxt₀ : Option Addr)
      (hlen : suf.length ≤ F)
      (m' : Mem) (hd' : Option Addr)
      (droppedOut : List (Addr × Nat × List (BitVec 32)))
      (hC : listUniqueSweep F m head prev cur scanned dropped =
        .ok (m', hd', droppedOut)),
    ∃ prev' nxt',
      memEvalStmtFuel F listUniqueLoop
        (mkListUniqueEnv head prev cur nxt₀) m π =
        .ok ((mkListUniqueEnv hd' prev' none nxt', m', π),
          .fellThrough) := by
  induction F with
  | zero =>
    intro m π hex head prev cur scanned kept hchain suf hseg
      hprevnil hprevlast dropped hdead nxt₀ hlen m' hd' droppedOut hC
    cases cur with
    | none =>
      have hC' : listUniqueSweep 0 m head prev none scanned dropped =
          .ok (m, head, dropped) := by
        simp [listUniqueSweep]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      obtain ⟨e1, e2, e3⟩ := hC
      subst m'; subst hd'; subst droppedOut
      refine ⟨prev, nxt₀, ?_⟩
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListUniqueEnv head prev none nxt₀) m π =
          .ok (.b false) := by
        have hcurE : memEvalExpr (.var "cur")
            (mkListUniqueEnv head prev none nxt₀) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (mkListUniqueEnv_cur head prev none nxt₀)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkListUniqueEnv head prev none nxt₀) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
          hcurE hnullE
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
      exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
    | some a =>
      unfold listUniqueSweep at hC
      simp only at hC
      cases hC
  | succ F ih =>
    intro m π hex head prev cur scanned kept hchain suf hseg
      hprevnil hprevlast dropped hdead nxt₀ hlen m' hd' droppedOut hC
    cases cur with
    | none =>
      have hC' : listUniqueSweep (F + 1) m head prev none scanned
          dropped =
          .ok (m, head, dropped) := by
        simp [listUniqueSweep]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      obtain ⟨e1, e2, e3⟩ := hC
      subst m'; subst hd'; subst droppedOut
      refine ⟨prev, nxt₀, ?_⟩
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListUniqueEnv head prev none nxt₀) m π =
          .ok (.b false) := by
        have hcurE : memEvalExpr (.var "cur")
            (mkListUniqueEnv head prev none nxt₀) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (mkListUniqueEnv_cur head prev none nxt₀)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkListUniqueEnv head prev none nxt₀) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
          hcurE hnullE
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
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
            (mkListUniqueEnv head prev (some a) nxt₀) m π =
            .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (mkListUniqueEnv_cur head prev (some a) nxt₀)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkListUniqueEnv head prev (some a) nxt₀) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListUniqueEnv head prev (some a) nxt₀) m π =
            .ok (.b true) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
            hcurE hnullE
          have hbe : (((some a) : Option Addr) != none) = true := by simp
          rw [hbe] at hg
          exact hg
        have hpget : memEvalExpr (.pgetVal (.var "cur"))
            (mkListUniqueEnv head prev (some a) nxt₀) m π =
            .ok (.i32 v₀) :=
          memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE hfb hmem0
        have hpgn : memEvalExpr (.pgetNext (.var "cur"))
            (mkListUniqueEnv head prev (some a) nxt₀) m π =
            .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
          memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE hfb hmem1w
        have hloop : listUniqueLoop =
            (.while_ (.une (.var "cur") (.lit .nullptr))
              listUniqueLoopBody) := rfl
        have hbody : listUniqueLoopBody =
            (.if_ (.tif (.une (.var "prev") (.lit .nullptr))
                    (.ueq (.pgetVal (.var "cur"))
                      (.pgetVal (.var "prev")))
                    (.lit (.b false)))
              (.seq (.assign "next" (.pgetNext (.var "cur")))
                (.seq (.psetNext (.var "prev") (.var "next"))
                  (.seq (.nfree (.var "cur"))
                    (.assign "cur" (.var "next")))))
              (.seq (.assign "prev" (.var "cur"))
                (.assign "cur" (.pgetNext (.var "cur"))))) := rfl
        unfold listUniqueSweep at hC
        simp only [hfb, hmem0, hmem1] at hC
        cases prev with
        | none =>
          obtain hkept0 : kept = [] := hprevnil rfl
          simp only [hmem1] at hC
          subst hkept0
          have hprevE : memEvalExpr (.var "prev")
              (mkListUniqueEnv head none (some a) nxt₀) m π =
              .ok (.ptrVal none) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListUniqueEnv_prev head none (some a) nxt₀)
          have hcondV : memEvalExpr
              (.une (.var "prev") (.lit .nullptr))
              (mkListUniqueEnv head none (some a) nxt₀) m π =
              .ok (.b false) := by
            have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
              hprevE hnullE
            have hbe : ((none : Option Addr) != none) = false := by simp
            rw [hbe] at hg
            exact hg
          have htif : memEvalExpr
              (.tif (.une (.var "prev") (.lit .nullptr))
                (.ueq (.pgetVal (.var "cur")) (.pgetVal (.var "prev")))
                (.lit (.b false)))
              (mkListUniqueEnv head none (some a) nxt₀) m π =
              .ok (.b false) := by
            unfold memEvalExpr
            rw [hcondV]
            simp [memEvalExpr, litVal]
          have hassP := memEvalStmtFuel_assign_mem F "prev" (.var "cur")
            (mkListUniqueEnv head none (some a) nxt₀) m π
            (.ptrVal (some a))
            (mkListUniqueEnv head (some a) (some a) nxt₀) hcurE
            (by simp [mkListUniqueEnv, envUpdate])
          have hcurE1 : memEvalExpr (.var "cur")
              (mkListUniqueEnv head (some a) (some a) nxt₀) m π =
              .ok (.ptrVal (some a)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (mkListUniqueEnv_cur head (some a) (some a) nxt₀)
          have hpgn1 : memEvalExpr (.pgetNext (.var "cur"))
              (mkListUniqueEnv head (some a) (some a) nxt₀) m π =
              .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE1 hfb hmem1w
          have hassC := memEvalStmtFuel_assign_mem F "cur"
            (.pgetNext (.var "cur"))
            (mkListUniqueEnv head (some a) (some a) nxt₀) m π
            (.ptrVal (addrOfWord (linkWord nxt)))
            (mkListUniqueEnv head (some a)
              (addrOfWord (linkWord nxt)) nxt₀) hpgn1
            (by simp [mkListUniqueEnv, envUpdate])
          have helse : memEvalStmtFuel F
              (.seq (.assign "prev" (.var "cur"))
                (.assign "cur" (.pgetNext (.var "cur"))))
              (mkListUniqueEnv head none (some a) nxt₀) m π =
              .ok (((mkListUniqueEnv head (some a)
                (addrOfWord (linkWord nxt)) nxt₀, m, π)),
                .fellThrough) :=
            memEvalStmtFuel_seq_fallthrough_trans F
              (.assign "prev" (.var "cur"))
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkListUniqueEnv head none (some a) nxt₀) m π
              (mkListUniqueEnv head (some a) (some a) nxt₀) m π _
              hassP hassC
          have hbodyEv : memEvalStmtFuel F listUniqueLoopBody
              (mkListUniqueEnv head none (some a) nxt₀) m π =
              .ok (((mkListUniqueEnv head (some a)
                (addrOfWord (linkWord nxt)) nxt₀, m, π)),
                .fellThrough) := by
            rw [hbody]
            exact (memEvalStmtFuel_if_false F _ _ _ _ _ _ htif).trans
              helse
          have hWT : memEvalStmtFuel (F + 1) listUniqueLoop
              (mkListUniqueEnv head none (some a) nxt₀) m π =
              memEvalStmtFuel F listUniqueLoop
                (mkListUniqueEnv head (some a)
                  (addrOfWord (linkWord nxt)) nxt₀) m π := by
            rw [hloop]
            have h := memEvalStmtFuel_while_true F _
              listUniqueLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          have ht2' : ListSeg m (addrOfWord (linkWord nxt)) vs' := by
            rw [hdec]
            exact t2
          have hchain' : PrefixChain m head [(a, t', v₀)]
              (addrOfWord (linkWord nxt)) := by
            rw [hdec]
            exact PrefixChain.snoc_extend hchain hnode rfl rfl
          have hprevnil' : (some a : Option Addr) = none →
              [(a, t', v₀)] = [] := by
            intro h
            cases h
          have hprevlast' : ∀ q, (some a : Option Addr) = some q →
              ∃ init tp wp, [(a, t', v₀)] = init ++ [(q, tp, wp)] ∧
                nodeAt m q tp wp (addrOfWord (linkWord nxt)) := by
            intro q hq
            cases hq
            rw [hdec]
            exact ⟨[], t', v₀, by simp, hnode⟩
          have hIH := ih m π hex head (some a)
            (addrOfWord (linkWord nxt)) (scanned ++ [v₀])
            [(a, t', v₀)] hchain' vs' ht2' hprevnil' hprevlast'
            dropped hdead nxt₀ hlen' m' hd' droppedOut hC
          obtain ⟨prev', nxt', hIH'⟩ := hIH
          refine ⟨prev', nxt', ?_⟩
          rw [hWT]
          exact hIH'
        | some p =>
          obtain ⟨init, tp, wp, hsplitEq, hnp⟩ := hprevlast p rfl
          cases hFp : memFind m p with
          | none =>
            simp only [hFp] at hC
            cases hC
          | some bp =>
            simp only [hFp] at hC
            have hfindP : memFind m p = some _ := hnp
            rw [hfindP] at hFp
            cases hFp
            have hmemP : memLoad m p tp 0 = .ok wp := nodeLoadVal hnp
            simp only [hmemP] at hC
            have hprevE : memEvalExpr (.var "prev")
                (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                .ok (.ptrVal (some p)) := by
              rw [memEvalExpr_var]
              exact evalExpr_var_hit _ _ _
                (mkListUniqueEnv_prev head (some p) (some a) nxt₀)
            have hcondT : memEvalExpr
                (.une (.var "prev") (.lit .nullptr))
                (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                .ok (.b true) := by
              have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some p) none
                hprevE hnullE
              have hbe : (((some p) : Option Addr) != none) = true := by
                simp
              rw [hbe] at hg
              exact hg
            have hpgetP : memEvalExpr (.pgetVal (.var "prev"))
                (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                .ok (.i32 wp) :=
              memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hprevE hfindP hmemP
            have hueq : memEvalExpr
                (.ueq (.pgetVal (.var "cur")) (.pgetVal (.var "prev")))
                (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                .ok (.b (v₀ == wp)) := by
              unfold memEvalExpr
              simp only [hpget, hpgetP]
            by_cases hcond : (v₀ == wp) = true
            · -- Evaluator drop leg: unlink, free, advance only cursor.
              have hueqT : memEvalExpr
                  (.ueq (.pgetVal (.var "cur")) (.pgetVal (.var "prev")))
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                  .ok (.b true) := by
                rw [hcond] at hueq
                exact hueq
              have htifT : memEvalExpr
                  (.tif (.une (.var "prev") (.lit .nullptr))
                    (.ueq (.pgetVal (.var "cur"))
                      (.pgetVal (.var "prev")))
                    (.lit (.b false)))
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                  .ok (.b true) := by
                unfold memEvalExpr
                rw [hcondT]
                exact hueqT
              simp only [ite_eq_left hcond] at hC
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
                    (mkListUniqueEnv head (some p) (some a) nxt₀) m π
                    (.ptrVal (addrOfWord (linkWord nxt)))
                    (mkListUniqueEnv head (some p) (some a)
                      (addrOfWord (linkWord nxt))) hpgn
                    (by simp [mkListUniqueEnv, envUpdate])
                  have hnextE : memEvalExpr (.var "next")
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π =
                      .ok (.ptrVal (addrOfWord (linkWord nxt))) := by
                    rw [memEvalExpr_var]
                    exact evalExpr_var_hit _ _ _
                      (mkListUniqueEnv_next head (some p) (some a)
                        (addrOfWord (linkWord nxt)))
                  have hstoreP : memStore m p tp 1
                      (linkWord (addrOfWord (linkWord nxt))) =
                      .ok m2' := by
                    rw [hdec]
                    exact hFS
                  have hprevE1 : memEvalExpr (.var "prev")
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π =
                      .ok (.ptrVal (some p)) := by
                    rw [memEvalExpr_var]
                    exact evalExpr_var_hit _ _ _
                      (mkListUniqueEnv_prev head (some p) (some a)
                        (addrOfWord (linkWord nxt)))
                  have hpset := memEvalStmtFuel_psetNext_ok F
                    (.var "prev") (.var "next")
                    (mkListUniqueEnv head (some p) (some a)
                      (addrOfWord (linkWord nxt))) m π
                    p (addrOfWord (linkWord nxt)) _ m2'
                    hprevE1 hnextE hfindP hstoreP
                  have hnePC : p ≠ a := by
                    intro hcon
                    have hnpC : nodeAt m a tp wp (some a) := hcon ▸ hnp
                    have hmemC : SegMem (m := m) (some a) a :=
                      SegMem.here hnode
                    have htailP : ListSeg m (some a) (v₀ :: vs') :=
                      ListSeg.cons hnode t2
                    have hcontra :=
                      ListSeg_head_notin_tail hnpC htailP hex a hmemC
                    exact hcontra rfl
                  have hneCP : a ≠ p := Ne.symm hnePC
                  have hvic2 : nodeAt m2' a t' v₀ nxt :=
                    nodeAt_store_other_fwd hnode hFS hneCP
                  have hfindC : memFind m2' a =
                      some ⟨t', true, [v₀, linkWord nxt]⟩ := hvic2
                  have hcurE2 : memEvalExpr (.var "cur")
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m2' π =
                      .ok (.ptrVal (some a)) := by
                    rw [memEvalExpr_var]
                    exact evalExpr_var_hit _ _ _
                      (mkListUniqueEnv_cur head (some p) (some a)
                        (addrOfWord (linkWord nxt)))
                  have hnfree2 := memEvalStmtFuel_nfree_ok F (.var "cur")
                    (mkListUniqueEnv head (some p) (some a)
                      (addrOfWord (linkWord nxt))) m2' π a _ m3
                    hcurE2 hfindC hFR2
                  have hnextE2 : memEvalExpr (.var "next")
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m3 π =
                      .ok (.ptrVal (addrOfWord (linkWord nxt))) := by
                    rw [memEvalExpr_var]
                    exact evalExpr_var_hit _ _ _
                      (mkListUniqueEnv_next head (some p) (some a)
                        (addrOfWord (linkWord nxt)))
                  have hassC := memEvalStmtFuel_assign_mem F "cur"
                    (.var "next")
                    (mkListUniqueEnv head (some p) (some a)
                      (addrOfWord (linkWord nxt))) m3 π
                    (.ptrVal (addrOfWord (linkWord nxt)))
                    (mkListUniqueEnv head (some p)
                      (addrOfWord (linkWord nxt))
                      (addrOfWord (linkWord nxt))) hnextE2
                    (by simp [mkListUniqueEnv, envUpdate])
                  have hseqNC : memEvalStmtFuel F
                      (.seq (.nfree (.var "cur"))
                        (.assign "cur" (.var "next")))
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m2' π =
                      .ok (((mkListUniqueEnv head (some p)
                        (addrOfWord (linkWord nxt))
                        (addrOfWord (linkWord nxt)), m3, π)),
                        .fellThrough) :=
                    memEvalStmtFuel_seq_fallthrough_trans F
                      (.nfree (.var "cur")) (.assign "cur" (.var "next"))
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m2' π
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m3 π _
                      hnfree2 hassC
                  have hrest : memEvalStmtFuel F
                      (.seq (.psetNext (.var "prev") (.var "next"))
                        (.seq (.nfree (.var "cur"))
                          (.assign "cur" (.var "next"))))
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π =
                      .ok (((mkListUniqueEnv head (some p)
                        (addrOfWord (linkWord nxt))
                        (addrOfWord (linkWord nxt)), m3, π)),
                        .fellThrough) :=
                    memEvalStmtFuel_seq_fallthrough_trans F _ _
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m2' π _
                      hpset hseqNC
                  have hthen : memEvalStmtFuel F
                      (.seq (.assign "next" (.pgetNext (.var "cur")))
                        (.seq (.psetNext (.var "prev") (.var "next"))
                          (.seq (.nfree (.var "cur"))
                            (.assign "cur" (.var "next")))))
                      (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                      .ok (((mkListUniqueEnv head (some p)
                        (addrOfWord (linkWord nxt))
                        (addrOfWord (linkWord nxt)), m3, π)),
                        .fellThrough) :=
                    memEvalStmtFuel_seq_fallthrough_trans F _ _
                      (mkListUniqueEnv head (some p) (some a) nxt₀) m π
                      (mkListUniqueEnv head (some p) (some a)
                        (addrOfWord (linkWord nxt))) m π _
                      hassN hrest
                  have hbodyEv : memEvalStmtFuel F listUniqueLoopBody
                      (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                      .ok (((mkListUniqueEnv head (some p)
                        (addrOfWord (linkWord nxt))
                        (addrOfWord (linkWord nxt)), m3, π)),
                        .fellThrough) := by
                    rw [hbody]
                    exact (memEvalStmtFuel_if_true F _ _ _ _ _ _
                      htifT).trans hthen
                  have hWT : memEvalStmtFuel (F + 1) listUniqueLoop
                      (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                      memEvalStmtFuel F listUniqueLoop
                        (mkListUniqueEnv head (some p)
                          (addrOfWord (linkWord nxt))
                          (addrOfWord (linkWord nxt))) m3 π := by
                    rw [hloop]
                    have h := memEvalStmtFuel_while_true F _
                      listUniqueLoopBody _ _ _ hgT
                    simp only [hbodyEv] at h
                    exact h
                  rw [hsplitEq] at hchain
                  obtain ⟨midp, hinit, hplast⟩ :=
                    PrefixChain.split hchain
                  cases hplast with
                  | cons hnodeP' hrestP =>
                    cases hrestP
                    have hfindP2 : memFind m p = some _ := hnodeP'
                    rw [hfindP2] at hfindP
                    cases hfindP
                    have hfindP' : memFind m p = some _ := hnp
                    have hpNew2 : nodeAt m2' p tp wp nxt :=
                      nodeStoreNext_nodeAt hnp hFS
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
                      have htailP : ListSeg m (some a) (v₀ :: vs') :=
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
                        (init ++ [(p, tp, wp)])
                        (addrOfWord (linkWord nxt)) := by
                      rw [hdec]
                      exact PrefixChain.snoc_extend hpreT hpNew3 rfl rfl
                    have hsuf3' : ListSeg m3
                        (addrOfWord (linkWord nxt)) vs' := by
                      rw [hdec]
                      exact hsuf3
                    have hprevnil' : (some p : Option Addr) = none →
                        init ++ [(p, tp, wp)] = [] := by
                      intro h
                      cases h
                    have hprevlast' : ∀ q, (some p : Option Addr) = some q →
                        ∃ i2 t2 w2, init ++ [(p, tp, wp)] =
                          i2 ++ [(q, t2, w2)] ∧
                          nodeAt m3 q t2 w2
                            (addrOfWord (linkWord nxt)) := by
                      intro q hq
                      cases hq
                      rw [hdec]
                      exact ⟨init, tp, wp, rfl, hpNew3⟩
                    have hdead' : ∀ (a2 : Addr) (t2 : Nat)
                        (blk : List (BitVec 32)),
                        (a2, t2, blk) ∈
                          dropped ++ [(a, t', [v₀, linkWord nxt])] →
                        ∃ w n, blk = [w, linkWord n] ∧
                        memFind m3 a2 = some ⟨t2, false, blk⟩ := by
                      intro a2 t2 blk hmem2
                      rw [List.mem_append] at hmem2
                      cases hmem2 with
                      | inl hmem2 =>
                        obtain ⟨w2, n2, hblk, hfind⟩ :=
                          hdead _ _ _ hmem2
                        have hne2a : a2 ≠ p := by
                          intro hcon
                          rw [hcon, hfindP'] at hfind
                          simp only [Option.some.injEq, Block.mk.injEq]
                            at hfind
                          obtain ⟨_, hcontra, _⟩ := hfind
                          cases hcontra
                        have hfind2 : memFind m2' a2 =
                            some ⟨t2, false, blk⟩ := by
                          rw [memFind_memStore_other _ _ _ _ _ _ _ hFS hne2a]
                          exact hfind
                        have hne2b : a2 ≠ a := by
                          intro hcon
                          rw [hcon, hvic2] at hfind2
                          simp only [Option.some.injEq, Block.mk.injEq]
                            at hfind2
                          obtain ⟨_, hcontra, _⟩ := hfind2
                          cases hcontra
                        refine ⟨w2, n2, hblk, ?_⟩
                        rw [memFind_memFree_other _ _ _ _ _ hFR2 hne2b]
                        exact hfind2
                      | inr hmem2 =>
                        simp only [List.mem_singleton] at hmem2
                        obtain ⟨rfl, rfl, rfl⟩ := hmem2
                        exact ⟨v₀, nxt, rfl,
                          memFind_memFree_dead hvic2 hFR2⟩
                    have hex3 : ∀ x, (memFind m3 x).isSome = true →
                        x + 1 < 2 ^ 32 := by
                      intro x hx
                      by_cases heqx : x = a
                      · rw [heqx]
                        exact hex a (by rw [hfb]; rfl)
                      · rw [memFind_memFree_other _ _ _ _ _ hFR2 heqx]
                          at hx
                        exact hex2 x hx
                    have hIH := ih m3 π hex3 head (some p)
                      (addrOfWord (linkWord nxt)) (scanned ++ [v₀])
                      (init ++ [(p, tp, wp)]) hchain' vs' hsuf3'
                      hprevnil' hprevlast'
                      (dropped ++ [(a, t', [v₀, linkWord nxt])])
                      hdead' (addrOfWord (linkWord nxt)) hlen'
                      m' hd' droppedOut hC
                    obtain ⟨prev', nxt', hIH'⟩ := hIH
                    refine ⟨prev', nxt', ?_⟩
                    rw [hWT]
                    exact hIH'
            · -- Evaluator keep leg: payload differs; snoc the visited node.
              have hnev : v₀ ≠ wp := fun heq => hcond (by rw [heq]; simp)
              simp only [ite_eq_right hcond] at hC
              have hueqF : memEvalExpr
                  (.ueq (.pgetVal (.var "cur")) (.pgetVal (.var "prev")))
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                  .ok (.b false) := by
                have hbf : (v₀ == wp) = false := by simp_all
                rw [hbf] at hueq
                exact hueq
              have htifF : memEvalExpr
                  (.tif (.une (.var "prev") (.lit .nullptr))
                    (.ueq (.pgetVal (.var "cur"))
                      (.pgetVal (.var "prev")))
                    (.lit (.b false)))
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                  .ok (.b false) := by
                unfold memEvalExpr
                rw [hcondT]
                exact hueqF
              have hassP := memEvalStmtFuel_assign_mem F "prev" (.var "cur")
                (mkListUniqueEnv head (some p) (some a) nxt₀) m π
                (.ptrVal (some a))
                (mkListUniqueEnv head (some a) (some a) nxt₀) hcurE
                (by simp [mkListUniqueEnv, envUpdate])
              have hcurE1 : memEvalExpr (.var "cur")
                  (mkListUniqueEnv head (some a) (some a) nxt₀) m π =
                  .ok (.ptrVal (some a)) := by
                rw [memEvalExpr_var]
                exact evalExpr_var_hit _ _ _
                  (mkListUniqueEnv_cur head (some a) (some a) nxt₀)
              have hpgn1 : memEvalExpr (.pgetNext (.var "cur"))
                  (mkListUniqueEnv head (some a) (some a) nxt₀) m π =
                  .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
                memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE1 hfb hmem1w
              have hassC := memEvalStmtFuel_assign_mem F "cur"
                (.pgetNext (.var "cur"))
                (mkListUniqueEnv head (some a) (some a) nxt₀) m π
                (.ptrVal (addrOfWord (linkWord nxt)))
                (mkListUniqueEnv head (some a)
                  (addrOfWord (linkWord nxt)) nxt₀) hpgn1
                (by simp [mkListUniqueEnv, envUpdate])
              have helse : memEvalStmtFuel F
                  (.seq (.assign "prev" (.var "cur"))
                    (.assign "cur" (.pgetNext (.var "cur"))))
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                  .ok (((mkListUniqueEnv head (some a)
                    (addrOfWord (linkWord nxt)) nxt₀, m, π)),
                    .fellThrough) :=
                memEvalStmtFuel_seq_fallthrough_trans F
                  (.assign "prev" (.var "cur"))
                  (.assign "cur" (.pgetNext (.var "cur")))
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π
                  (mkListUniqueEnv head (some a) (some a) nxt₀) m π _
                  hassP hassC
              have hbodyEv : memEvalStmtFuel F listUniqueLoopBody
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                  .ok (((mkListUniqueEnv head (some a)
                    (addrOfWord (linkWord nxt)) nxt₀, m, π)),
                    .fellThrough) := by
                rw [hbody]
                exact (memEvalStmtFuel_if_false F _ _ _ _ _ _ htifF).trans
                  helse
              have hWT : memEvalStmtFuel (F + 1) listUniqueLoop
                  (mkListUniqueEnv head (some p) (some a) nxt₀) m π =
                  memEvalStmtFuel F listUniqueLoop
                    (mkListUniqueEnv head (some a)
                      (addrOfWord (linkWord nxt)) nxt₀) m π := by
                rw [hloop]
                have h := memEvalStmtFuel_while_true F _
                  listUniqueLoopBody _ _ _ hgT
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
                  ∃ i2 t2 w2, kept ++ [(a, t', v₀)] =
                    i2 ++ [(q, t2, w2)] ∧
                    nodeAt m q t2 w2
                      (addrOfWord (linkWord nxt)) := by
                intro q hq
                cases hq
                rw [hdec]
                exact ⟨kept, t', v₀, rfl, hnode⟩
              have hIH := ih m π hex head (some a)
                (addrOfWord (linkWord nxt)) (scanned ++ [v₀])
                (kept ++ [(a, t', v₀)]) hchain' vs' ht2'
                hprevnil' hprevlast' dropped hdead nxt₀ hlen'
                m' hd' droppedOut hC
              obtain ⟨prev', nxt', hIH'⟩ := hIH
              refine ⟨prev', nxt', ?_⟩
              rw [hWT]
              exact hIH'

/-- Entry correctness: evaluating `list_unique` on a `ListSeg`
    returns the swept head with the squeezed survivors and every
    dropped victim cell dead. The three cursor lets build the
    sweep environment, the loop agreement runs the chase, and the
    return reads back the unchanged head. The memory contract
    (squeezed chain + dead victims) is the forward mirror's. -/
theorem listUniqueFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs) (hlen : vs.length ≤ F)
    (hfwd : listUniqueFwd F m head = .ok (m', hd')) :
    ∃ dropped' : List (Addr × Nat × List (BitVec 32)), ∃ ρ',
      memEvalStmtFuel F listUniqueFunc.body
        [("head", .ptrVal head)] m π =
        .ok ((ρ', m', π), .returned (.ptrVal hd')) ∧
      ListSeg m' hd' (dedupAdj vs) ∧
      (∀ (a : Addr) (t : Nat) (blk : List (BitVec 32)),
        (a, t, blk) ∈ dropped' →
        ∃ w n, blk = [w, linkWord n] ∧
        memFind m' a = some ⟨t, false, blk⟩) := by
  unfold listUniqueFwd at hfwd
  cases hsw : listUniqueSweep F m head none head [] [] with
  | error e =>
    simp only [hsw] at hfwd
    cases hfwd
  | ok res =>
    obtain ⟨m'', hd'', dropped''⟩ := res
    have hfwd0 := hfwd
    simp only [hsw] at hfwd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨e1, e2⟩ := hfwd
    have hcorr := listUniqueFwd_correct F m head vs hex hseg hlen
      m' hd' hfwd0
    obtain ⟨dropped', hdead', hpin, hlist⟩ := hcorr
    subst m''; subst hd''
    have hchain0 : PrefixChain m head [] head := PrefixChain.nil
    have hloop := listUniqueLoop_agree F m π hex head none head [] []
      hchain0 vs hseg (fun _ => rfl)
      (fun p hp => by cases hp)
      [] (fun (a : Addr) (t : Nat) (blk : List (BitVec 32))
        (h : (a, t, blk) ∈ ([] : List (Addr × Nat × List (BitVec 32)))) =>
        by cases (List.not_mem_nil h))
      none hlen m' hd' dropped'' hsw
    obtain ⟨prev', nxt', hloop'⟩ := hloop
    have eP : memEvalExpr (.lit .nullptr)
        [("head", .ptrVal head)] m π =
        evalExpr (.lit .nullptr)
          [("head", .ptrVal head)] :=
      memEvalExpr_lit _ _ _ _
    have vP : evalExpr (.lit .nullptr)
        [("head", .ptrVal head)] =
        .ok (.ptrVal none) := by simp [evalExpr, litVal]
    have hA := memEvalStmtFuel_let_pure F "prev" nodeTy (.lit .nullptr)
      _ _ _ (.ptrVal none)
      (by simp) (by simp) (by simp) (by simp) eP vP
    have eC : memEvalExpr (.var "head")
        ([("prev", .ptrVal none),
          ("head", .ptrVal head)]) m π =
        evalExpr (.var "head")
          ([("prev", .ptrVal none),
            ("head", .ptrVal head)]) :=
      memEvalExpr_var _ _ _ _
    have vC : evalExpr (.var "head")
        ([("prev", .ptrVal none),
          ("head", .ptrVal head)]) =
        .ok (.ptrVal head) :=
      evalExpr_var_hit _ _ _ (by simp [envLookup])
    have hB := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
      _ _ _ (.ptrVal head)
      (by simp) (by simp) (by simp) (by simp) eC vC
    have eN : memEvalExpr (.lit .nullptr)
        ([("cur", .ptrVal head), ("prev", .ptrVal none),
          ("head", .ptrVal head)]) m π =
        evalExpr (.lit .nullptr)
          ([("cur", .ptrVal head), ("prev", .ptrVal none),
            ("head", .ptrVal head)]) :=
      memEvalExpr_lit _ _ _ _
    have vN : evalExpr (.lit .nullptr)
        ([("cur", .ptrVal head), ("prev", .ptrVal none),
          ("head", .ptrVal head)]) =
        .ok (.ptrVal none) := by simp [evalExpr, litVal]
    have hN := memEvalStmtFuel_let_pure F "next" nodeTy (.lit .nullptr)
      _ _ _ (.ptrVal none)
      (by simp) (by simp) (by simp) (by simp) eN vN
    have hretE : memEvalExpr (.var "head")
        (mkListUniqueEnv hd' prev' none nxt') m' π =
        evalExpr (.var "head")
          (mkListUniqueEnv hd' prev' none nxt') :=
      memEvalExpr_var _ _ _ _
    have hretV : evalExpr (.var "head")
        (mkListUniqueEnv hd' prev' none nxt') =
        .ok (.ptrVal hd') :=
      evalExpr_var_hit _ _ _ (mkListUniqueEnv_head hd' prev' none nxt')
    have hret := memEvalStmtFuel_return F (.var "head")
      (mkListUniqueEnv hd' prev' none nxt') m' π _ hretE hretV
    have hbody : listUniqueFunc.body = listUniqueBody := rfl
    rw [hbody]
    have hRest2 := memEvalStmtFuel_seq_fallthrough_trans F
      listUniqueLoop (.return_ (.var "head"))
      (mkListUniqueEnv head none head none) m π
      (mkListUniqueEnv hd' prev' none nxt') m' π _
      hloop' hret
    have hRest1 := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "next" nodeTy (.lit .nullptr))
      (.seq listUniqueLoop (.return_ (.var "head")))
      ([("cur", .ptrVal head), ("prev", .ptrVal none),
        ("head", .ptrVal head)]) m π
      (mkListUniqueEnv head none head none) m π _
      hN hRest2
    have hRest0 := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "head"))
      (.seq (.let_ "next" nodeTy (.lit .nullptr))
        (.seq listUniqueLoop (.return_ (.var "head"))))
      ([("prev", .ptrVal none),
        ("head", .ptrVal head)]) m π
      ([("cur", .ptrVal head), ("prev", .ptrVal none),
        ("head", .ptrVal head)]) m π _
      hB hRest1
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "prev" nodeTy (.lit .nullptr))
      (.seq (.let_ "cur" nodeTy (.var "head"))
        (.seq (.let_ "next" nodeTy (.lit .nullptr))
          (.seq listUniqueLoop (.return_ (.var "head")))))
      ([("head", .ptrVal head)]) m π
      ([("prev", .ptrVal none),
        ("head", .ptrVal head)]) m π _
      hA hRest0
    exact ⟨dropped', _, hTop, hlist, hdead'⟩
