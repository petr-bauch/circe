/-
Circe.Emit.LinkedReverse — L-slice raw-pointer in-place list reversal:
the `list_reverse` entry.

The corpus (`tests/cpp/linked_reverse.cpp`: `Node { val, next }`,
entry `Node *list_reverse(Node *head)`, caller-owned nodes, no
allocation in the entry) captures the classic three-pointer swing:
seed `prev = nullptr` / `cur = head`, then `while_ cur != nullptr`
with body `nxt = cur->next` (link load), `cur->next = prev` (link
swing), advances. The body carries no guards — the link ops are
loud on their own (null, missing, dead, or short block) — and the
only branch is the drain condition.

Pointers cross the boundary as opaque node capabilities (`ptrVal`,
`Option Addr` with `none` null: L3a): equality, `pgetNext`, and
`psetNext` only — no arithmetic, no casts. Addresses resolve
through the block's own tag, so the layout stays empty (no pins).
Termination is by fuel lockstep, not by measure: the forward threads
the same fuel as the evaluator (`while_` is the only consumer, one
per iteration; zero fuel exits cleanly on a null cursor and aborts
loudly on a live one — the S3a fuel contract). Cyclic input simply
exhausts fuel (no visited set is needed — the chase is purely
structural on fuel), and agreement with native is pinned by spec
edges plus the Diff fuzz (J precedent).
-/
import Circe.Mem.LinkedList

/-! ## L: `list_reverse` entry -/

/-- Mangled name of the reversal entry. -/
def linkRevName : String :=
  "_Z12list_reverseP4Node"

/-- Nominal node-pointer type (documentary: `bindArgs` checks arity
    only): payload `i32`, encoded link `u32`. -/
def nodeTy : CType :=
  .struct "Node" [.i 32, .u 32]

/-- The fused entry seed: null predecessor, head cursor, null spare
    (the G5a init-all-loop-vars convention). -/
def linkRevSeed : CStmt :=
  .seq (.let_ "prev" nodeTy (.lit .nullptr))
  (.seq (.let_ "cur" nodeTy (.var "head"))
  (.let_ "nxt" nodeTy (.lit .nullptr)))

/-- One chase iteration: link read, link swing to the predecessor,
    predecessor advance, chase advance. -/
def linkRevBody : CStmt :=
  .seq (.assign "nxt" (.pgetNext (.var "cur")))
  (.seq (.psetNext (.var "cur") (.var "prev"))
  (.seq (.assign "prev" (.var "cur"))
    (.assign "cur" (.var "nxt"))))

/-- The chase: `cur != nullptr`. -/
def linkRevOuter : CStmt :=
  .while_ (.une (.var "cur") (.lit .nullptr)) linkRevBody

/-- Canonical CoreIR for `list_reverse`: the seed, the chase, and the
    new-head return. -/
def linkRevFunc : Func :=
  ⟨linkRevName,
   [{ name := "head", ty := nodeTy, role := .owned }],
   nodeTy,
   (.seq linkRevSeed (.seq linkRevOuter (.return_ (.var "prev"))))⟩

/-- Chase environment: the four capability slots (the layout stays
    empty — link ops resolve through the block's own tag). -/
def mkLinkRevEnv (head prev cur nxt : Option Addr) : Env :=
  [("nxt", .ptrVal nxt), ("cur", .ptrVal cur),
   ("prev", .ptrVal prev), ("head", .ptrVal head)]

theorem mkLinkRevEnv_nxt (head prev cur nxt : Option Addr) :
    envLookup (mkLinkRevEnv head prev cur nxt) "nxt" =
      some (.ptrVal nxt) := by
  simp [mkLinkRevEnv, envLookup]

theorem mkLinkRevEnv_cur (head prev cur nxt : Option Addr) :
    envLookup (mkLinkRevEnv head prev cur nxt) "cur" =
      some (.ptrVal cur) := by
  simp [mkLinkRevEnv, envLookup,
    show ("nxt" : String) ≠ "cur" by decide]

theorem mkLinkRevEnv_prev (head prev cur nxt : Option Addr) :
    envLookup (mkLinkRevEnv head prev cur nxt) "prev" =
      some (.ptrVal prev) := by
  simp [mkLinkRevEnv, envLookup,
    show ("nxt" : String) ≠ "prev" by decide,
    show ("cur" : String) ≠ "prev" by decide]

theorem mkLinkRevEnv_head (head prev cur nxt : Option Addr) :
    envLookup (mkLinkRevEnv head prev cur nxt) "head" =
      some (.ptrVal head) := by
  simp [mkLinkRevEnv, envLookup,
    show ("nxt" : String) ≠ "head" by decide,
    show ("cur" : String) ≠ "head" by decide,
    show ("prev" : String) ≠ "head" by decide]

/-! ## Fuel-threaded chase forward -/

/-- Chase forward: mirrors `linkRevOuter` iteration for iteration
    (same fuel, same memory ops, same order). Zero fuel exits cleanly
    on a null cursor and aborts loudly on a live one — the S3a fuel
    contract. -/
def linkRevOuterFwd (F : Nat) (m : Mem) (prev cur : Option Addr) :
    Result (Mem × Option Addr) :=
  match F with
  | 0 =>
    match cur with
    | none => .ok (m, prev)
    | some _ => .error .AssertFail
  | F + 1 =>
    match cur with
    | none => .ok (m, prev)
    | some a =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 1 with
        | .error e => .error e
        | .ok w =>
          match memStore m a b.tag 1 (linkWord prev) with
          | .error e => .error e
          | .ok m' => linkRevOuterFwd F m' cur (addrOfWord w)

/-- Entry mirror: seed the predecessor and cursor, then the chase;
    the predecessor is the return. -/
def linkRevFwd (F : Nat) (m : Mem) (head : Option Addr) :
    Result (Mem × Option Addr) :=
  linkRevOuterFwd F m none head

/-! ## Body agreement -/

/-- One chase iteration with a live cursor: link read, swing to the
    predecessor, advances (any fuel). -/
theorem linkRevBody_ok (F : Nat) (m : Mem) (π : Layout)
    (head prev : Option Addr) (a : Addr) (nxt₀ nxt : Option Addr)
    (b : Block) (w : BitVec 32) (m' : Mem)
    (hfind : memFind m a = some b)
    (hmem : memLoad m a b.tag 1 = .ok w)
    (hstore : memStore m a b.tag 1 (linkWord prev) = .ok m')
    (hdec : addrOfWord w = nxt) :
    memEvalStmtFuel F linkRevBody
      (mkLinkRevEnv head prev (some a) nxt₀) m π =
      .ok (((mkLinkRevEnv head (some a) nxt nxt, m', π)),
        .fellThrough) := by
  have hbody : linkRevBody =
      .seq (.assign "nxt" (.pgetNext (.var "cur")))
      (.seq (.psetNext (.var "cur") (.var "prev"))
      (.seq (.assign "prev" (.var "cur"))
        (.assign "cur" (.var "nxt")))) := rfl
  have hcur : memEvalExpr (.var "cur")
      (mkLinkRevEnv head prev (some a) nxt₀) m π =
      .ok (.ptrVal (some a)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _
      (mkLinkRevEnv_cur head prev (some a) nxt₀)
  have hget : memEvalExpr (.pgetNext (.var "cur"))
      (mkLinkRevEnv head prev (some a) nxt₀) m π =
      .ok (.ptrVal nxt) := by
    have h := memEvalExpr_pgetNext_hit (.var "cur")
      (mkLinkRevEnv head prev (some a) nxt₀) m π a w b
      hcur hfind hmem
    rw [hdec] at h
    exact h
  have huN : envUpdate
      (mkLinkRevEnv head prev (some a) nxt₀) "nxt" (.ptrVal nxt) =
      some (mkLinkRevEnv head prev (some a) nxt) := by
    simp [mkLinkRevEnv, envUpdate]
  have hassignN := memEvalStmtFuel_assign_mem F "nxt"
    (.pgetNext (.var "cur"))
    (mkLinkRevEnv head prev (some a) nxt₀) m π _ _ hget huN
  have hcur1 : memEvalExpr (.var "cur")
      (mkLinkRevEnv head prev (some a) nxt) m π =
      .ok (.ptrVal (some a)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkLinkRevEnv,
        show ("nxt" : String) ≠ "cur" by decide])
  have hprev1 : memEvalExpr (.var "prev")
      (mkLinkRevEnv head prev (some a) nxt) m π =
      .ok (.ptrVal prev) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkLinkRevEnv,
        show ("nxt" : String) ≠ "prev" by decide,
        show ("cur" : String) ≠ "prev" by decide])
  have hswing := memEvalStmtFuel_psetNext_ok F
    (.var "cur") (.var "prev")
    (mkLinkRevEnv head prev (some a) nxt) m π a prev b m'
    hcur1 hprev1 hfind hstore
  have hcur2 : evalExpr (.var "cur")
      (mkLinkRevEnv head prev (some a) nxt) =
      .ok (.ptrVal (some a)) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkLinkRevEnv,
        show ("nxt" : String) ≠ "cur" by decide])
  have huP : envUpdate
      (mkLinkRevEnv head prev (some a) nxt) "prev"
      (.ptrVal (some a)) =
      some (mkLinkRevEnv head (some a) (some a) nxt) := by
    simp [mkLinkRevEnv, envUpdate,
      show ("nxt" : String) ≠ "prev" by decide,
      show ("cur" : String) ≠ "prev" by decide]
  have hassignP := memEvalStmtFuel_assign F "prev" (.var "cur")
    (mkLinkRevEnv head prev (some a) nxt) m' π _ _
    (memEvalExpr_var "cur" _ _ _) hcur2 huP
  have hnxt : evalExpr (.var "nxt")
      (mkLinkRevEnv head (some a) (some a) nxt) =
      .ok (.ptrVal nxt) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkLinkRevEnv])
  have huC : envUpdate
      (mkLinkRevEnv head (some a) (some a) nxt) "cur"
      (.ptrVal nxt) =
      some (mkLinkRevEnv head (some a) nxt nxt) := by
    simp [mkLinkRevEnv, envUpdate,
      show ("nxt" : String) ≠ "cur" by decide]
  have hassignC := memEvalStmtFuel_assign F "cur" (.var "nxt")
    (mkLinkRevEnv head (some a) (some a) nxt) m' π _ _
    (memEvalExpr_var "nxt" _ _ _) hnxt huC
  have htail := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _ hassignP hassignC
  have hmid := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _ hswing htail
  rw [hbody]
  exact memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _ hassignN hmid

/-- One chase iteration with a dangling cursor aborts loudly. -/
theorem linkRevBody_miss (F : Nat) (m : Mem) (π : Layout)
    (head prev : Option Addr) (a : Addr) (nxt₀ : Option Addr)
    (hfind : memFind m a = none) :
    memEvalStmtFuel F linkRevBody
      (mkLinkRevEnv head prev (some a) nxt₀) m π =
      .error .AssertFail := by
  have hbody : linkRevBody =
      .seq (.assign "nxt" (.pgetNext (.var "cur")))
      (.seq (.psetNext (.var "cur") (.var "prev"))
      (.seq (.assign "prev" (.var "cur"))
        (.assign "cur" (.var "nxt")))) := rfl
  have hcur : memEvalExpr (.var "cur")
      (mkLinkRevEnv head prev (some a) nxt₀) m π =
      .ok (.ptrVal (some a)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _
      (mkLinkRevEnv_cur head prev (some a) nxt₀)
  have hpg := memEvalExpr_pgetNext_miss (.var "cur")
    (mkLinkRevEnv head prev (some a) nxt₀) m π a hcur hfind
  have hassign := memEvalStmtFuel_assign_err F "nxt"
    (.pgetNext (.var "cur"))
    (mkLinkRevEnv head prev (some a) nxt₀) m π .AssertFail hpg
  rw [hbody]
  exact memEvalStmtFuel_seq_err F _ _ _ _ _ _ hassign

/-- Pure mirror: pointer reversal is list reversal. -/
def linkRevMirror : List (BitVec 32) → List (BitVec 32) :=
  List.reverse

theorem linkRevMirror_eq (vs : List (BitVec 32)) :
    linkRevMirror vs = vs.reverse := rfl

/-- Loop invariant: chasing `cur` with reversed-prefix `done` in
    `prev` returns the full reversal. Induction on fuel; the stores
    frame both segments (heads stay outside each other's footprint by
    acyclicity `ListSeg_head_notin_tail` plus the carried disjointness). -/
theorem linkRevOuterFwd_invariant (F : Nat) :
    ∀ (m) (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (prev cur : Option Addr) (done rest : List (BitVec 32))
      (m' : Mem) (prev' : Option Addr),
    ListSeg m prev done.reverse →
    ListSeg m cur rest →
    (∀ b c, SegMem (m := m) prev b → SegMem (m := m) cur c → b ≠ c) →
    linkRevOuterFwd F m prev cur = .ok (m', prev') →
    ListSeg m' prev' (done ++ rest).reverse := by
  induction F with
  | zero =>
    intro m hex prev cur done rest m' prev' hprev hcur hdisj hf
    cases cur with
    | none =>
      simp only [linkRevOuterFwd] at hf
      cases hf
      cases hcur with
      | nil =>
        simpa using hprev
    | some a =>
      simp only [linkRevOuterFwd] at hf
      cases hf
  | succ F ih =>
    intro m hex prev cur done rest m' prev' hprev hcur hdisj hf
    cases cur with
    | none =>
      simp only [linkRevOuterFwd] at hf
      cases hf
      cases hcur with
      | nil =>
        simpa using hprev
    | some a =>
      cases hcur with
      | cons hnode t2 =>
        obtain ⟨v', n', rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        have hfb : memFind m a = some _ := hnode
        have hmem : memLoad m a _ 1 = .ok _ := nodeLoadNext hnode
        simp only [linkRevOuterFwd, hfb, hmem] at hf
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode hf
        cases hst : memStore m a t' 1 (linkWord prev) with
        | error e =>
          simp [hst] at hf
        | ok m'' =>
          simp only [hst] at hf
          have hndec := nodeAt_link_roundtrip hnode hex
            (ListSeg_tail_alloc t2)
          rw [hndec] at hf
          have ha : (memFind m a).isSome = true := by simp [hfb]
          have hhex : ∀ x, (memFind m'' x).isSome = true → x + 1 < 2 ^ 32 :=
            hex_store hex hst ha
          -- A. swung node (Lemma A: the store lands the link).
          have hnode' : nodeAt m'' a t' v' prev :=
            nodeStoreNext_nodeAt hnode hst
          -- Cur-side self-membership (for disjointness use).
          have hcur_self : SegMem (m := m) (some a) a :=
            SegMem.here hnode
          -- B. prev-frame: old prefix survives (heads outside footprint).
          have hout_prev : ∀ b, SegMem (m := m) prev b → b ≠ a := by
            intro b hb hab
            exact hdisj b a hb hcur_self hab
          have hrev : (done ++ [v']).reverse = v' :: done.reverse := by
            simp
          have hprevF : ListSeg m'' prev done.reverse :=
            ListSeg.store_other hprev hst hout_prev
          have hprevC : ListSeg m'' (some a) ((done ++ [v']).reverse) := by
            rw [hrev]
            exact ListSeg.cons hnode' hprevF
          -- C. tail-frame: old tail survives (acyclicity).
          have hout_tail : ∀ b, SegMem (m := m) n' b → b ≠ a :=
            ListSeg_head_notin_tail hnode t2 hex
          have hcur' : ListSeg m'' n' vs' :=
            ListSeg.store_other t2 hst hout_tail
          -- Avoidance: the stored head is in neither post-footprint.
          have havoidMN : ∀ b, SegMem (m := m) n' b → b ≠ a :=
            ListSeg_head_notin_tail hnode t2 hex
          have hheadN : ∀ y, n' = some y → y ≠ a := by
            intro y hy
            cases t2 with
            | nil => cases hy
            | cons hN tN =>
              cases hy
              have hmemY := SegMem.here hN
              have t2re := ListSeg.cons hN tN
              exact ListSeg_head_notin_tail hnode t2re hex _ hmemY
          have havoidN : ∀ b, SegMem (m := m'') n' b → b ≠ a :=
            SegMem_store_avoid hst t2 hex hhex hheadN havoidMN
          have hheadP : ∀ y, prev = some y → y ≠ a := by
            intro y hy hab
            subst y
            have hmemA : SegMem (m := m) prev a := by
              rw [hy]
              exact SegMem.here hnode
            exact (hdisj a a hmemA hcur_self) rfl
          have havoidMP : ∀ b, SegMem (m := m) prev b → b ≠ a := by
            intro b hb hab
            subst b
            exact (hdisj a a hb hcur_self) rfl
          have havoidP : ∀ b, SegMem (m := m'') prev b → b ≠ a :=
            SegMem_store_avoid hst hprev hex hhex hheadP havoidMP
          -- Allocatedness of the new prefix head (for uniqueness).
          have hprev_alloc : ∀ c, prev = some c →
              (memFind m'' c).isSome = true := by
            intro c hc
            cases hP : prev with
            | none =>
              rw [hP] at hc
              cases hc
            | some p =>
              rw [hP] at hc
              cases hc
              rw [hP] at hprevF
              exact ListSeg_head_alloc hprevF
          -- D. new disjointness: chase both sides, identify, lift.
          have hdisj' : ∀ b c, SegMem (m := m'') (some a) b →
              SegMem (m := m'') n' c → b ≠ c := by
            intro b c hb hc
            cases hb with
            | here hA =>
              exact Ne.symm (havoidN c hc)
            | there hA tail =>
              have hNA := nodeAt_link_unique hA hnode' hhex
                (SegMem_head_alloc tail) hprev_alloc
              rw [hNA] at tail
              have tailM := SegMem_of_store tail hst havoidP
              have hcM' := SegMem_of_store hc hst havoidN
              have hcM : SegMem (m := m) (some a) c :=
                SegMem.there hnode hcM'
              exact hdisj b c tailM hcM
          have hIH := ih m'' hhex (some a) n' (done ++ [v']) vs'
            m' prev' hprevC hcur' hdisj' hf
          simpa [List.append_assoc] using hIH

/-- Top-level reversal contract: chasing a whole segment returns its
    reversal (seed the predecessor with null). -/
theorem linkRevFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (vs : List (BitVec 32))
    (m' : Mem) (prev' : Option Addr)
    (hseg : ListSeg m head vs)
    (hfwd : linkRevFwd F m head = .ok (m', prev')) :
    ListSeg m' prev' vs.reverse := by
  have h := linkRevOuterFwd_invariant F m hex none head [] vs m' prev'
    ListSeg.nil hseg (fun b c hb _ => by cases hb) hfwd
  simpa using h

/-- Loop/evaluator agreement: `linkRevOuter` at any fuel agrees with
    the chase forward (same fuel, same memory ops, same order;
    the spare slot is existentially bound). -/
theorem linkRevOuter_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout) (head prev cur nxt₀ : Option Addr),
    ∃ nxt', memEvalStmtFuel F linkRevOuter
      (mkLinkRevEnv head prev cur nxt₀) m π =
      match linkRevOuterFwd F m prev cur with
      | .ok (m', prev') =>
        .ok (((mkLinkRevEnv head prev' none nxt', m', π)), .fellThrough)
      | .error e => .error e := by
  induction F with
  | zero =>
    intro m π head prev cur nxt₀
    cases cur with
    | none =>
      have hcur : memEvalExpr (.var "cur")
          (mkLinkRevEnv head prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkLinkRevEnv_cur _ _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkLinkRevEnv head prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkLinkRevEnv head prev none nxt₀) m π = .ok (.b false) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcur hnull
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
      have hw : memEvalStmtFuel 0 linkRevOuter
          (mkLinkRevEnv head prev none nxt₀) m π =
          .ok ((((mkLinkRevEnv head prev none nxt₀), m, π)),
            .fellThrough) :=
        memEvalStmtFuel_while_false _ _ linkRevBody _ _ _ hgF
      refine ⟨nxt₀, ?_⟩
      rw [hw]
      simp only [linkRevOuterFwd]
    | some a =>
      have hcur : memEvalExpr (.var "cur")
          (mkLinkRevEnv head prev (some a) nxt₀) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkLinkRevEnv_cur _ _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkLinkRevEnv head prev (some a) nxt₀) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkLinkRevEnv head prev (some a) nxt₀) m π =
          .ok (.b true) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
          hcur hnull
        have hbe : ((some a) != none) = true := by simp
        rw [hbe] at hg
        exact hg
      have hw : memEvalStmtFuel 0 linkRevOuter
          (mkLinkRevEnv head prev (some a) nxt₀) m π =
          .error .AssertFail := by
        simp only [linkRevOuter, memEvalStmtFuel, memEvalStmtZero,
          memEvalStmtWith, memEvalStmtZeroHandler, hgT]
      refine ⟨none, ?_⟩
      rw [hw]
      simp only [linkRevOuterFwd]
  | succ F ih =>
    intro m π head prev cur nxt₀
    cases cur with
    | none =>
      have hcur : memEvalExpr (.var "cur")
          (mkLinkRevEnv head prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkLinkRevEnv_cur _ _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkLinkRevEnv head prev none nxt₀) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkLinkRevEnv head prev none nxt₀) m π = .ok (.b false) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcur hnull
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
      have hw : memEvalStmtFuel (F + 1) linkRevOuter
          (mkLinkRevEnv head prev none nxt₀) m π =
          .ok ((((mkLinkRevEnv head prev none nxt₀), m, π)),
            .fellThrough) :=
        memEvalStmtFuel_while_false _ _ linkRevBody _ _ _ hgF
      refine ⟨nxt₀, ?_⟩
      rw [hw]
      simp only [linkRevOuterFwd]
    | some a =>
      have hcur : memEvalExpr (.var "cur")
          (mkLinkRevEnv head prev (some a) nxt₀) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkLinkRevEnv_cur _ _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkLinkRevEnv head prev (some a) nxt₀) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkLinkRevEnv head prev (some a) nxt₀) m π =
          .ok (.b true) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
          hcur hnull
        have hbe : ((some a) != none) = true := by simp
        rw [hbe] at hg
        exact hg
      have hw := memEvalStmtFuel_while_true F
        (.une (.var "cur") (.lit .nullptr)) linkRevBody _ _ _ hgT
      simp only [linkRevOuter] at hw ⊢
      rw [hw]
      cases hF : memFind m a with
      | none =>
        have hb := linkRevBody_miss F m π head prev a nxt₀ hF
        refine ⟨none, ?_⟩
        rw [hb]
        simp only [linkRevOuterFwd, hF]
      | some b =>
        cases hL : memLoad m a b.tag 1 with
        | error werr =>
          have hpg := memEvalExpr_pgetNext_err (.var "cur")
            (mkLinkRevEnv head prev (some a) nxt₀) m π a b werr
            hcur hF hL
          have hassign := memEvalStmtFuel_assign_err F "nxt"
            (.pgetNext (.var "cur"))
            (mkLinkRevEnv head prev (some a) nxt₀) m π werr hpg
          have hbody : linkRevBody =
              .seq (.assign "nxt" (.pgetNext (.var "cur")))
              (.seq (.psetNext (.var "cur") (.var "prev"))
              (.seq (.assign "prev" (.var "cur"))
                (.assign "cur" (.var "nxt")))) := rfl
          have hb : memEvalStmtFuel F linkRevBody
              (mkLinkRevEnv head prev (some a) nxt₀) m π =
              .error werr := by
            rw [hbody]
            exact memEvalStmtFuel_seq_err F _ _ _ _ _ _ hassign
          refine ⟨none, ?_⟩
          rw [hb]
          simp only [linkRevOuterFwd, hF, hL]
        | ok w =>
          cases hS : memStore m a b.tag 1 (linkWord prev) with
          | error e =>
            have hpg := memEvalExpr_pgetNext_hit (.var "cur")
              (mkLinkRevEnv head prev (some a) nxt₀) m π a w b
              hcur hF hL
            have huN : envUpdate
                (mkLinkRevEnv head prev (some a) nxt₀) "nxt"
                (.ptrVal (addrOfWord w)) =
                some (mkLinkRevEnv head prev (some a)
                  (addrOfWord w)) := by
              simp [mkLinkRevEnv, envUpdate]
            have hassignN := memEvalStmtFuel_assign_mem F "nxt"
              (.pgetNext (.var "cur"))
              (mkLinkRevEnv head prev (some a) nxt₀) m π _ _ hpg huN
            have hcur1 : memEvalExpr (.var "cur")
                (mkLinkRevEnv head prev (some a) (addrOfWord w)) m π =
                .ok (.ptrVal (some a)) := by
              rw [memEvalExpr_var]
              exact evalExpr_var_hit _ _ _ (by
                simp [envLookup, mkLinkRevEnv])
            have hprev1 : memEvalExpr (.var "prev")
                (mkLinkRevEnv head prev (some a) (addrOfWord w)) m π =
                .ok (.ptrVal prev) := by
              rw [memEvalExpr_var]
              exact evalExpr_var_hit _ _ _ (by
                simp [envLookup, mkLinkRevEnv])
            have hswing := memEvalStmtFuel_psetNext_err F
              (.var "cur") (.var "prev")
              (mkLinkRevEnv head prev (some a) (addrOfWord w))
              m π a prev b e hcur1 hprev1 hF hS
            have hbody : linkRevBody =
                .seq (.assign "nxt" (.pgetNext (.var "cur")))
                (.seq (.psetNext (.var "cur") (.var "prev"))
                (.seq (.assign "prev" (.var "cur"))
                  (.assign "cur" (.var "nxt")))) := rfl
            have hb : memEvalStmtFuel F linkRevBody
                (mkLinkRevEnv head prev (some a) nxt₀) m π =
                .error e := by
              rw [hbody]
              have h1 := memEvalStmtFuel_seq_fallthrough F
                (.assign "nxt" (.pgetNext (.var "cur")))
                (.seq (.psetNext (.var "cur") (.var "prev"))
                (.seq (.assign "prev" (.var "cur"))
                  (.assign "cur" (.var "nxt"))))
                _ _ _ _ _ _ hassignN
              rw [h1]
              exact memEvalStmtFuel_seq_err F _ _ _ _ _ _ hswing
            refine ⟨none, ?_⟩
            rw [hb]
            simp only [linkRevOuterFwd, hF, hL, hS]
          | ok m' =>
            have hb := linkRevBody_ok F m π head prev a nxt₀
              (addrOfWord w) b w m' hF hL hS rfl
            obtain ⟨nxt', hIH⟩ := ih m' π head (some a)
              (addrOfWord w) (addrOfWord w)
            simp only [linkRevOuter] at hIH
            refine ⟨nxt', ?_⟩
            simp only [hb]
            rw [hIH]
            simp only [linkRevOuterFwd, hF, hL, hS]

/-- Entry Hoare triple (thin sugar): the seeded chase returns the
    reversal — seed, loop (bridge), return, then the pure contract. -/
theorem linkRevFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (vs : List (BitVec 32))
    (m' : Mem) (prev' : Option Addr)
    (hseg : ListSeg m head vs)
    (hfwd : linkRevFwd F m head = .ok (m', prev')) :
    ∃ ρ', memEvalStmtFuel F linkRevFunc.body
      [("head", .ptrVal head)] m π =
      .ok ((ρ', m', π), .returned (.ptrVal prev')) ∧
      ListSeg m' prev' vs.reverse := by
  have hseg' := linkRevFwd_correct F m hex head vs m' prev' hseg hfwd
  simp only [linkRevFwd] at hfwd
  -- Seed: three lets build the chase environment.
  have hseed : memEvalStmtFuel F linkRevSeed [("head", .ptrVal head)] m π =
      .ok ((mkLinkRevEnv head none head none, m, π), .fellThrough) := by
    have hsu : linkRevSeed = .seq (.let_ "prev" nodeTy (.lit .nullptr))
        (.seq (.let_ "cur" nodeTy (.var "head"))
          (.let_ "nxt" nodeTy (.lit .nullptr))) := rfl
    rw [hsu]
    have eP : memEvalExpr (.lit .nullptr) [("head", .ptrVal head)] m π =
        evalExpr (.lit .nullptr) [("head", .ptrVal head)] :=
      memEvalExpr_lit _ _ _ _
    have vP : evalExpr (.lit .nullptr) [("head", .ptrVal head)] =
        .ok (.ptrVal none) := by simp [evalExpr, litVal]
    have hL1 := memEvalStmtFuel_let_pure F "prev" nodeTy
      (.lit .nullptr) _ _ _ (.ptrVal none)
      (by simp) (by simp) (by simp) eP vP
    have eC : memEvalExpr (.var "head")
        [("prev", .ptrVal none), ("head", .ptrVal head)] m π =
        evalExpr (.var "head")
          [("prev", .ptrVal none), ("head", .ptrVal head)] :=
      memEvalExpr_var _ _ _ _
    have vC : evalExpr (.var "head")
        [("prev", .ptrVal none), ("head", .ptrVal head)] =
        .ok (.ptrVal head) :=
      evalExpr_var_hit _ _ _ (by simp [envLookup])
    have hL2 := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
      _ _ _ (.ptrVal head) (by simp) (by simp) (by simp) eC vC
    have eN : memEvalExpr (.lit .nullptr)
        [("cur", .ptrVal head), ("prev", .ptrVal none),
          ("head", .ptrVal head)] m π =
        evalExpr (.lit .nullptr)
          [("cur", .ptrVal head), ("prev", .ptrVal none),
            ("head", .ptrVal head)] :=
      memEvalExpr_lit _ _ _ _
    have vN : evalExpr (.lit .nullptr)
        [("cur", .ptrVal head), ("prev", .ptrVal none),
          ("head", .ptrVal head)] = .ok (.ptrVal none) := by
      simp [evalExpr, litVal]
    have hL3 := memEvalStmtFuel_let_pure F "nxt" nodeTy (.lit .nullptr)
      _ _ _ (.ptrVal none) (by simp) (by simp) (by simp) eN vN
    have s1 := memEvalStmtFuel_seq_fallthrough F
      (.let_ "prev" nodeTy (.lit .nullptr))
      (.seq (.let_ "cur" nodeTy (.var "head"))
        (.let_ "nxt" nodeTy (.lit .nullptr)))
      _ _ _ _ _ _ hL1
    rw [s1]
    have s2 := memEvalStmtFuel_seq_fallthrough F
      (.let_ "cur" nodeTy (.var "head"))
      (.let_ "nxt" nodeTy (.lit .nullptr))
      _ _ _ _ _ _ hL2
    rw [s2]
    exact hL3
  -- Loop: the bridge fires the forward.
  obtain ⟨nxt', hloop⟩ := linkRevOuter_agree F m π head none head none
  rw [hfwd] at hloop
  -- Return: the predecessor slot.
  have hretE : memEvalExpr (.var "prev")
      (mkLinkRevEnv head prev' none nxt') m' π =
      evalExpr (.var "prev") (mkLinkRevEnv head prev' none nxt') :=
    memEvalExpr_var _ _ _ _
  have hretV : evalExpr (.var "prev")
      (mkLinkRevEnv head prev' none nxt') = .ok (.ptrVal prev') :=
    evalExpr_var_hit _ _ _ (mkLinkRevEnv_prev _ _ _ _)
  have hret := memEvalStmtFuel_return F (.var "prev")
    (mkLinkRevEnv head prev' none nxt') m' π _ hretE hretV
  -- Compose: seed, loop, return.
  have hbody : linkRevFunc.body =
      .seq linkRevSeed
        (.seq linkRevOuter (.return_ (.var "prev"))) := rfl
  have heval : memEvalStmtFuel F linkRevFunc.body
      [("head", .ptrVal head)] m π =
      .ok ((mkLinkRevEnv head prev' none nxt', m', π),
        .returned (.ptrVal prev')) := by
    rw [hbody]
    have c1 := memEvalStmtFuel_seq_fallthrough F linkRevSeed
      (.seq linkRevOuter (.return_ (.var "prev")))
      _ _ _ _ _ _ hseed
    rw [c1]
    have c2 := memEvalStmtFuel_seq_fallthrough F linkRevOuter
      (.return_ (.var "prev")) _ _ _ _ _ _ hloop
    rw [c2]
    exact hret
  exact ⟨_, heval, hseg'⟩
