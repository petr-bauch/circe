import Circe.Emit.LinkedReverse

/-- Pillar-1 goal #3: first-match query (`list_find`, read-only
    traversal leg reusing the chase kit). `Node *list_find(Node
    *head, int val)` chases with a single cursor and returns the
    first node whose payload matches — `nullptr` on miss. No
    stores to the chain, no `malloc`, no `free`: the loop guard,
    not a branch, covers misses; faults are loud. -/
def listFindName : String :=
  "_Z9list_findP4Nodei"

/-- The chase-loop body (guard, hit-or-step): named so the
    agreement proof can rewrite it without literals. -/
def listFindLoopBody : CStmt :=
  (.seq (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
            (.return_ (.var "cur"))
            .skip)
    (.assign "cur" (.pgetNext (.var "cur"))))

/-- The chase loop (isolated for the loop/evaluator
    agreement: guard, hit-or-step body). -/
def listFindLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) listFindLoopBody)

/-- Canonical CoreIR for `list_find`: seed the cursor, chase
    while `cur != nullptr`, return the hit cursor early,
    return null on exhaustion. -/
def listFindBody : CStmt :=
  (.seq (.let_ "cur" nodeTy (.var "head"))
    (.seq listFindLoop (.return_ (.lit .nullptr))))

/-- The find entry: `Node*` + `i32` in, `Node*` out (found node
    or null). -/
def listFindFunc : Func :=
  ⟨listFindName,
   [{ name := "head", ty := nodeTy, role := .owned },
    { name := "val", ty := (.i 32), role := .owned }],
   nodeTy,
   listFindBody⟩

/-- Find environment: head and payload slots, then the cursor
    slot (the entry binds `head` and `val` first, then the let
    conses `cur` on the front). -/
def mkListFindEnv (head : Option Addr) (v : BitVec 32)
    (cur : Option Addr) : Env :=
  [("cur", .ptrVal cur), ("head", .ptrVal head), ("val", .i32 v)]

theorem mkListFindEnv_cur (head : Option Addr) (v : BitVec 32)
    (cur : Option Addr) :
    envLookup (mkListFindEnv head v cur) "cur" =
      some (.ptrVal cur) := by
  simp [mkListFindEnv, envLookup]

theorem mkListFindEnv_head (head : Option Addr) (v : BitVec 32)
    (cur : Option Addr) :
    envLookup (mkListFindEnv head v cur) "head" =
      some (.ptrVal head) := by
  simp [mkListFindEnv, envLookup]

theorem mkListFindEnv_val (head : Option Addr) (v : BitVec 32)
    (cur : Option Addr) :
    envLookup (mkListFindEnv head v cur) "val" =
      some (.i32 v) := by
  simp [mkListFindEnv, envLookup]

/-! ## Forward mirror (read-only chase, found node or null) -/

/-- Chase for the first payload hit: read-only (each step reads
    the payload at `[0]` and the link at `[1]`), returning the
    match (`none` on exhaustion). Misses, dangling links, and
    short blocks abort loudly at any fuel; each visit consumes
    fuel (like the evaluator's loop iteration — a hit needs
    fuel too). -/
def listFindChase (F : Nat) (m : Mem) (cur : Option Addr)
    (v : BitVec 32) : Result (Option Addr) :=
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
          if w == v then .ok (some a)
          else match memLoad m a b.tag 1 with
               | .error e => .error e
               | .ok w' => listFindChase F m (addrOfWord w') v

/-- Entry mirror: chase to the first payload hit. -/
def listFindFwd (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) : Result (Option Addr) :=
  listFindChase F m head v

/-- The chase succeeds on a fueled segment (faults ruled out by
    the segment hypotheses, exhaustion by fuel). -/
theorem listFindChase_ok (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (v : BitVec 32) (cur : Option Addr)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hlen : suf.length ≤ F),
    ∃ cur', listFindChase F m cur v = .ok cur' := by
  induction F with
  | zero =>
    intro m hex v cur suf hseg hlen
    cases cur with
    | none => exact ⟨none, by simp [listFindChase]⟩
    | some a =>
      cases hseg with
      | cons _ t2 =>
        obtain ⟨vs', rfl⟩ := listSegVals t2
        exact False.elim (by
          simp only [List.length_cons] at hlen
          omega)
  | succ F ih =>
    intro m hex v cur suf hseg hlen
    cases cur with
    | none => exact ⟨none, by simp [listFindChase]⟩
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
        · exact ⟨some a, by
            unfold listFindChase
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
          obtain ⟨c', hC'⟩ :=
            ih m hex v nxt vs' t2 hlen'
          exact ⟨c', by
            unfold listFindChase
            simp only [hfb, hmem0, hmem1, if_neg heq2, hdec, hC']⟩

/-- The forward mirror is correct: a hit returns a chain node
    holding the payload, a miss means the payload is absent.
    Direct induction on fuel (no surgery — the chase is
    read-only and the result is the chase result). -/
theorem listFindFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hlen : vs.length ≤ F)
    (hfwd : listFindFwd F m head v = .ok hd') :
    (∀ c, hd' = some c → ∃ t n, nodeAt m c t v n) ∧
      (hd' = none → v ∉ vs) := by
  induction F generalizing head vs with
  | zero =>
    cases hseg with
    | nil =>
      simp only [listFindFwd, listFindChase] at hfwd
      simp only [Except.ok.injEq] at hfwd
      subst hd'
      refine ⟨?_, ?_⟩
      · intro c hcon
        cases hcon
      · intro _ hmem
        exact List.not_mem_nil hmem
    | cons hnode t2 =>
      obtain ⟨vs', rfl⟩ := listSegVals t2
      simp only [List.length_cons] at hlen
      omega
  | succ F ih =>
    cases hseg with
    | nil =>
      simp only [listFindFwd, listFindChase] at hfwd
      simp only [Except.ok.injEq] at hfwd
      subst hd'
      refine ⟨?_, ?_⟩
      · intro c hcon
        cases hcon
      · intro _ hmem
        exact List.not_mem_nil hmem
    | cons hnode t2 =>
      obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
      obtain ⟨vs', rfl⟩ := listSegVals t2
      obtain ⟨t', heq⟩ := nodeAt_tag hnode
      rw [← heq] at hnode
      have hfb : memFind m _ = some _ := hnode
      have hmem0 : memLoad m _ t' 0 = .ok _ := nodeLoadVal hnode
      have hmem1 : memLoad m _ t' 1 = .ok _ := nodeLoadNext hnode
      by_cases heq2 : (v₀ == v) = true
      · simp only [listFindFwd, listFindChase, hfb, hmem0,
          hmem1, if_pos heq2] at hfwd
        simp only [Except.ok.injEq] at hfwd
        subst hd'
        have hvv : v₀ = v := beq_iff_eq.mp heq2
        rw [hvv] at hnode
        refine ⟨?_, ?_⟩
        · intro c hcon
          cases hcon
          exact ⟨t', nxt, hnode⟩
        · intro hcon
          cases hcon
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
        simp only [listFindFwd, listFindChase, hfb, hmem0,
          hmem1, if_neg heq2, hdec] at hfwd
        have hfwd' : listFindFwd F m nxt v = .ok hd' := hfwd
        have hIH := ih nxt vs' t2 hlen' hfwd'
        refine ⟨hIH.1, fun hcon hmem => ?_⟩
        have hnev : v₀ ≠ v := fun heq => heq2 (by rw [heq]; simp)
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl h => exact hnev h.symm
        | inr h => exact hIH.2 hcon h

/-- Loop/evaluator agreement: the find loop evaluates exactly
    as the read-only chase directs — miss falls through with
    the cursor at null, hit returns the cursor early. No unlink
    equations (the entry mirror is the chase itself, so the
    forward identification is direct). Induction on fuel, reusing
    the chase-ok skeleton (segment hypotheses rule out faults;
    fuel rules out exhaustion). -/
theorem listFindLoop_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (head : Option Addr) (v : BitVec 32)
      (cur : Option Addr)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hlen : suf.length ≤ F)
      (cur' : Option Addr)
      (hC : listFindChase F m cur v = .ok cur'),
    (cur' = none →
      memEvalStmtFuel F listFindLoop (mkListFindEnv head v cur) m π =
        .ok ((mkListFindEnv head v none, m, π), .fellThrough)) ∧
    (∀ c, cur' = some c →
      memEvalStmtFuel F listFindLoop (mkListFindEnv head v cur) m π =
        .ok ((mkListFindEnv head v (some c), m, π),
          .returned (.ptrVal (some c)))) := by
  induction F with
  | zero =>
    intro m π hex head v cur suf hseg hlen cur' hC
    cases cur with
    | none =>
      have hC' : listFindChase 0 m none v = .ok none := by
        simp [listFindChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      subst cur'
      refine ⟨?_, ?_⟩
      · intro _
        have hcurE : memEvalExpr (.var "cur") (mkListFindEnv head v none) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListFindEnv_cur _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr) (mkListFindEnv head v none) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListFindEnv head v none) m π = .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel 0 listFindLoop (mkListFindEnv head v none) m π =
            .ok ((mkListFindEnv head v none, m, π), .fellThrough) :=
          memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
        exact hw
      · intro c hcon
        cases hcon
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨vs', rfl⟩ := listSegVals t2
        simp only [List.length_cons] at hlen
        omega
  | succ F ih =>
    intro m π hex head v cur suf hseg hlen cur' hC
    cases cur with
    | none =>
      have hC' : listFindChase (F + 1) m none v = .ok none := by
        simp [listFindChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      subst cur'
      refine ⟨?_, ?_⟩
      · intro _
        have hcurE : memEvalExpr (.var "cur") (mkListFindEnv head v none) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListFindEnv_cur _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr) (mkListFindEnv head v none) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListFindEnv head v none) m π = .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel (F + 1) listFindLoop
            (mkListFindEnv head v none) m π =
            .ok ((mkListFindEnv head v none, m, π), .fellThrough) :=
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
        have hfb : memFind m _ = some _ := hnode
        have hmem0 : memLoad m _ t' 0 = .ok _ := nodeLoadVal hnode
        have hmem1 : memLoad m _ t' 1 = .ok _ := nodeLoadNext hnode
        have hcurE : memEvalExpr (.var "cur") (mkListFindEnv head v (some a)) m π =
            .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListFindEnv_cur _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkListFindEnv head v (some a)) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkListFindEnv head v (some a)) m π = .ok (.b true) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none hcurE hnullE
          have hbe : ((some a) != none) = true := by simp
          rw [hbe] at hg
          exact hg
        have hpget : memEvalExpr (.pgetVal (.var "cur"))
            (mkListFindEnv head v (some a)) m π =
            .ok (.i32 v₀) :=
          memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE hfb hmem0
        have hvalE : memEvalExpr (.var "val") (mkListFindEnv head v (some a)) m π =
            .ok (.i32 v) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (mkListFindEnv_val _ _ _)
        have hueq : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
            (mkListFindEnv head v (some a)) m π = .ok (.b (v₀ == v)) := by
          unfold memEvalExpr
          simp only [hpget, hvalE]
        by_cases heq2 : (v₀ == v) = true
        · have hC' : listFindChase (F + 1) m (some a) v =
              .ok (some a) := by
            unfold listFindChase
            simp only [hfb, hmem0, hmem1, if_pos heq2]
          rw [hC'] at hC
          simp only [Except.ok.injEq] at hC
          subst cur'
          have hvv : v₀ = v := beq_iff_eq.mp heq2
          subst v₀
          rw [heq2] at hueq
          refine ⟨?_, ?_⟩
          · intro hcon
            cases hcon
          · intro c hcon
            cases hcon
            have hueqT : memEvalExpr
                (.ueq (.pgetVal (.var "cur")) (.var "val"))
                (mkListFindEnv head v (some a)) m π =
                .ok (.b true) := hueq
            have hretE : memEvalExpr (.var "cur")
                (mkListFindEnv head v (some a)) m π =
                evalExpr (.var "cur")
                  (mkListFindEnv head v (some a)) :=
              memEvalExpr_var _ _ _ _
            have hretV : evalExpr (.var "cur")
                (mkListFindEnv head v (some a)) =
                .ok (.ptrVal (some a)) :=
              evalExpr_var_hit _ _ _ (mkListFindEnv_cur _ _ _)
            have hret := memEvalStmtFuel_return F (.var "cur")
              (mkListFindEnv head v (some a)) m π
              _ hretE hretV
            have hifOuter : memEvalStmtFuel F
                (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
                  (.return_ (.var "cur"))
                  .skip)
                (mkListFindEnv head v (some a)) m π =
                .ok (((mkListFindEnv head v (some a)), m, π),
                  .returned (.ptrVal (some a))) :=
              (memEvalStmtFuel_if_true F _ _ _ _ _ _ hueqT).trans hret
            have hbodyEv : memEvalStmtFuel F listFindLoopBody
                (mkListFindEnv head v (some a)) m π =
                .ok (((mkListFindEnv head v (some a)), m, π),
                  .returned (.ptrVal (some a))) :=
              memEvalStmtFuel_seq_return F _ _ _ _ _ _ _ _ _ hifOuter
            have hW : memEvalStmtFuel (F + 1) listFindLoop
                (mkListFindEnv head v (some a)) m π =
                .ok (((mkListFindEnv head v (some a)), m, π),
                  .returned (.ptrVal (some a))) := by
              have h := memEvalStmtFuel_while_true F _ listFindLoopBody _ _ _ hgT
              simp only [hbodyEv] at h
              exact h
            exact hW
        · have heqF : (v₀ == v) = false := by
            cases h : (v₀ == v) with
            | true => exact absurd h heq2
            | false => rfl
          have hueqF : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "val"))
              (mkListFindEnv head v (some a)) m π =
              .ok (.b false) := by
            rw [heqF] at hueq
            exact hueq
          have hskip : memEvalStmtFuel F .skip
              (mkListFindEnv head v (some a)) m π =
              .ok (((mkListFindEnv head v (some a)), m, π),
                .fellThrough) := by
            cases F <;> rfl
          have hifOuterF : memEvalStmtFuel F
              (.if_ (.ueq (.pgetVal (.var "cur")) (.var "val"))
                (.return_ (.var "cur"))
                .skip)
              (mkListFindEnv head v (some a)) m π =
              .ok (((mkListFindEnv head v (some a)), m, π),
                .fellThrough) :=
            (memEvalStmtFuel_if_false F _ _ _ _ _ _ hueqF).trans hskip
          have hcurE1 : memEvalExpr (.var "cur")
              (mkListFindEnv head v (some a)) m π =
              .ok (.ptrVal (some a)) := hcurE
          have hlinkE1 : memEvalExpr (.pgetNext (.var "cur"))
              (mkListFindEnv head v (some a)) m π =
              .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE1 hfb hmem1
          have hstep : memEvalStmtFuel F
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkListFindEnv head v (some a)) m π =
              .ok (((mkListFindEnv head v
                  (addrOfWord (linkWord nxt))), m, π),
                .fellThrough) :=
            memEvalStmtFuel_assign_mem F "cur" (.pgetNext (.var "cur"))
              (mkListFindEnv head v (some a)) m π _ _ hlinkE1
              (by simp [mkListFindEnv, envUpdate])
          have hbodyEv : memEvalStmtFuel F listFindLoopBody
              (mkListFindEnv head v (some a)) m π =
              .ok (((mkListFindEnv head v
                  (addrOfWord (linkWord nxt))), m, π),
                .fellThrough) :=
            memEvalStmtFuel_seq_fallthrough_trans F _ _
              (mkListFindEnv head v (some a)) _ _
              (mkListFindEnv head v (some a)) _ _ _
              hifOuterF hstep
          have hWh : memEvalStmtFuel (F + 1) listFindLoop
              (mkListFindEnv head v (some a)) m π =
              memEvalStmtFuel F listFindLoop
                (mkListFindEnv head v
                  (addrOfWord (linkWord nxt))) m π := by
            have h := memEvalStmtFuel_while_true F _ listFindLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          have hallocN : ∀ c'', nxt = some c'' →
              (memFind m c'').isSome = true := by
            intro c'' hc''
            cases hc''
            exact ListSeg_head_alloc t2
          have hdecN : addrOfWord (linkWord nxt) = nxt :=
            nodeAt_link_roundtrip hnode hex hallocN
          have t2' : ListSeg m (addrOfWord (linkWord nxt)) vs' := by
            rw [hdecN]
            exact t2
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          have hC'' : listFindChase F m (addrOfWord (linkWord nxt)) v =
              .ok cur' := by
            have hch := hC
            unfold listFindChase at hch
            simp only [hfb, hmem0, hmem1] at hch
            rw [if_neg heq2] at hch
            exact hch
          have hIH := ih m π hex head v (addrOfWord (linkWord nxt))
            vs' t2' hlen' cur' hC''
          refine ⟨?_, ?_⟩
          · intro hcon
            have hstep := hIH.1 hcon
            rw [hWh]
            exact hstep
          · intro c hcon
            have hev := hIH.2 c hcon
            rw [hWh]
            exact hev

/-- The find entry evaluates as the mirror and returns the
    first hit (null on miss). Seed let builds the chase
    environment, the loop agree fires the chase result
    (miss falls through to the final null return, hit
    returns early), and the forward contract supplies the
    node fact. -/
theorem listFindFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hlen : vs.length ≤ F)
    (hfwd : listFindFwd F m head v = .ok hd') :
    ∃ ρ', memEvalStmtFuel F listFindFunc.body
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      .ok ((ρ', m, π), .returned (.ptrVal hd')) ∧
      (∀ c, hd' = some c → ∃ t n, nodeAt m c t v n) ∧
        (hd' = none → v ∉ vs) := by
  have hsegF := listFindFwd_correct F m hex head v vs hd'
    hseg hlen hfwd
  obtain ⟨cur', hC⟩ :=
    listFindChase_ok F m hex v head vs hseg hlen
  have hloop := listFindLoop_agree F m π hex head v head vs
    hseg hlen cur' hC
  -- Seed: the cursor let builds the chase environment.
  have eC : memEvalExpr (.var "head")
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      evalExpr (.var "head")
        [("head", .ptrVal head), ("val", .i32 v)] :=
    memEvalExpr_var _ _ _ _
  have vC : evalExpr (.var "head")
      [("head", .ptrVal head), ("val", .i32 v)] =
      .ok (.ptrVal head) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hA := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
    _ _ _ (.ptrVal head)
    (by simp) (by simp) (by simp) (by simp) eC vC
  have hbody : listFindFunc.body = listFindBody := rfl
  rw [hbody]
  unfold listFindFwd at hfwd
  rw [hC] at hfwd
  simp only [Except.ok.injEq] at hfwd
  subst hd'
  cases cur' with
  | none =>
    have hmiss := hloop.1 rfl
    have hretE : memEvalExpr (.lit .nullptr)
        (mkListFindEnv head v none) m π =
        evalExpr (.lit .nullptr) (mkListFindEnv head v none) :=
      memEvalExpr_lit _ _ _ _
    have hretV : evalExpr (.lit .nullptr)
        (mkListFindEnv head v none) =
        .ok (.ptrVal none) := by simp [evalExpr, litVal]
    have hret := memEvalStmtFuel_return F (.lit .nullptr)
      (mkListFindEnv head v none) m π _ hretE hretV
    have hRest := memEvalStmtFuel_seq_fallthrough_trans F
      listFindLoop (.return_ (.lit .nullptr))
      (mkListFindEnv head v head) m π
      (mkListFindEnv head v none) m π _
      hmiss hret
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "head"))
      (.seq listFindLoop (.return_ (.lit .nullptr)))
      ([("head", .ptrVal head), ("val", .i32 v)]) m π
      (mkListFindEnv head v head) m π _
      hA hRest
    exact ⟨_, hTop, hsegF.1, hsegF.2⟩
  | some c =>
    have hev := hloop.2 c rfl
    have hRest := memEvalStmtFuel_seq_return F
      listFindLoop (.return_ (.lit .nullptr))
      (mkListFindEnv head v head) m π
      (mkListFindEnv head v (some c)) m π _ hev
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "head"))
      (.seq listFindLoop (.return_ (.lit .nullptr)))
      ([("head", .ptrVal head), ("val", .i32 v)]) m π
      (mkListFindEnv head v head) m π _
      hA hRest
    exact ⟨_, hTop, hsegF.1, hsegF.2⟩
