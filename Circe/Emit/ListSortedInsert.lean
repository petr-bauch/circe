import Circe.Emit.LinkedReverse

/-- Pillar-1 goal #6: ordered insert (`list_sorted_insert`,
    find + link swing over an ascending chain). `Node
    *list_sorted_insert(Node *head, int val)` chases with a
    prev/cur pair while `cur != nullptr && cur->val <= val`
    (upper-bound rule), `malloc`s one fresh node, stores the
    payload, swings the fresh link at the landing cursor, then
    swings the head (empty/landing-at-head) or the
    predecessor link, returning the (possibly new) head.
    Faults are loud (miss/tag/liveness checks); cycles out of
    scope. -/
def listSortedInsertName : String :=
  "_Z18list_sorted_insertP4Nodei"

/-- The chase-loop body (advance both cursors): named so the
    agreement proof can rewrite it without literals. -/
def listSortedInsertLoopBody : CStmt :=
  (.seq (.assign "prev" (.var "cur"))
    (.assign "cur" (.pgetNext (.var "cur"))))

/-- The chase loop (isolated for the loop/evaluator
    agreement): guard is the short-circuit `&&` as the pure
    ternary — non-null cursor and the signed keep-advancing
    test (`val < cur` false means `cur <= val`, landing
    before the first strictly greater payload). -/
def listSortedInsertLoop : CStmt :=
  (.while_ (.tif (.une (.var "cur") (.lit .nullptr))
              (.tif (.slt (.var "val") (.pgetVal (.var "cur")))
                (.lit (.b false))
                (.lit (.b true)))
              (.lit (.b false)))
    listSortedInsertLoopBody)

/-- Canonical CoreIR for `list_sorted_insert`: allocate the
    fresh node, store the payload, seed the cursors, chase to
    the landing point, swing the fresh link, swing the head
    (null predecessor) or the predecessor link, return the
    head. -/
def listSortedInsertBody : CStmt :=
  (.seq (.let_ "nd" nodeTy .nnew)
    (.seq (.psetVal (.var "nd") (.var "val"))
      (.seq (.let_ "prev" nodeTy (.lit .nullptr))
        (.seq (.let_ "cur" nodeTy (.var "head"))
          (.seq listSortedInsertLoop
            (.seq (.psetNext (.var "nd") (.var "cur"))
              (.seq (.if_ (.ueq (.var "prev") (.lit .nullptr))
                      (.assign "head" (.var "nd"))
                      (.psetNext (.var "prev") (.var "nd")))
                (.return_ (.var "head")))))))))

/-- The sorted-insert entry: `Node*` + `i32` in, `Node*`
    out (possibly-new head after the swing). -/
def listSortedInsertFunc : Func :=
  ⟨listSortedInsertName,
   [{ name := "head", ty := nodeTy, role := .owned },
    { name := "val", ty := (.i 32), role := .owned }],
   nodeTy,
   listSortedInsertBody⟩

/-- Sorted-insert environment: head and payload slots, then
    the fresh-node and cursor slots (the entry binds `head`
    and `val` first, then the lets cons `nd`, `prev`, `cur`
    on the front). -/
def mkListSortedInsertEnv (head : Option Addr) (v : BitVec 32)
    (nd prev cur : Option Addr) : Env :=
  [("cur", .ptrVal cur), ("prev", .ptrVal prev),
    ("nd", .ptrVal nd),
    ("head", .ptrVal head), ("val", .i32 v)]

theorem mkListSortedInsertEnv_cur (head : Option Addr) (v : BitVec 32)
    (nd prev cur : Option Addr) :
    envLookup (mkListSortedInsertEnv head v nd prev cur) "cur" =
      some (.ptrVal cur) := by
  simp [mkListSortedInsertEnv, envLookup]

theorem mkListSortedInsertEnv_prev (head : Option Addr) (v : BitVec 32)
    (nd prev cur : Option Addr) :
    envLookup (mkListSortedInsertEnv head v nd prev cur) "prev" =
      some (.ptrVal prev) := by
  simp [mkListSortedInsertEnv, envLookup,
    show ("prev" : String) ≠ "cur" by decide]

theorem mkListSortedInsertEnv_nd (head : Option Addr) (v : BitVec 32)
    (nd prev cur : Option Addr) :
    envLookup (mkListSortedInsertEnv head v nd prev cur) "nd" =
      some (.ptrVal nd) := by
  simp [mkListSortedInsertEnv, envLookup,
    show ("nd" : String) ≠ "cur" by decide,
    show ("nd" : String) ≠ "prev" by decide]

theorem mkListSortedInsertEnv_head (head : Option Addr) (v : BitVec 32)
    (nd prev cur : Option Addr) :
    envLookup (mkListSortedInsertEnv head v nd prev cur) "head" =
      some (.ptrVal head) := by
  simp [mkListSortedInsertEnv, envLookup,
    show ("head" : String) ≠ "cur" by decide,
    show ("head" : String) ≠ "prev" by decide,
    show ("head" : String) ≠ "nd" by decide]

theorem mkListSortedInsertEnv_val (head : Option Addr) (v : BitVec 32)
    (nd prev cur : Option Addr) :
    envLookup (mkListSortedInsertEnv head v nd prev cur) "val" =
      some (.i32 v) := by
  simp [mkListSortedInsertEnv, envLookup,
    show ("val" : String) ≠ "cur" by decide,
    show ("val" : String) ≠ "prev" by decide,
    show ("val" : String) ≠ "nd" by decide,
    show ("val" : String) ≠ "head" by decide]

/-! ## Forward mirror (chase to the landing point) -/

/-- Chase to the insertion point: read-only (each step loads
    the payload at `[0]` and the link at `[1]`), stopping at
    the first node whose payload is strictly greater than `v`
    (upper-bound rule, `none` on exhaustion). Misses, dangling
    links, and short blocks abort loudly at any fuel; each
    visited node consumes fuel (like the evaluator's loop
    iteration — a stop needs fuel too). -/
def listSortedInsertChase (F : Nat) (m : Mem)
    (prev cur : Option Addr) (v : BitVec 32) :
    Result (Option Addr × Option Addr) :=
  match cur with
  | none => .ok (prev, none)
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
          if (v.slt w) then .ok (prev, some a)
          else match memLoad m a b.tag 1 with
               | .error e => .error e
               | .ok w' =>
                 listSortedInsertChase F m (some a)
                   (addrOfWord w') v

/-- The chase lands on a fueled segment (faults ruled out by
    the segment hypotheses, exhaustion by fuel). Direct fuel
    induction (no surgery — the chase only observes). -/
theorem listSortedInsertChase_ok (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (v : BitVec 32) (prev cur : Option Addr)
      (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
      (hlen : suf.length ≤ F),
    ∃ p q, listSortedInsertChase F m prev cur v = .ok (p, q) := by
  induction F with
  | zero =>
    intro m hex v prev cur suf hseg hlen
    cases cur with
    | none => exact ⟨prev, none, by simp [listSortedInsertChase]⟩
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
    | none => exact ⟨prev, none, by simp [listSortedInsertChase]⟩
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a t' 0 = .ok _ := nodeLoadVal hnode
        by_cases hstop : (v.slt v₀) = true
        · exact ⟨prev, some a, by
            unfold listSortedInsertChase
            simp only [hfb, hmem0, if_pos hstop]⟩
        · have hmem1 : memLoad m a t' 1 = .ok _ :=
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
          obtain ⟨p, q, hC'⟩ :=
            ih m hex v (some a) nxt vs' t2 hlen'
          refine ⟨p, q, ?_⟩
          unfold listSortedInsertChase
          simp only [hfb, hmem0, if_neg hstop, hmem1, hdec, hC']

/-- The chase lands exactly at the upper-bound split: the
    traveled prefix is all `≤ₛ v`, the remaining suffix is
    empty or starts strictly above `v`; the returned
    predecessor points at the landing cursor and the landing
    cursor heads the remaining suffix. Induction on fuel
    generalizing the cursors and the traveled prefix (the
    predecessor invariant is existential over tag/payload, so
    each visit supplies its own witnesses — no determinism
    needed). -/
theorem listSortedInsertChase_split (F : Nat)
    (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (v : BitVec 32) (prev cur : Option Addr)
    (pre suf : List (BitVec 32))
    (hseg : ListSeg m cur suf)
    (hpre : ∀ a, a ∈ pre → (v.slt a) = false)
    (hprev : ∀ b : Addr, prev = some b →
      ∃ tb wb, nodeAt m b tb wb cur)
    (hlen : suf.length ≤ F)
    (p q : Option Addr)
    (hC : listSortedInsertChase F m prev cur v = .ok (p, q)) :
    ∃ post rest, suf = post ++ rest ∧
      (∀ a, a ∈ post → (v.slt a) = false) ∧
      (∀ x xs, rest = x :: xs → (v.slt x) = true) ∧
      (∀ b : Addr, p = some b →
        ∃ tb wb, nodeAt m b tb wb q) ∧
      ListSeg m q rest := by
  induction F generalizing prev cur pre suf with
  | zero =>
    cases cur with
    | none =>
      cases hseg with
      | nil =>
        have hC' : listSortedInsertChase 0 m prev none v =
            .ok (prev, none) := by
          simp [listSortedInsertChase]
        rw [hC'] at hC
        simp only [Except.ok.injEq, Prod.mk.injEq] at hC
        have hp : p = prev := hC.1.symm
        have hq : q = none := hC.2.symm
        clear hC
        rw [hp, hq]
        exact ⟨[], [], by simp,
          fun _ h => False.elim (by simp at h),
          fun _ _ h => False.elim (by simp at h),
          fun b hb => hprev b hb,
          ListSeg.nil⟩
    | some a =>
      cases hseg with
      | cons _ t2 =>
        obtain ⟨vs', rfl⟩ := listSegVals t2
        exact False.elim (by
          simp only [List.length_cons] at hlen
          omega)
  | succ F ih =>
    cases cur with
    | none =>
      cases hseg with
      | nil =>
        have hC' : listSortedInsertChase (F + 1) m prev none v =
            .ok (prev, none) := by
          simp [listSortedInsertChase]
        rw [hC'] at hC
        simp only [Except.ok.injEq] at hC
        obtain ⟨rfl, rfl⟩ := hC
        exact ⟨[], [], by simp,
          fun _ h => False.elim (by simp at h),
          fun _ _ h => False.elim (by simp at h),
          fun b hb => hprev b hb,
          ListSeg.nil⟩
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a t' 0 = .ok v₀ :=
          nodeLoadVal hnode
        by_cases hstop : (v.slt v₀) = true
        · have hC' : listSortedInsertChase (F + 1) m prev
              (some a) v = .ok (prev, some a) := by
            unfold listSortedInsertChase
            simp only [hfb, hmem0, if_pos hstop]
          rw [hC'] at hC
          simp only [Except.ok.injEq] at hC
          obtain ⟨rfl, rfl⟩ := hC
          refine ⟨[], v₀ :: vs', by simp, ?_, ?_, ?_, ?_⟩
          · intro a' ha'
            simp at ha'
          · intro x xs hx
            simp only [List.cons.injEq] at hx
            obtain ⟨rfl, -⟩ := hx
            exact hstop
          · intro b hb
            exact hprev b hb
          · exact ListSeg.cons hnode t2
        · have hmem1 : memLoad m a t' 1 = .ok (linkWord nxt) :=
            nodeLoadNext hnode
          have hle : (v.slt v₀) = false := by
            cases hv : (v.slt v₀) with
            | true => exact False.elim (hstop hv)
            | false => rfl
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
          simp only [listSortedInsertChase, hfb, hmem0,
            if_neg hstop, hmem1] at hC
          have hpre' : ∀ a', a' ∈ pre ++ [v₀] →
              (v.slt a') = false := by
            intro a' ha'
            simp only [List.mem_append, List.mem_singleton] at ha'
            cases ha' with
            | inl h => exact hpre _ h
            | inr h =>
              cases h
              exact hle
          have hprev' : ∀ b : Addr, (some a) = some b →
              ∃ tb wb, nodeAt m b tb wb (addrOfWord (linkWord nxt)) := by
            intro b hb
            cases hb
            exact ⟨t', v₀, by rw [hdec]; exact hnode⟩
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          have hsegI : ListSeg m (addrOfWord (linkWord nxt)) vs' := by
            rw [hdec]
            exact t2
          obtain ⟨post', rest', hsplit', hord', hgt',
              hprev'', hseg'⟩ :=
            ih (prev := some a) (cur := addrOfWord (linkWord nxt))
              (pre := pre ++ [v₀]) (suf := vs') (hseg := hsegI)
              (hpre := hpre') (hprev := hprev') (hlen := hlen')
              (hC := hC)
          refine ⟨v₀ :: post', rest', ?_, ?_, hgt', hprev'', hseg'⟩
          · simp only [List.cons_append]
            rw [hsplit']
          · intro a' ha'
            simp only [List.mem_cons] at ha'
            cases ha' with
            | inl h =>
              cases h
              exact hle
            | inr h => exact hord' _ h

/-! ## Loop/evaluator agreement -/

/-- Loop/evaluator agreement: the `while` evaluates exactly
    as the chase directs — stop (null cursor or strictly
    greater payload) falls through with the cursors at the
    landing point, advance steps both cursors. Induction on
    fuel generalizing the cursors and the suffix (faults ruled
    out by the segment hypotheses, exhaustion by fuel). -/
theorem listSortedInsertLoop_agree (F : Nat)
    (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (v : BitVec 32)
    (nd prev cur : Option Addr)
    (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
    (hlen : suf.length ≤ F)
    (p q : Option Addr)
    (hC : listSortedInsertChase F m prev cur v = .ok (p, q)) :
    memEvalStmtFuel F listSortedInsertLoop
      (mkListSortedInsertEnv head v nd prev cur) m π =
      .ok ((mkListSortedInsertEnv head v nd p q, m, π),
        .fellThrough) := by
  induction F generalizing prev cur suf with
  | zero =>
    cases cur with
    | none =>
      have hC' : listSortedInsertChase 0 m prev none v =
          .ok (prev, none) := by
        simp [listSortedInsertChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      have hp : p = prev := hC.1.symm
      have hq : q = none := hC.2.symm
      clear hC
      rw [hp, hq]
      have hbe : ((none : Option Addr) != none) = false := by simp
      have hgM : memEvalExpr
          (.tif (.une (.var "cur") (.lit .nullptr))
            (.tif (.slt (.var "val") (.pgetVal (.var "cur")))
              (.lit (.b false))
              (.lit (.b true)))
            (.lit (.b false)))
          (mkListSortedInsertEnv head v nd prev none) m π =
          .ok (.b false) := by
        simp only [memEvalExpr, mkListSortedInsertEnv_cur,
          hbe, litVal]
      exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgM
    | some a =>
      cases hseg with
      | cons _ t2 =>
        obtain ⟨vs', rfl⟩ := listSegVals t2
        exact False.elim (by
          simp only [List.length_cons] at hlen
          omega)
  | succ F ih =>
    cases cur with
    | none =>
      have hC' : listSortedInsertChase (F + 1) m prev none v =
          .ok (prev, none) := by
        simp [listSortedInsertChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq] at hC
      have hp : p = prev := hC.1.symm
      have hq : q = none := hC.2.symm
      clear hC
      rw [hp, hq]
      have hbe : ((none : Option Addr) != none) = false := by simp
      have hgM : memEvalExpr
          (.tif (.une (.var "cur") (.lit .nullptr))
            (.tif (.slt (.var "val") (.pgetVal (.var "cur")))
              (.lit (.b false))
              (.lit (.b true)))
            (.lit (.b false)))
          (mkListSortedInsertEnv head v nd prev none) m π =
          .ok (.b false) := by
        simp only [memEvalExpr, mkListSortedInsertEnv_cur,
          hbe, litVal]
      exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgM
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a t' 0 = .ok v₀ :=
          nodeLoadVal hnode
        have hcurE : memEvalExpr (.var "cur")
            (mkListSortedInsertEnv head v nd prev (some a)) m π =
            .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (mkListSortedInsertEnv_cur _ _ _ _ _)
        have hbe : ((some a : Option Addr) != none) = true := by simp
        by_cases hstop : (v.slt v₀) = true
        · have hgM : memEvalExpr
              (.tif (.une (.var "cur") (.lit .nullptr))
                (.tif (.slt (.var "val") (.pgetVal (.var "cur")))
                  (.lit (.b false))
                  (.lit (.b true)))
                (.lit (.b false)))
              (mkListSortedInsertEnv head v nd prev (some a)) m π =
              .ok (.b false) := by
            simp only [memEvalExpr, mkListSortedInsertEnv_val,
              mkListSortedInsertEnv_cur, hfb, hmem0, hstop, hbe, litVal]
          have hC' : listSortedInsertChase (F + 1) m prev
              (some a) v = .ok (prev, some a) := by
            unfold listSortedInsertChase
            simp only [hfb, hmem0, if_pos hstop]
          rw [hC'] at hC
          simp only [Except.ok.injEq, Prod.mk.injEq] at hC
          have hp : p = prev := hC.1.symm
          have hq : q = some a := hC.2.symm
          clear hC
          rw [hp, hq]
          exact memEvalStmtFuel_while_false _ _ _ _ _ _ hgM
        · have hmem1 : memLoad m a t' 1 = .ok (linkWord nxt) :=
            nodeLoadNext hnode
          have hlinkE : memEvalExpr (.pgetNext (.var "cur"))
              (mkListSortedInsertEnv head v nd prev (some a)) m π =
              .ok (.ptrVal (addrOfWord (linkWord nxt))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE hfb hmem1
          have hstep1 : memEvalStmtFuel F
              (.assign "prev" (.var "cur"))
              (mkListSortedInsertEnv head v nd prev (some a)) m π =
              .ok (((mkListSortedInsertEnv head v nd (some a) (some a)),
                m, π), .fellThrough) :=
            memEvalStmtFuel_assign_mem F "prev" (.var "cur")
              (mkListSortedInsertEnv head v nd prev (some a)) m π
              _ _ hcurE
              (by simp [mkListSortedInsertEnv, envUpdate])
          have hstep2 : memEvalStmtFuel F
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkListSortedInsertEnv head v nd (some a) (some a)) m π =
              .ok (((mkListSortedInsertEnv head v nd (some a)
                (addrOfWord (linkWord nxt))), m, π),
              .fellThrough) :=
            memEvalStmtFuel_assign_mem F "cur" (.pgetNext (.var "cur"))
              (mkListSortedInsertEnv head v nd (some a) (some a)) m π
              _ _ hlinkE
              (by simp [mkListSortedInsertEnv, envUpdate])
          have hbodyEv : memEvalStmtFuel F listSortedInsertLoopBody
              (mkListSortedInsertEnv head v nd prev (some a)) m π =
              .ok (((mkListSortedInsertEnv head v nd (some a)
                (addrOfWord (linkWord nxt))), m, π),
              .fellThrough) :=
            memEvalStmtFuel_seq_fallthrough_trans F _ _
              (mkListSortedInsertEnv head v nd prev (some a)) _ _
              (mkListSortedInsertEnv head v nd (some a) (some a)) _ _ _
              hstep1 hstep2
          have hguardT : memEvalExpr
              (.tif (.une (.var "cur") (.lit .nullptr))
                (.tif (.slt (.var "val") (.pgetVal (.var "cur")))
                  (.lit (.b false))
                  (.lit (.b true)))
                (.lit (.b false)))
              (mkListSortedInsertEnv head v nd prev (some a)) m π =
              .ok (.b true) := by
            have hle : (v.slt v₀) = false := by
              cases hv2 : (v.slt v₀) with
              | true => exact False.elim (hstop hv2)
              | false => rfl
            simp only [memEvalExpr, mkListSortedInsertEnv_val,
                mkListSortedInsertEnv_cur, hfb, hmem0, hle, hbe, litVal]
          have h := memEvalStmtFuel_while_true F _
            listSortedInsertLoopBody _ _ _ hguardT
          simp only [listSortedInsertLoop] at h ⊢
          rw [h]
          simp only [hbodyEv]
          have hC' : listSortedInsertChase (F + 1) m prev
              (some a) v =
              listSortedInsertChase F m (some a)
                (addrOfWord (linkWord nxt)) v := by
            simp only [listSortedInsertChase, hfb, hmem0,
              if_neg hstop, hmem1]
          rw [hC'] at hC
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
          have hsegI : ListSeg m (addrOfWord (linkWord nxt)) vs' := by
            rw [hdec]
            exact t2
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          have hIH := ih (prev := some a)
            (cur := addrOfWord (linkWord nxt)) (suf := vs')
            (hseg := hsegI) (hlen := hlen') (hC := hC)
          exact hIH

/-! ## Chase transport across fresh allocation+stores -/

/-- The chase only observes old nodes: allocation plus stores at
    the fresh address leave every old `memFind` (hence every
    `memLoad`, hence every chase step) unchanged. Induction on
    fuel generalizing the cursors and suffix (the visited nodes
    are segment members, hence live, hence below the mark,
    hence distinct from the fresh address). -/
theorem listSortedInsertChase_transport (F : Nat) (m m₂ : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmark : Mark m)
    (hagree : ∀ a, a ≠ m.next → memFind m₂ a = memFind m a)
    (prev cur : Option Addr) (v : BitVec 32)
    (suf : List (BitVec 32)) (hseg : ListSeg m cur suf) :
    listSortedInsertChase F m₂ prev cur v =
      listSortedInsertChase F m prev cur v := by
  induction F generalizing prev cur suf with
  | zero =>
    cases cur with
    | none => rfl
    | some a =>
      cases hseg with
      | cons _ t2 =>
        obtain ⟨vs', rfl⟩ := listSegVals t2
        simp [listSortedInsertChase]
  | succ F ih =>
    cases cur with
    | none => rfl
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hne : a ≠ m.next :=
          Nat.ne_of_lt (live_lt_of_memFind hmark hfb)
        have hF2 : memFind m₂ a = memFind m a := hagree a hne
        have hmem0 : memLoad m a t' 0 = .ok v₀ :=
          nodeLoadVal hnode
        have eL0 : memLoad m₂ a t' 0 = memLoad m a t' 0 := by
          unfold memLoad
          rw [hF2]
        by_cases hstop : (v.slt v₀) = true
        · simp only [listSortedInsertChase, hfb, hF2, eL0, hmem0,
            if_pos hstop]
        · have hmem1 : memLoad m a t' 1 = .ok (linkWord nxt) :=
            nodeLoadNext hnode
          have eL1 : memLoad m₂ a t' 1 = memLoad m a t' 1 := by
            unfold memLoad
            rw [hF2]
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
          have hIH := ih (prev := some a)
            (cur := nxt) (suf := vs')
            (hseg := t2)
          simp only [listSortedInsertChase, hfb, hF2, eL0, hmem0,
            if_neg hstop, eL1, hmem1, hdec, hIH]

/-! ## Forward mirror (allocate + swing) -/

/-- Functional mirror: chase to the landing point, allocate the
    fresh node, store the payload and the landing link, swing
    the head (landing at head) or the predecessor link. Every
    lookup/store is matched on (erase style) so failures stay
    loud and the evaluator agreement is step-for-step. -/
def listSortedInsertFwd (F : Nat) (m : Mem) (head : Option Addr)
    (v : BitVec 32) : Result (Mem × Option Addr) :=
  match listSortedInsertChase F m none head v with
  | .error e => .error e
  | .ok (prev, cur) =>
    let (m1, a) := memAlloc m 2
    match memFind m1 a with
    | none => .error .AssertFail
    | some ba =>
      match memStore m1 a ba.tag 0 v with
      | .error e => .error e
      | .ok m2 =>
        match memFind m2 a with
        | none => .error .AssertFail
        | some ba2 =>
          match memStore m2 a ba2.tag 1 (linkWord cur) with
          | .error e => .error e
          | .ok m3 =>
            match prev with
            | none => .ok (m3, some a)
            | some p =>
              match memFind m3 p with
              | none => .error .AssertFail
              | some bp =>
                match memStore m3 p bp.tag 1 (linkWord (some a)) with
                | .error e => .error e
                | .ok m4 => .ok (m4, head)

/-- Existential store leg (per-slice kit, mirrors the copy kit):
    a `cellsAt`-pinned cell stores successfully. -/
theorem memStore_cellsAt_ok_insert {m : Mem} {a t : Nat}
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

/-- A `ListSeg` rides a 2-word allocation (node-level
    transport; visited nodes are live, hence below the mark). -/
theorem ListSeg_alloc_other {m : Mem} (hmark : Mark m)
    {s : Option Addr} {vs : List (BitVec 32)}
    (hseg : ListSeg m s vs) :
    ListSeg (memAlloc m 2).1 s vs := by
  induction hseg with
  | nil => exact .nil
  | cons hnode t2 ih =>
    have hf : memFind m _ = some _ := hnode
    exact .cons (nodeAt_alloc_other hnode _
      (Nat.ne_of_lt (live_lt_of_memFind hmark hf))) ih

/-- Members of an allocated segment sit below the mark
    (segment/path lockstep: the path follows segment links,
    which agree across the allocation because `memFind` is
    functional — pinned by link uniqueness). -/
theorem SegMem_alloc_other_lt {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmark : Mark m) (hroom : m.next + 1 < 2 ^ 32)
    {s : Option Addr} {ws : List (BitVec 32)}
    (h1 : ListSeg (memAlloc m 2).1 s ws) (hM : ListSeg m s ws)
    {b : Addr} (hb : SegMem (m := (memAlloc m 2).1) s b) :
    b < m.next := by
  have hex1 : ∀ x, (memFind (memAlloc m 2).1 x).isSome = true →
      x + 1 < 2 ^ 32 := by
    intro x hx
    by_cases heq : x = m.next
    · subst heq
      exact hroom
    · have e : memFind (memAlloc m 2).1 x = memFind m x :=
        memFind_memAllocData_other m [0, 0] x heq
      rw [e] at hx
      exact hex x hx
  induction h1 with
  | nil => cases hb
  | cons hnode1 t2 ih =>
    cases hb with
    | here _ =>
      cases hM with
      | cons hnodeM _ =>
        have hf : memFind m _ = some _ := hnodeM
        exact live_lt_of_memFind hmark hf
    | there hnodeQ hmem =>
      -- Name the links WITHOUT substituting (subst direction is
      -- fragile here); rewrite explicitly via `hnQ`/`hnS` below.
      obtain ⟨vQ, nQ, hvQ, hnQ⟩ := nodeAt_parts hnodeQ
      obtain ⟨vS, nS, hvS, hnS⟩ := nodeAt_parts hnode1
      have hnalloc : ∀ c, nQ = some c →
          (memFind (memAlloc m 2).1 c).isSome := by
        intro c hc
        have hmemQ : SegMem (m := (memAlloc m 2).1) (some c) b := by
          have h := hmem
          rwa [← hnQ, hc] at h
        cases hmemQ with
        | here hnode =>
          unfold nodeAt cellsAt at hnode
          simp [hnode]
        | there hnode _ =>
          unfold nodeAt cellsAt at hnode
          simp [hnode]
      have hnalloc' : ∀ c, nS = some c →
          (memFind (memAlloc m 2).1 c).isSome := by
        intro c hc
        have t2copy := t2
        rw [← hnS, hc] at t2copy
        cases t2copy with
        | cons hnodeT _ =>
          unfold nodeAt cellsAt at hnodeT
          simp [hnodeT]
      -- Same live allocated node: the links agree. Move the two
      -- head facts into named-link form first (they are not needed
      -- afterwards); payloads unify at the lemma application.
      rw [← hnQ] at hnodeQ
      rw [← hnS] at hnode1
      have heq : nQ = nS :=
        nodeAt_link_unique hnodeQ hnode1 hex1 hnalloc hnalloc'
      rw [← hnQ, heq, hnS] at hmem
      cases hM with
      | cons hnodeM t2M =>
        -- The m-side head cell rides the allocation; its link is
        -- the m1-side link by same-memory uniqueness.
        have hfindM : memFind m _ = some _ := hnodeM
        have hnodeM1 := nodeAt_alloc_other hnodeM [0, 0]
          (Nat.ne_of_lt (live_lt_of_memFind hmark hfindM))
        have heqM := nodeAt_link_unique hnodeM1 hnode1 hex1
          (by intro c hc
              have h := t2M
              rw [hc] at h
              cases h with
              | cons hnodeT _ =>
                unfold nodeAt cellsAt at hnodeT
                have hne : c ≠ m.next := Nat.ne_of_lt
                  (live_lt_of_memFind hmark hnodeT)
                have e : memFind (memAllocData m [0, 0]).1 c =
                    memFind m c :=
                  memFind_memAllocData_other m [0, 0] c hne
                rw [e]
                simp [hnodeT])
          hnalloc'
        rw [heqM, hnS] at t2M
        exact ih t2M hmem

/-- Entry correctness (evaluator agrees with the mirror): the
    body runs to exactly the fwd mirror's `(m', hd')`. The loop
    evaluates on the post-store memory, so the chase equation
    is transported across the fresh allocation+store and the
    segment is carried along (freshness is the mark). -/
theorem listSortedInsertFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmark : Mark m)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hroom : m.next + 1 < 2 ^ 32)
    (hseg : ListSeg m head vs)
    (hlen : vs.length ≤ F)
    (hfwd : listSortedInsertFwd F m head v = .ok (m', hd')) :
    ∃ ρ', memEvalStmtFuel F listSortedInsertBody
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      .ok ((ρ', m', π), .returned (.ptrVal hd')) := by
  -- Chase on the original memory, plus the upper-bound split.
  obtain ⟨p, q, hC⟩ :=
    listSortedInsertChase_ok F m hex v none head vs hseg hlen
  have hsplit := listSortedInsertChase_split F m hex v none head
    [] vs hseg (by simp) (by intro b hb; cases hb) hlen p q hC
  obtain ⟨post, rest, hvsplit, hord, hgt, hprev, hsegR⟩ := hsplit
  -- Fresh allocation and the two fresh-cell stores.
  have hmfresh : memFind m m.next = none := hmark _ (Nat.le_refl _)
  have hA : (memAlloc m 2).2 = m.next := memAlloc_next m 2
  have hmark1 : Mark (memAlloc m 2).1 := freshAbove_alloc m 2 hmark
  have hfindN : memFind (memAlloc m 2).1 (memAlloc m 2).2 =
      some ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ :=
    memFind_memAlloc m 2
  have hcell0 : cellsAt (memAlloc m 2).1 (memAlloc m 2).2
      ((memAlloc m 2).2) [0, 0] := hfindN
  obtain ⟨m2, hS1⟩ := memStore_cellsAt_ok_insert (i := 0) hcell0
    (by decide)
  have hcell1 : cellsAt m2 (memAlloc m 2).2 ((memAlloc m 2).2)
      [v, 0] := by
    have h := memFind_cellsAt_store _ _ _ _ _ _ _ hcell0
      (by decide) hS1
    simpa using h
  obtain ⟨m3, hS2⟩ := memStore_cellsAt_ok_insert (i := 1) hcell1
    (by simp)
  -- The segment rides the allocation, then the payload store.
  have hseg1 : ListSeg (memAlloc m 2).1 head vs :=
    ListSeg_alloc_other hmark hseg
  have hout1 : ∀ b, SegMem (m := (memAlloc m 2).1) head b →
      b ≠ (memAlloc m 2).2 := by
    intro b hb
    have hlt := SegMem_alloc_other_lt hex hmark hroom
      hseg1 hseg hb
    rw [hA]
    exact Nat.ne_of_lt hlt
  have hseg2 : ListSeg m2 head vs :=
    ListSeg.store_other_mem hseg1 hout1 hS1
  -- Reads agree across alloc+store (stores hit only fresh).
  have hagree : ∀ a, a ≠ m.next → memFind m2 a = memFind m a := by
    intro a ha
    have e1 : memFind m2 a = memFind (memAlloc m 2).1 a :=
      memFind_memStore_other _ _ _ _ _ _ _ hS1 ha
    have e2 : memFind (memAlloc m 2).1 a = memFind m a :=
      memFind_memAllocData_other m [0, 0] a ha
    rw [e1, e2]
  -- Exactness rides along (fresh cell needs room).
  have hex2 : ∀ x, (memFind m2 x).isSome = true → x + 1 < 2 ^ 32 := by
    intro x hx
    by_cases heq : x = m.next
    · subst heq
      exact hroom
    · have e : memFind m2 x = memFind m x := hagree x heq
      rw [e] at hx
      exact hex x hx
  -- Chase equation on the loop memory.
  have hC2 : listSortedInsertChase F m2 none head v = .ok (p, q) := by
    rw [listSortedInsertChase_transport F m m2 hex hmark hagree
      none head v vs hseg, hC]
  -- Loop agreement on the loop memory.
  have hloop := listSortedInsertLoop_agree F m2 π hex2 head v
    ((memAlloc m 2).2) none head vs hseg2 hlen p q hC2
  -- Seed: allocate, store the payload, seed the cursors.
  -- Envs are flat lists (notation-identical to cons chains).
  have hletN : memEvalStmtFuel F (.let_ "nd" nodeTy .nnew)
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      .ok ((([("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)],
        (memAlloc m 2).1, π), .fellThrough)) := by
    have h := memEvalStmtFuel_let_nnew F "nd" nodeTy
      [("head", .ptrVal head), ("val", .i32 v)] m π
    simpa using h
  have hdN : memEvalExpr (.var "nd")
      [("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)]
      (memAlloc m 2).1 π =
      .ok (.ptrVal (memAlloc m 2).2) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hvN : memEvalExpr (.var "val")
      [("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)]
      (memAlloc m 2).1 π =
      .ok (.i32 v) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hpsetV : memEvalStmtFuel F
      (.psetVal (.var "nd") (.var "val"))
      [("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)]
      (memAlloc m 2).1 π =
      .ok ((([("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)], m2, π),
        .fellThrough)) :=
    memEvalStmtFuel_psetVal_ok F (.var "nd") (.var "val")
      _ _ _ _ _ _ _ hdN hvN hfindN hS1
  have eP : memEvalExpr (.lit .nullptr)
      [("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)] m2 π =
      evalExpr (.lit .nullptr)
        [("nd", .ptrVal (memAlloc m 2).2),
          ("head", .ptrVal head), ("val", .i32 v)] :=
    memEvalExpr_lit _ _ _ _
  have vP : evalExpr (.lit .nullptr)
      [("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)] =
      .ok (.ptrVal none) := by simp [evalExpr, litVal]
  have hletP : memEvalStmtFuel F
      (.let_ "prev" nodeTy (.lit .nullptr))
      [("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)] m2 π =
      .ok ((([("prev", .ptrVal none),
        ("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)], m2, π),
        .fellThrough)) :=
    memEvalStmtFuel_let_pure F "prev" nodeTy (.lit .nullptr)
      _ _ _ (.ptrVal none)
      (by simp) (by simp) (by simp) (by simp) eP vP
  have eC : memEvalExpr (.var "head")
      [("prev", .ptrVal none),
        ("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)] m2 π =
      evalExpr (.var "head")
        [("prev", .ptrVal none),
          ("nd", .ptrVal (memAlloc m 2).2),
          ("head", .ptrVal head), ("val", .i32 v)] :=
    memEvalExpr_var _ _ _ _
  have vC : evalExpr (.var "head")
      [("prev", .ptrVal none),
        ("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)] =
      .ok (.ptrVal head) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hletC : memEvalStmtFuel F
      (.let_ "cur" nodeTy (.var "head"))
      [("prev", .ptrVal none),
        ("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)] m2 π =
      .ok ((([("cur", .ptrVal head), ("prev", .ptrVal none),
        ("nd", .ptrVal (memAlloc m 2).2),
        ("head", .ptrVal head), ("val", .i32 v)], m2, π),
        .fellThrough)) :=
    memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
      _ _ _ (.ptrVal head)
      (by simp) (by simp) (by simp) (by simp) eC vC
  have eEnv : [("cur", .ptrVal head), ("prev", .ptrVal none),
      ("nd", .ptrVal (memAlloc m 2).2),
      ("head", .ptrVal head), ("val", .i32 v)] =
      mkListSortedInsertEnv head v (memAlloc m 2).2 none head := rfl
  have hloopE : memEvalStmtFuel F listSortedInsertLoop
      [("cur", .ptrVal head), ("prev", .ptrVal none),
      ("nd", .ptrVal (memAlloc m 2).2),
      ("head", .ptrVal head), ("val", .i32 v)] m2 π =
      .ok (((mkListSortedInsertEnv head v (memAlloc m 2).2 p q,
        m2, π), .fellThrough)) := by
    rw [eEnv]
    exact hloop
  -- Swing the fresh link at the landing cursor.
  have hfindN2 : memFind m2 (memAlloc m 2).2 =
      some ⟨(memAlloc m 2).2, true, [v, 0]⟩ := hcell1
  have hdN4 : memEvalExpr (.var "nd")
      (mkListSortedInsertEnv head v (memAlloc m 2).2 p q) m2 π =
      .ok (.ptrVal (memAlloc m 2).2) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ (mkListSortedInsertEnv_nd _ _ _ _ _)
  have hlC4 : memEvalExpr (.var "cur")
      (mkListSortedInsertEnv head v (memAlloc m 2).2 p q) m2 π =
      .ok (.ptrVal q) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ (mkListSortedInsertEnv_cur _ _ _ _ _)
  have hpsetN : memEvalStmtFuel F
      (.psetNext (.var "nd") (.var "cur"))
      (mkListSortedInsertEnv head v (memAlloc m 2).2 p q) m2 π =
      .ok (((mkListSortedInsertEnv head v (memAlloc m 2).2 p q,
        m3, π), .fellThrough)) :=
    memEvalStmtFuel_psetNext_ok F (.var "nd") (.var "cur")
      _ _ _ _ _ _ _ hdN4 hlC4 hfindN2 hS2
  -- Branch on the predecessor: head swing vs link swing.
  cases hp : p with
  | none =>
    subst hp
    have hprevE : memEvalExpr (.var "prev")
        (mkListSortedInsertEnv head v (memAlloc m 2).2 none q)
        m3 π =
        .ok (.ptrVal none) := by
      rw [memEvalExpr_var]
      exact evalExpr_var_hit _ _ _
        (mkListSortedInsertEnv_prev _ _ _ _ _)
    have hnullE3 : memEvalExpr (.lit .nullptr)
        (mkListSortedInsertEnv head v (memAlloc m 2).2 none q)
        m3 π =
        .ok (.ptrVal none) := by
      simp [memEvalExpr, litVal]
    have hcondT : memEvalExpr
        (.ueq (.var "prev") (.lit .nullptr))
        (mkListSortedInsertEnv head v (memAlloc m 2).2 none q)
        m3 π =
        .ok (.b true) := by
      have hbe : ((none : Option Addr) == none) = true := by simp
      have h := memEvalExpr_ueq_ptrVal _ _ _ _ _ none none
        hprevE hnullE3
      rwa [hbe] at h
    have hifT : memEvalStmtFuel F
        (.if_ (.ueq (.var "prev") (.lit .nullptr))
          (.assign "head" (.var "nd"))
          (.psetNext (.var "prev") (.var "nd")))
        (mkListSortedInsertEnv head v (memAlloc m 2).2 none q)
        m3 π =
        memEvalStmtFuel F (.assign "head" (.var "nd"))
          (mkListSortedInsertEnv head v (memAlloc m 2).2 none q)
          m3 π :=
      memEvalStmtFuel_if_true F _ _ _ _ _ _ hcondT
    have hassign : memEvalStmtFuel F (.assign "head" (.var "nd"))
        (mkListSortedInsertEnv head v (memAlloc m 2).2 none q)
        m3 π =
        .ok ((([("cur", .ptrVal q), ("prev", .ptrVal none),
          ("nd", .ptrVal (memAlloc m 2).2),
          ("head", .ptrVal (memAlloc m 2).2),
          ("val", .i32 v)], m3, π), .fellThrough)) :=
      memEvalStmtFuel_assign_mem F "head" (.var "nd")
        (mkListSortedInsertEnv head v (memAlloc m 2).2 none q)
        m3 π _ _ hdN4
        (by simp [mkListSortedInsertEnv, envUpdate])
    have hret : memEvalStmtFuel F (.return_ (.var "head"))
        [("cur", .ptrVal q), ("prev", .ptrVal none),
          ("nd", .ptrVal (memAlloc m 2).2),
          ("head", .ptrVal (memAlloc m 2).2),
          ("val", .i32 v)] m3 π =
        .ok ((([("cur", .ptrVal q), ("prev", .ptrVal none),
          ("nd", .ptrVal (memAlloc m 2).2),
          ("head", .ptrVal (memAlloc m 2).2),
          ("val", .i32 v)], m3, π),
          .returned (.ptrVal (memAlloc m 2).2))) :=
      memEvalStmtFuel_return F _ _ _ _ _
        (memEvalExpr_var _ _ _ _)
        (evalExpr_var_hit _ _ _ (by simp [envLookup]))
    have hSeqGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ (hifT.trans hassign) hret
    have hSeqFGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ hpsetN hSeqGH
    have hSeqEFGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ hloopE hSeqFGH
    have hSeqDEFGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ hletC hSeqEFGH
    have hSeqCDEFGH := memEvalStmtFuel_seq_fallthrough_trans
      F _ _ _ _ _ _ _ _ _ hletP hSeqDEFGH
    have hSeqBCDEFGH := memEvalStmtFuel_seq_fallthrough_trans
      F _ _ _ _ _ _ _ _ _ hpsetV hSeqCDEFGH
    have hFULL := memEvalStmtFuel_seq_fallthrough_trans
      F _ _ _ _ _ _ _ _ _ hletN hSeqBCDEFGH
    simp only [listSortedInsertFwd, hC, hfindN, hS1, hfindN2,
      hS2] at hfwd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨e1, e2⟩ := hfwd
    subst e1
    subst e2
    exact ⟨_, hFULL⟩
  | some b =>
    subst hp
    -- The predecessor node exists in the original memory.
    obtain ⟨tb, wb, hnodeP⟩ := hprev b rfl
    have hfbP : memFind m b = some _ := hnodeP
    have hneP : b ≠ m.next :=
      Nat.ne_of_lt (live_lt_of_memFind hmark hfbP)
    have hneP2 : b ≠ (memAlloc m 2).2 := by
      rw [hA]
      exact hneP
    -- Carry it across the allocation and the two fresh stores.
    have hnodeP1 : nodeAt (memAlloc m 2).1 b tb wb q :=
      nodeAt_alloc_other hnodeP _ hneP
    have hnodeP2 : nodeAt m2 b tb wb q :=
      nodeAt_store_other_fwd hnodeP1 hS1 hneP2
    have hnodeP3 : nodeAt m3 b tb wb q :=
      nodeAt_store_other_fwd hnodeP2 hS2 hneP2
    have hfindP3 : memFind m3 b =
        some ⟨tb, true, [wb, linkWord q]⟩ := hnodeP3
    have hcellP : cellsAt m3 b tb [wb, linkWord q] := hnodeP3
    obtain ⟨m4, hS3⟩ := memStore_cellsAt_ok_insert (i := 1) hcellP
      (by simp)
    have hprevE : memEvalExpr (.var "prev")
        (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
        m3 π =
        .ok (.ptrVal (some b)) := by
      rw [memEvalExpr_var]
      exact evalExpr_var_hit _ _ _
        (mkListSortedInsertEnv_prev _ _ _ _ _)
    have hnullE3 : memEvalExpr (.lit .nullptr)
        (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
        m3 π =
        .ok (.ptrVal none) := by
      simp [memEvalExpr, litVal]
    have hcondF : memEvalExpr
        (.ueq (.var "prev") (.lit .nullptr))
        (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
        m3 π =
        .ok (.b false) := by
      have hbe : (((some b) : Option Addr) == none) = false := by
        simp
      have h := memEvalExpr_ueq_ptrVal _ _ _ _ _ (some b) none
        hprevE hnullE3
      rwa [hbe] at h
    have hifF : memEvalStmtFuel F
        (.if_ (.ueq (.var "prev") (.lit .nullptr))
          (.assign "head" (.var "nd"))
          (.psetNext (.var "prev") (.var "nd")))
        (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
        m3 π =
        memEvalStmtFuel F (.psetNext (.var "prev") (.var "nd"))
          (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
          m3 π :=
      memEvalStmtFuel_if_false F _ _ _ _ _ _ hcondF
    have hdN4b : memEvalExpr (.var "nd")
        (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
        m3 π =
        .ok (.ptrVal (memAlloc m 2).2) := by
      rw [memEvalExpr_var]
      exact evalExpr_var_hit _ _ _ (mkListSortedInsertEnv_nd _ _ _ _ _)
    have hbranch : memEvalStmtFuel F
        (.psetNext (.var "prev") (.var "nd"))
        (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
        m3 π =
        .ok (((mkListSortedInsertEnv head v (memAlloc m 2).2
          (some b) q, m4, π), .fellThrough)) :=
      memEvalStmtFuel_psetNext_ok F (.var "prev") (.var "nd")
        _ _ _ _ _ _ _ hprevE hdN4b hfindP3 hS3
    have hretH : memEvalStmtFuel F (.return_ (.var "head"))
        (mkListSortedInsertEnv head v (memAlloc m 2).2 (some b) q)
        m4 π =
        .ok (((mkListSortedInsertEnv head v (memAlloc m 2).2
          (some b) q, m4, π),
          .returned (.ptrVal head))) :=
      memEvalStmtFuel_return F _ _ _ _ _
        (memEvalExpr_var _ _ _ _)
        (evalExpr_var_hit _ _ _
          (mkListSortedInsertEnv_head _ _ _ _ _))
    have hSeqGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ (hifF.trans hbranch) hretH
    have hSeqFGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ hpsetN hSeqGH
    have hSeqEFGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ hloopE hSeqFGH
    have hSeqDEFGH := memEvalStmtFuel_seq_fallthrough_trans F _ _
      _ _ _ _ _ _ _ hletC hSeqEFGH
    have hSeqCDEFGH := memEvalStmtFuel_seq_fallthrough_trans
      F _ _ _ _ _ _ _ _ _ hletP hSeqDEFGH
    have hSeqBCDEFGH := memEvalStmtFuel_seq_fallthrough_trans
      F _ _ _ _ _ _ _ _ _ hpsetV hSeqCDEFGH
    have hFULL := memEvalStmtFuel_seq_fallthrough_trans
      F _ _ _ _ _ _ _ _ _ hletN hSeqBCDEFGH
    simp only [listSortedInsertFwd, hC, hfindN, hS1, hfindN2,
      hS2, hfindP3, hS3] at hfwd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨e1, e2⟩ := hfwd
    subst e1
    subst e2
    exact ⟨_, hFULL⟩

/-! ## Spec: upper-bound insertion oracle (pure) -/

/-- Pure oracle: insert `v` after all elements `≤ v` (upper bound —
    insert before the first strictly-greater element). -/
def sortedInsert (v : BitVec 32) : List (BitVec 32) → List (BitVec 32)
  | [] => [v]
  | x :: xs => if (v.slt x) then v :: x :: xs else x :: sortedInsert v xs

/-- `slt` transitivity (via `toInt` + `omega`, the `slt_trans`
    precedent restated locally to avoid a new import). -/
theorem sortedInsert_slt_trans {x y z : BitVec 32}
    (hxy : (x.slt y) = true) (hyz : (y.slt z) = true) :
    (x.slt z) = true := by
  rw [BitVec.slt_eq_decide] at hxy hyz ⊢
  simp only [decide_eq_true_eq] at hxy hyz ⊢
  omega

/-- `slt` asymmetry (via `toInt` + `omega`, the `slt_asymm`
    precedent restated locally). -/
theorem sortedInsert_slt_asymm {x y : BitVec 32}
    (h : (x.slt y) = true) : (y.slt x) = false := by
  rw [BitVec.slt_eq_decide] at h ⊢
  simp only [decide_eq_true_eq] at h
  simp only [decide_eq_false_iff_not]
  omega

/-- `slt` irreflexivity (via `toInt`, the `slt_irrefl` precedent
    restated locally). -/
theorem sortedInsert_slt_irrefl (x : BitVec 32) : (x.slt x) = false := by
  rw [BitVec.slt_eq_decide]
  simp

/-- The oracle pushes `v` past a no-greater prefix: everything
    `≤ v` stays ahead, then `v`, then the rest. -/
theorem sortedInsert_prefix (v : BitVec 32) (L rest : List (BitVec 32))
    (hall : ∀ a ∈ L, (v.slt a) = false)
    (hgt : ∀ x xs, rest = x :: xs → (v.slt x) = true) :
    sortedInsert v (L ++ rest) = L ++ [v] ++ rest := by
  induction L with
  | nil =>
    cases rest with
    | nil => rfl
    | cons x xs =>
      have hx : (v.slt x) = true := hgt x xs rfl
      simp [sortedInsert, hx]
  | cons y L' ih =>
    have hle : (v.slt y) = false :=
      hall y (List.mem_cons.mpr (Or.inl rfl))
    have hall' : ∀ a ∈ L', (v.slt a) = false := by
      intro a ha
      exact hall a (List.mem_cons.mpr (Or.inr ha))
    have estep : sortedInsert v ((y :: L') ++ rest) =
        y :: sortedInsert v (L' ++ rest) := by
      have e0 : (y :: L') ++ rest = y :: (L' ++ rest) := rfl
      rw [e0]
      simp [sortedInsert, hle]
    have e2 : (y :: L') ++ [v] ++ rest = y :: (L' ++ [v] ++ rest) := by
      simp only [List.cons_append]
    rw [estep, e2, ih hall']

/-- The oracle only inserts: output is a permutation of `v :: l`. -/
theorem sortedInsert_perm (v : BitVec 32) (l : List (BitVec 32)) :
    List.Perm (sortedInsert v l) (v :: l) := by
  induction l with
  | nil => exact List.Perm.rfl
  | cons x xs ih =>
    by_cases h : (v.slt x) = true
    · have e : sortedInsert v (x :: xs) = v :: x :: xs := by
        simp [sortedInsert, h]
      rw [e]
    · have hle : (v.slt x) = false := by
        cases hv : (v.slt x) with
        | true => exact False.elim (h hv)
        | false => rfl
      have e : sortedInsert v (x :: xs) = x :: sortedInsert v xs := by
        simp [sortedInsert, hle]
      rw [e]
      exact (ih.cons x).trans (List.Perm.swap v x xs)

/-- Inserting in the middle permutes past the value. -/
theorem perm_insert_middle (post : List (BitVec 32)) (v : BitVec 32)
    (rest : List (BitVec 32)) :
    List.Perm (post ++ [v] ++ rest) (v :: (post ++ rest)) := by
  induction post with
  | nil => exact List.Perm.rfl
  | cons x xs ih =>
    have e1 : (x :: xs) ++ [v] ++ rest = x :: (xs ++ [v] ++ rest) := by
      simp only [List.cons_append]
    have e2 : v :: ((x :: xs) ++ rest) = v :: x :: (xs ++ rest) := rfl
    rw [e1, e2]
    exact (ih.cons x).trans (List.Perm.swap v x (xs ++ rest))

/-! ## Chain acyc: the last visited node is fresh in its chain -/

/-- Successor link at chain position `i`: the next node's
    address, or the chain end at the tail. -/
def chainNext (nodes : List (Addr × Nat × BitVec 32)) (e : Option Addr)
    (i : Nat) : Option Addr :=
  match nodes[i + 1]? with
  | some y => some y.1
  | none => e

/-- The successor link shifts over a cons. -/
theorem chainNext_cons (hd : Addr × Nat × BitVec 32)
    (tl : List (Addr × Nat × BitVec 32)) (e : Option Addr) (i : Nat) :
    chainNext (hd :: tl) e (i + 1) = chainNext tl e i := by
  simp only [chainNext, List.getElem?_cons_succ]

/-- The head successor is the chain's first link. -/
theorem chainNext_head {m : Mem} {n e : Option Addr}
    {tl : List (Addr × Nat × BitVec 32)}
    (hrest : PrefixChain m n tl e) (hd : Addr × Nat × BitVec 32) :
    chainNext (hd :: tl) e 0 = n := by
  cases tl with
  | nil =>
    cases hrest with
    | nil => rfl
  | cons y ys =>
    cases hrest with
    | cons _ _ => rfl

/-- Chain nodes lie in the chain-start footprint. -/
theorem prefixChain_mem {m : Mem} {s e : Option Addr}
    {nodes : List (Addr × Nat × BitVec 32)}
    (h : PrefixChain m s nodes e) :
    ∀ x ∈ nodes, SegMem (m := m) s x.1 := by
  induction h with
  | nil =>
    intro x hx
    simp at hx
  | cons hnode _ ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    cases hx with
    | inl heq =>
      obtain rfl := heq
      exact SegMem.here hnode
    | inr hmem =>
      exact SegMem.there hnode (ih _ hmem)

/-- Footprint members are live. -/
theorem SegMem_mem_alloc {m : Mem} {s : Option Addr} {b : Addr}
    (hb : SegMem (m := m) s b) : (memFind m b).isSome = true := by
  induction hb with
  | here hnode =>
    unfold nodeAt cellsAt at hnode
    simp [hnode]
  | there _ _ ih => exact ih

/-- Footprint members are below the mark (live). -/
theorem SegMem_mem_lt {m : Mem} {s : Option Addr} {b : Addr}
    (hb : SegMem (m := m) s b) (hmark : Mark m) : b < m.next := by
  induction hb with
  | here hnode =>
    unfold nodeAt cellsAt at hnode
    exact live_lt_of_memFind hmark hnode
  | there _ _ ih => exact ih

/-- Chain steps are `chaseN` steps: the `i`-th chain node is the
    `i`-th link-chase from the chain start (deterministic links;
    each link target is allocated). -/
theorem prefixChain_chaseN {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {s e : Option Addr} {nodes : List (Addr × Nat × BitVec 32)}
    (h : PrefixChain m s nodes e)
    (halloc : ∀ (i : Nat) (c : Addr), chainNext nodes e i = some c →
      (memFind m c).isSome = true) :
    ∀ (i : Nat) (x : Addr × Nat × BitVec 32),
      nodes[i]? = some x → chaseN m i s = some x.1 := by
  induction h with
  | nil =>
    intro i x hx
    simp at hx
  | cons hnode hrest ih =>
    rename_i n e tl a t w
    have hallocT : ∀ (i : Nat) (c : Addr), chainNext tl e i = some c →
        (memFind m c).isSome = true := by
      intro i c hc
      exact halloc (i + 1) c (by rw [chainNext_cons]; exact hc)
    have h1 : chainNext ((a, t, w) :: tl) e 0 = n :=
      chainNext_head hrest (a, t, w)
    have hstep : chaseStep m (some a) = n :=
      chaseStep_nodeAt hnode hex
        (fun c' hc' => halloc 0 c' (by rw [h1]; exact hc'))
    intro i x hx
    cases i with
    | zero =>
      simp at hx
      obtain rfl := hx
      rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at hx
      have estep : chaseN m (j + 1) (some a) = chaseN m j n := by
        calc chaseN m (j + 1) (some a)
            = chaseN m j (chaseN m 1 (some a)) :=
              chaseN_add m j 1 (some a)
          _ = chaseN m j n := by
              have h1' : chaseN m 1 (some a) = n := by
                show chaseStep m (chaseN m 0 (some a)) = n
                rw [show chaseN m 0 (some a) = some a from rfl]
                exact hstep
              rw [h1']
      rw [estep]
      exact ih hallocT j x hx

/-- The last visited node is fresh in its chain: nothing before it
    shares its address (chase injectivity on the paired segment). -/
theorem chain_last_notin_init {m : Mem}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    {head q : Option Addr}
    {init : List (Addr × Nat × BitVec 32)}
    {b : Addr} {tb : Nat} {wb : BitVec 32}
    {post rest : List (BitVec 32)}
    (hchain : PrefixChain m head (init ++ [(b, tb, wb)]) q)
    (hpost : preVals (init ++ [(b, tb, wb)]) = post)
    (hseg : ListSeg m head (post ++ rest))
    (hallocC : ∀ (i : Nat) (c : Addr),
      chainNext (init ++ [(b, tb, wb)]) q i = some c →
      (memFind m c).isSome = true) :
    ∀ x ∈ init, x.1 ≠ b := by
  intro x hx heq
  obtain ⟨j, hjx⟩ := List.mem_iff_getElem?.mp hx
  have hj_lt : j < init.length :=
    (List.getElem?_eq_some_iff.mp hjx).1
  have hjxN : (init ++ [(b, tb, wb)])[j]? = some x := by
    rw [List.getElem?_append_left hj_lt]
    exact hjx
  have hlast : (init ++ [(b, tb, wb)])[init.length]? =
      some (b, tb, wb) := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  have e1 : chaseN m j head = some b := by
    have h := prefixChain_chaseN hex hchain hallocC j x hjxN
    rwa [heq] at h
  have e2 : chaseN m init.length head = some b :=
    prefixChain_chaseN hex hchain hallocC init.length (b, tb, wb) hlast
  have hinj := (ListSeg_acyclic_aux (post ++ rest).length m hex head
    (post ++ rest) (Nat.le_refl _) hseg).1
  have hjeq : j = init.length := hinj j init.length b e1 e2
  omega

/-! ## Spec: sortedness is preserved -/

/-- Sorted window (same statement as `Specs.SortedWindow`, restated at
    the Emit layer: this fragment cannot import downstream `Specs`
    without cycling through `Match` once wired). Positions in
    `[lo, hi)` pairwise ascending under `slt`. -/
def SortedWindow (l : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ∀ p q, lo ≤ p → p < q → q < hi → ∀ a b,
    l[p]? = some a → l[q]? = some b → (b.slt a) = false

/-- The output window is sorted: pairs inside either side ride the
    input window, pairs across the value use the no-greater /
    stop-greater facts (with `slt` transitivity for deep rest). -/
theorem sortedInsert_sorted (v : BitVec 32) (post rest : List (BitVec 32))
    (hord : ∀ a ∈ post, (v.slt a) = false)
    (hgt : ∀ x xs, rest = x :: xs → (v.slt x) = true)
    (hsorted : SortedWindow (post ++ rest) 0 (post ++ rest).length) :
    SortedWindow (post ++ [v] ++ rest) 0 (post ++ [v] ++ rest).length := by
  have eout : (post ++ [v] ++ rest) = post ++ (v :: rest) := by
    simp [List.append_assoc]
  have hlenV : (post ++ rest).length = post.length + rest.length := by
    simp [List.length_append]
  intro p q hlo hpq hqk a b ha hb
  rw [eout] at ha hb
  have hvP : (post ++ (v :: rest))[post.length]? = some v := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  have happendL : ∀ (k : Nat) (hk : k < post.length),
      (post ++ (v :: rest))[k]? = post[k]? :=
    fun k hk => List.getElem?_append_left hk
  have happendR : ∀ (k : Nat) (hk : post.length ≤ k),
      (post ++ (v :: rest))[k]? = (v :: rest)[k - post.length]? :=
    fun k hk => List.getElem?_append_right hk
  have hvsL : ∀ (k : Nat) (hk : k < post.length),
      (post ++ rest)[k]? = post[k]? :=
    fun k hk => List.getElem?_append_left hk
  have hvsR : ∀ (k : Nat) (hk : post.length ≤ k),
      (post ++ rest)[k]? = rest[k - post.length]? :=
    fun k hk => List.getElem?_append_right hk
  rcases Nat.lt_trichotomy p post.length with hpP | hpP | hpP
  · rcases Nat.lt_trichotomy q post.length with hqP | hqP | hqP
    · -- Both in the prefix: ride the input window.
      have ha' : post[p]? = some a := by
        rw [← happendL p hpP]; exact ha
      have hb' : post[q]? = some b := by
        rw [← happendL q hqP]; exact hb
      have haV : (post ++ rest)[p]? = some a := by
        rw [hvsL p hpP]; exact ha'
      have hbV : (post ++ rest)[q]? = some b := by
        rw [hvsL q hqP]; exact hb'
      have hjlen : q < post.length :=
        (List.getElem?_eq_some_iff.mp hb').1
      have hqlen : q < (post ++ rest).length := by
        rw [hlenV]; omega
      exact hsorted p q (by omega) hpq hqlen a b haV hbV
    · -- Cursor at the value: the no-greater fact.
        have ha' : post[p]? = some a := by
          rw [← happendL p hpP]; exact ha
        have hbv : b = v := by
          rw [hqP] at hb
          rw [hvP] at hb
          exact (Option.some_inj.mp hb).symm
        rw [hbv]
        exact hord a (List.mem_of_getElem? ha')
    · -- Prefix against rest: ride the input window across.
      have ha' : post[p]? = some a := by
        rw [← happendL p hpP]; exact ha
      have hb' : rest[q - post.length - 1]? = some b := by
        have h1 : (post ++ (v :: rest))[q]? = (v :: rest)[q - post.length]? :=
          happendR q (by omega)
        rw [h1] at hb
        have h2 : q - post.length = (q - post.length - 1) + 1 := by omega
        rw [h2, List.getElem?_cons_succ] at hb
        exact hb
      have haV : (post ++ rest)[p]? = some a := by
        rw [hvsL p hpP]; exact ha'
      have hbV : (post ++ rest)[q - 1]? = some b := by
        have h1 : (post ++ rest)[q - 1]? = rest[q - 1 - post.length]? :=
          hvsR (q - 1) (by omega)
        rw [h1]
        have h2 : q - 1 - post.length = q - post.length - 1 := by omega
        rw [h2]; exact hb'
      have hjlen : q - post.length - 1 < rest.length :=
        (List.getElem?_eq_some_iff.mp hb').1
      have hqlen : q - 1 < (post ++ rest).length := by
        rw [hlenV]; omega
      exact hsorted p (q - 1) (by omega) (by omega) hqlen a b haV hbV
  · -- Cursor at the value.
    subst hpP
    rcases Nat.lt_trichotomy q post.length with hqP | hqP | hqP
    · exact False.elim (by omega)
    · exact False.elim (by omega)
    · -- Value against rest: transitivity through the rest head.
      have hav : a = v := by
        rw [hvP] at ha
        exact (Option.some_inj.mp ha).symm
      have hb' : rest[q - post.length - 1]? = some b := by
        have h1 : (post ++ (v :: rest))[q]? = (v :: rest)[q - post.length]? :=
          happendR q (by omega)
        rw [h1] at hb
        have h2 : q - post.length = (q - post.length - 1) + 1 := by omega
        rw [h2, List.getElem?_cons_succ] at hb
        exact hb
      cases hrest : rest with
      | nil =>
        simp [hrest] at hb'
      | cons x xs =>
        have hxv : (v.slt x) = true := hgt x xs hrest
        have hbx : (b.slt x) = false := by
          by_cases hj : q - post.length - 1 = 0
          · have hbx0 : b = x := by
              have h0 : rest[0]? = some x := by simp [hrest]
              rw [hj] at hb'
              exact (Option.some_inj.mp (by rw [h0] at hb'; exact hb')).symm
            rw [hbx0]
            exact sortedInsert_slt_irrefl x
          · have hPx : (post ++ rest)[post.length]? = some x := by
              rw [hvsR post.length (Nat.le_refl _)]
              simp [hrest]
            have hPb : (post ++ rest)[post.length + (q - post.length - 1)]? =
                some b := by
              have h1 : (post ++ rest)[post.length + (q - post.length - 1)]? =
                  rest[post.length + (q - post.length - 1) - post.length]? :=
                hvsR _ (by omega)
              rw [h1]
              have h2 : post.length + (q - post.length - 1) - post.length =
                  q - post.length - 1 := by omega
              rw [h2]; exact hb'
            have hjlen : q - post.length - 1 < rest.length :=
              (List.getElem?_eq_some_iff.mp hb').1
            have hqlen : post.length + (q - post.length - 1) <
                (post ++ rest).length := by
              rw [hlenV]; omega
            exact hsorted post.length (post.length + (q - post.length - 1))
              (by omega) (by omega) hqlen x b hPx hPb
        rw [hav]
        by_cases hvb : (b.slt v) = true
        · exact False.elim (by
            have ht := sortedInsert_slt_trans hvb hxv
            simp [ht] at hbx)
        · cases h : (b.slt v) with
          | true => exact False.elim (hvb h)
          | false => rfl
  · -- Both in the rest: ride the input window shifted.
    have hqP : post.length < q := by omega
    have ha' : rest[p - post.length - 1]? = some a := by
      have h1 : (post ++ (v :: rest))[p]? = (v :: rest)[p - post.length]? :=
        happendR p (by omega)
      rw [h1] at ha
      have h2 : p - post.length = (p - post.length - 1) + 1 := by omega
      rw [h2, List.getElem?_cons_succ] at ha
      exact ha
    have hb' : rest[q - post.length - 1]? = some b := by
      have h1 : (post ++ (v :: rest))[q]? = (v :: rest)[q - post.length]? :=
        happendR q (by omega)
      rw [h1] at hb
      have h2 : q - post.length = (q - post.length - 1) + 1 := by omega
      rw [h2, List.getElem?_cons_succ] at hb
      exact hb
    have haV : (post ++ rest)[p - 1]? = some a := by
      have h1 : (post ++ rest)[p - 1]? = rest[p - 1 - post.length]? :=
        hvsR (p - 1) (by omega)
      rw [h1]
      have h2 : p - 1 - post.length = p - post.length - 1 := by omega
      rw [h2]; exact ha'
    have hbV : (post ++ rest)[q - 1]? = some b := by
      have h1 : (post ++ rest)[q - 1]? = rest[q - 1 - post.length]? :=
        hvsR (q - 1) (by omega)
      rw [h1]
      have h2 : q - 1 - post.length = q - post.length - 1 := by omega
      rw [h2]; exact hb'
    have hjlen : q - post.length - 1 < rest.length :=
      (List.getElem?_eq_some_iff.mp hb').1
    have hqlen : q - 1 < (post ++ rest).length := by
      rw [hlenV]; omega
    exact hsorted (p - 1) (q - 1) (by omega) (by omega) hqlen a b haV hbV

/-! ## Chain transports: prefix chains ride allocation+stores -/

/-- A prefix chain rides the fresh allocation: every visited node
    differs from the fresh cell (live below it). -/
theorem prefixChain_alloc_other {m : Mem} (hmark : Mark m)
    {s e : Option Addr} {nodes : List (Addr × Nat × BitVec 32)}
    (h : PrefixChain m s nodes e) (d : List (BitVec 32)) :
    PrefixChain (memAllocData m d).1 s nodes e := by
  induction h with
  | nil => exact .nil
  | cons hnode _ ih =>
    have hfind : memFind m _ = some _ := hnode
    have hne : _ ≠ m.next :=
      Nat.ne_of_lt (live_lt_of_memFind hmark hfind)
    exact .cons (nodeAt_alloc_other hnode d hne) ih

/-- A prefix chain rides a store elsewhere: every visited node
    differs from the stored cell. -/
theorem prefixChain_store_other {m m' : Mem} {c : Addr}
    {s e : Option Addr} {nodes : List (Addr × Nat × BitVec 32)}
    (h : PrefixChain m s nodes e)
    (hout : ∀ a, a ∈ nodes → a.1 ≠ c)
    (hstore : ∃ t i w, memStore m c t i w = .ok m') :
    PrefixChain m' s nodes e := by
  obtain ⟨t, i, w, hstore⟩ := hstore
  induction h with
  | nil => exact .nil
  | cons hnode hrest ih =>
    rename_i N E TL A T W
    clear hrest
    have hne : (A, T, W).1 ≠ c :=
      hout _ (List.mem_cons.mpr (Or.inl rfl))
    have houtT : ∀ a, a ∈ TL → a.1 ≠ c := by
      intro a ha
      exact hout a (List.mem_cons.mpr (Or.inr ha))
    exact .cons (nodeAt_store_other_fwd hnode hstore hne)
      (ih houtT)

/-! ## Chase invariant: chain + oracle equation through the chase -/

/-- A chase starting from a visited predecessor stays visited:
    the result `prev` is always `some` (the chase only ever assigns
    `some`). -/
theorem listSortedInsertChase_prev_some (F : Nat)
    (m : Mem) (prev cur : Option Addr) (v : BitVec 32)
    (p q : Option Addr)
    (hne : prev ≠ none)
    (hC : listSortedInsertChase F m prev cur v = .ok (p, q)) :
    ∃ b, p = some b := by
  induction F generalizing prev cur with
  | zero =>
    cases cur with
    | none =>
      have hC' : listSortedInsertChase 0 m prev none v =
          .ok (prev, none) := by
        simp [listSortedInsertChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      obtain ⟨rfl, -⟩ := hC
      cases p with
      | none => exact False.elim (hne rfl)
      | some b => exact ⟨b, rfl⟩
    | some a =>
      have hC' : listSortedInsertChase 0 m prev (some a) v =
          .error .AssertFail := by
        simp [listSortedInsertChase]
      rw [hC'] at hC
      cases hC
  | succ F ih =>
    cases cur with
    | none =>
      have hC' : listSortedInsertChase (F + 1) m prev none v =
          .ok (prev, none) := by
        simp [listSortedInsertChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      obtain ⟨rfl, -⟩ := hC
      cases p with
      | none => exact False.elim (hne rfl)
      | some b => exact ⟨b, rfl⟩
    | some a =>
      cases hmf : memFind m a with
      | none =>
        have hC' : listSortedInsertChase (F + 1) m prev (some a) v =
            .error .AssertFail := by
          simp only [listSortedInsertChase, hmf]
        rw [hC'] at hC
        cases hC
      | some bb =>
        cases hml : memLoad m a bb.tag 0 with
        | error e =>
          have hC' : listSortedInsertChase (F + 1) m prev (some a) v =
              .error e := by
            simp only [listSortedInsertChase, hmf, hml]
          rw [hC'] at hC
          cases hC
        | ok w =>
          by_cases hstop : (v.slt w) = true
          · have hC' : listSortedInsertChase (F + 1) m prev (some a) v =
                .ok (prev, some a) := by
              simp only [listSortedInsertChase, hmf, hml, if_pos hstop]
            rw [hC'] at hC
            simp only [Except.ok.injEq] at hC
            obtain ⟨rfl, -⟩ := hC
            cases p with
            | none => exact False.elim (hne rfl)
            | some b => exact ⟨b, rfl⟩
          · cases hml1 : memLoad m a bb.tag 1 with
            | error e =>
              have hC' : listSortedInsertChase (F + 1) m prev (some a) v =
                  .error e := by
                simp only [listSortedInsertChase, hmf, hml,
                  if_neg hstop, hml1]
              rw [hC'] at hC
              cases hC
            | ok w' =>
              have hC' : listSortedInsertChase (F + 1) m prev (some a) v =
                  listSortedInsertChase F m (some a)
                    (addrOfWord w') v := by
                simp only [listSortedInsertChase, hmf, hml,
                  if_neg hstop, hml1]
              rw [hC'] at hC
              exact ih (some a) (addrOfWord w') (by simp) hC

/-- Chase invariant (erase-style): the chase threads the visited
    prefix chain, the oracle equation for the visited prefix, the
    no-greater facts, the stop-greater fact, the prev-nil/prev-node
    correspondence, and the suffix segment. -/
theorem listSortedInsertChase_invariant (F : Nat)
    (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (top : Option Addr) (nodes : List (Addr × Nat × BitVec 32))
    (prev cur : Option Addr)
    (hchain : PrefixChain m top nodes cur) (v : BitVec 32)
    (suf : List (BitVec 32)) (hseg : ListSeg m cur suf)
    (hord : ∀ a ∈ preVals nodes, (v.slt a) = false)
    (hplink : ∀ p, prev = some p → ∃ tp wp, nodeAt m p tp wp cur)
    (hprevnil : prev = none → nodes = [])
    (hprevnodes : ∀ p, prev = some p →
      ∃ init lt lw, nodes = init ++ [(p, lt, lw)])
    (hlen : suf.length ≤ F)
    (p q : Option Addr)
    (hC : listSortedInsertChase F m prev cur v = .ok (p, q)) :
    ∃ post rest nodes₁, preVals nodes₁ = preVals nodes ++ post ∧
      suf = post ++ rest ∧
      PrefixChain m top nodes₁ q ∧
      ListSeg m q rest ∧
      (∀ a ∈ post, (v.slt a) = false) ∧
      (∀ x xs, rest = x :: xs → (v.slt x) = true) ∧
      (∀ b, p = some b → ∃ tb wb, nodeAt m b tb wb q) ∧
      (p = none → nodes₁ = nodes) ∧
      (∀ b, p = some b →
        ∃ init tb wb, nodes₁ = init ++ [(b, tb, wb)]) := by
  induction F generalizing prev cur nodes suf with
  | zero =>
    cases cur with
    | none =>
      cases hseg with
      | nil =>
        have hC' : listSortedInsertChase 0 m prev none v =
            .ok (prev, none) := by
          simp [listSortedInsertChase]
        rw [hC'] at hC
        simp only [Except.ok.injEq, Prod.mk.injEq] at hC
        obtain ⟨rfl, rfl⟩ := hC
        refine ⟨[], [], nodes, by simp, by simp, hchain, .nil,
          fun _ h => False.elim (by simp at h),
          fun _ _ h => False.elim (by simp at h),
          fun b hb => hplink b hb,
          fun _ => rfl,
          fun b hb => hprevnodes b hb⟩
    | some a =>
      cases hseg with
      | cons _ t2 =>
        obtain ⟨vs', rfl⟩ := listSegVals t2
        exact False.elim (by
          simp only [List.length_cons] at hlen
          omega)
  | succ F ih =>
    cases cur with
    | none =>
      cases hseg with
      | nil =>
        have hC' : listSortedInsertChase (F + 1) m prev none v =
            .ok (prev, none) := by
          simp [listSortedInsertChase]
        rw [hC'] at hC
        simp only [Except.ok.injEq] at hC
        obtain ⟨rfl, rfl⟩ := hC
        exact ⟨[], [], nodes, by simp, by simp, hchain, .nil,
          fun _ h => False.elim (by simp at h),
          fun _ _ h => False.elim (by simp at h),
          fun b hb => hplink b hb,
          fun _ => rfl,
          fun b hb => hprevnodes b hb⟩
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v₀, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem0 : memLoad m a t' 0 = .ok v₀ :=
          nodeLoadVal hnode
        by_cases hstop : (v.slt v₀) = true
        · have hC' : listSortedInsertChase (F + 1) m prev
              (some a) v = .ok (prev, some a) := by
            unfold listSortedInsertChase
            simp only [hfb, hmem0, if_pos hstop]
          rw [hC'] at hC
          simp only [Except.ok.injEq] at hC
          obtain ⟨rfl, rfl⟩ := hC
          refine ⟨[], v₀ :: vs', nodes, by simp, by simp, hchain, ?_,
            fun a' ha' => False.elim (by simp at ha'),
            fun x xs hx => ?_, fun b hb => hplink b hb,
            fun _ => rfl, fun b hb => hprevnodes b hb⟩
          · exact ListSeg.cons hnode t2
          · simp only [List.cons.injEq] at hx
            obtain ⟨rfl, -⟩ := hx
            exact hstop
        · have hmem1 : memLoad m a t' 1 = .ok (linkWord nxt) :=
            nodeLoadNext hnode
          have hle : (v.slt v₀) = false := by
            cases hv : (v.slt v₀) with
            | true => exact False.elim (hstop hv)
            | false => rfl
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
          simp only [listSortedInsertChase, hfb, hmem0,
            if_neg hstop, hmem1] at hC
          have hchain' : PrefixChain m top (nodes ++ [(a, t', v₀)])
              (addrOfWord (linkWord nxt)) :=
            PrefixChain.snoc_extend hchain hnode rfl hdec.symm
          have hord' : ∀ a' ∈ preVals (nodes ++ [(a, t', v₀)]),
              (v.slt a') = false := by
            intro a' ha'
            simp only [preVals, List.map_append, List.mem_append,
              List.mem_map, List.mem_singleton] at ha'
            cases ha' with
            | inl h =>
              obtain ⟨y, hym, rfl⟩ := h
              exact hord _ (List.mem_map.mpr ⟨y, hym, rfl⟩)
            | inr h =>
              have hv : v₀ = a' := by simpa [preVals] using h
              subst hv
              exact hle
          have hplink' : ∀ b : Addr, (some a) = some b →
              ∃ tb wb, nodeAt m b tb wb (addrOfWord (linkWord nxt)) := by
            intro b hb
            cases hb
            exact ⟨t', v₀, by rw [hdec]; exact hnode⟩
          have hprevnil' : (some a) = none → nodes ++ [(a, t', v₀)] = [] := by
            intro h
            cases h
          have hprevnodes' : ∀ b, (some a) = some b →
              ∃ init lt lw,
                nodes ++ [(a, t', v₀)] = init ++ [(b, lt, lw)] := by
            intro b hb
            cases hb
            exact ⟨nodes, t', v₀, rfl⟩
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          have hsegI : ListSeg m (addrOfWord (linkWord nxt)) vs' := by
            rw [hdec]
            exact t2
          obtain ⟨post', rest', nodes₁, hpost', hsplit', hchain₁,
              hseg₁, hord₁, hgt₁, hprev₁, hnil₁, hprevnodes₁⟩ :=
            ih (prev := some a) (cur := addrOfWord (linkWord nxt))
              (nodes := nodes ++ [(a, t', v₀)]) (suf := vs')
              (hchain := hchain') (hseg := hsegI)
              (hord := hord') (hplink := hplink')
              (hprevnil := hprevnil') (hprevnodes := hprevnodes')
              (hlen := hlen') (hC := hC)
          refine ⟨v₀ :: post', rest', nodes₁, ?_, ?_, hchain₁, hseg₁,
            ?_, hgt₁, hprev₁, ?_, hprevnodes₁⟩
          · rw [hpost']
            simp [preVals]
          · simp only [List.cons_append]
            rw [hsplit']
          · intro a' ha'
            simp only [List.mem_cons] at ha'
            cases ha' with
            | inl h =>
              cases h
              exact hle
            | inr h => exact hord₁ _ h
          · intro hp
            obtain ⟨b, hb⟩ := listSortedInsertChase_prev_some F m
              (some a) _ _ _ _ (by simp) hC
            rw [hb] at hp
            cases hp

/-! ## Forward-contract correctness: memory, sortedness, permutation -/

/-- Entry correctness at the forward-mirror level: the mirror runs
    the chase, allocates, stores, and swings to exactly the
    `sortedInsert` output — sorted, a permutation of `v :: vs`. -/
theorem listSortedInsertFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmark : Mark m)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hroom : m.next + 1 < 2 ^ 32)
    (hseg : ListSeg m head vs)
    (hsorted : SortedWindow vs 0 vs.length)
    (hlen : vs.length ≤ F)
    (hfwd : listSortedInsertFwd F m head v = .ok (m', hd')) :
    ListSeg m' hd' (sortedInsert v vs) ∧
    SortedWindow (sortedInsert v vs) 0 (sortedInsert v vs).length ∧
    List.Perm (sortedInsert v vs) (v :: vs) := by
  -- The chase must have succeeded (mirrors the entry leg).
  cases hC0 : listSortedInsertChase F m none head v with
  | error e =>
    simp only [listSortedInsertFwd, hC0] at hfwd
    cases hfwd
  | ok res =>
    obtain ⟨p, q⟩ := res
    -- Chain invariant at the top (empty prefix, head start).
    obtain ⟨post, rest, nodes₁, hpost, hsplit, hchain, hsegR, hord,
        hgt, hprev, hnil, hprevnodes⟩ :=
      listSortedInsertChase_invariant F m hex head [] none head
        .nil v vs hseg (by simp [preVals])
        (by intro b hb; cases hb)
        (fun _ => rfl) (by intro b hb; cases hb)
        hlen p q hC0
    have hpostEq : preVals nodes₁ = post := by
      simpa [preVals] using hpost
    -- Oracle equation, permutation, sortedness (branch-free).
    have horacle : sortedInsert v vs = post ++ [v] ++ rest := by
      rw [hsplit]
      exact sortedInsert_prefix v post rest hord hgt
    have hperm : List.Perm (sortedInsert v vs) (v :: vs) := by
      rw [horacle, hsplit]
      exact perm_insert_middle post v rest
    have hsortedOut : SortedWindow (sortedInsert v vs) 0
        (sortedInsert v vs).length := by
      rw [horacle]
      have hsV : SortedWindow (post ++ rest) 0 (post ++ rest).length := by
        rw [← hsplit]; exact hsorted
      exact sortedInsert_sorted v post rest hord hgt hsV
    -- Fresh allocation and the two fresh-cell stores.
    have hmfresh : memFind m m.next = none := hmark _ (Nat.le_refl _)
    have hA : (memAlloc m 2).2 = m.next := memAlloc_next m 2
    have hmark1 : Mark (memAlloc m 2).1 := freshAbove_alloc m 2 hmark
    have hfindN : memFind (memAlloc m 2).1 (memAlloc m 2).2 =
        some ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ :=
      memFind_memAlloc m 2
    have hcell0 : cellsAt (memAlloc m 2).1 (memAlloc m 2).2
        ((memAlloc m 2).2) [0, 0] := hfindN
    obtain ⟨m2, hS1⟩ := memStore_cellsAt_ok_insert (i := 0) hcell0
      (by decide)
    have hcell1 : cellsAt m2 (memAlloc m 2).2 ((memAlloc m 2).2)
        [v, 0] := by
      have h := memFind_cellsAt_store _ _ _ _ _ _ _ hcell0
        (by decide) hS1
      simpa using h
    obtain ⟨m3, hS2⟩ := memStore_cellsAt_ok_insert (i := 1) hcell1
      (by simp)
    have hfindN2 : memFind m2 (memAlloc m 2).2 =
        some ⟨(memAlloc m 2).2, true, [v, 0]⟩ := hcell1
    have hmark2 : Mark m2 := freshAbove_store hmark1 hS1
    have hmark3 : Mark m3 := freshAbove_store hmark2 hS2
    -- Exactness rides along (fresh cell needs room).
    have hex1 : ∀ x, (memFind (memAlloc m 2).1 x).isSome = true →
        x + 1 < 2 ^ 32 := by
      intro x hx
      by_cases heq : x = m.next
      · subst heq
        exact hroom
      · have e : memFind (memAlloc m 2).1 x = memFind m x :=
          memFind_memAllocData_other m [0, 0] x heq
        rw [e] at hx
        exact hex x hx
    have hagree : ∀ a, a ≠ m.next → memFind m2 a = memFind m a := by
      intro a ha
      have e1 : memFind m2 a = memFind (memAlloc m 2).1 a :=
        memFind_memStore_other _ _ _ _ _ _ _ hS1 ha
      have e2 : memFind (memAlloc m 2).1 a = memFind m a :=
        memFind_memAllocData_other m [0, 0] a ha
      rw [e1, e2]
    have hex2 : ∀ x, (memFind m2 x).isSome = true → x + 1 < 2 ^ 32 := by
      intro x hx
      by_cases heq : x = m.next
      · subst heq
        exact hroom
      · have e : memFind m2 x = memFind m x := hagree x heq
        rw [e] at hx
        exact hex x hx
    have hagree3 : ∀ a, a ≠ m.next → memFind m3 a = memFind m a := by
      intro a ha
      have e1 : memFind m3 a = memFind m2 a :=
        memFind_memStore_other _ _ _ _ _ _ _ hS2 ha
      rw [e1]
      exact hagree a ha
    have hex3 : ∀ x, (memFind m3 x).isSome = true → x + 1 < 2 ^ 32 := by
      intro x hx
      by_cases heq : x = m.next
      · subst heq
        exact hroom
      · have e : memFind m3 x = memFind m x := hagree3 x heq
        rw [e] at hx
        exact hex x hx
    -- Suffix rides the allocation, then both fresh stores.
    have hsegR1 : ListSeg (memAlloc m 2).1 q rest :=
      ListSeg_alloc_other hmark hsegR
    have houtR1 : ∀ b, SegMem (m := (memAlloc m 2).1) q b →
        b ≠ (memAlloc m 2).2 := by
      intro b hb
      have hlt := SegMem_alloc_other_lt hex hmark hroom hsegR1 hsegR hb
      rw [hA]
      exact Nat.ne_of_lt hlt
    have hsegR2 : ListSeg m2 q rest :=
      ListSeg.store_other_mem hsegR1 houtR1 hS1
    have hhead1 : ∀ y, q = some y → y ≠ (memAlloc m 2).2 := by
      intro y hy
      have h := hsegR
      rw [hy] at h
      cases h with
      | cons hnode _ =>
        have hfb : memFind m y = some _ := hnode
        have hlt := live_lt_of_memFind hmark hfb
        rw [hA]
        exact Nat.ne_of_lt hlt
    have houtR2 : ∀ b, SegMem (m := m2) q b →
        b ≠ (memAlloc m 2).2 :=
      SegMem_store_avoid hS1 hsegR1 hex1 hex2 hhead1 houtR1
    have hsegR3 : ListSeg m3 q rest :=
      ListSeg.store_other_mem hsegR2 houtR2 hS2
    have houtR3 : ∀ b, SegMem (m := m3) q b →
        b ≠ (memAlloc m 2).2 :=
      SegMem_store_avoid hS2 hsegR2 hex2 hex3 hhead1 houtR2
    -- Branch on the predecessor: head swing vs link swing.
    cases hp : p with
    | none =>
      subst hp
      have hnilEq : nodes₁ = [] := hnil rfl
      have hpostNil : post = [] := by
        rw [← hpostEq, hnilEq]; rfl
      -- Pin the second store's value before the mirror simp.
      have hcellND3 : cellsAt m3 (memAlloc m 2).2
          ((memAlloc m 2).2) [v, linkWord q] := by
        have h := memFind_cellsAt_store m2 (memAlloc m 2).2
          ((memAlloc m 2).2) 1 [v, 0] (linkWord q) m3 hcell1
          (by simp) hS2
        simpa using h
      have hnodeND3 : nodeAt m3 (memAlloc m 2).2
          ((memAlloc m 2).2) v q := hcellND3
      simp only [listSortedInsertFwd, hC0, hfindN, hS1,
        hfindN2, hS2] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨e1, e2⟩ := hfwd
      subst e1
      subst e2
      refine ⟨?_, ?_, ?_⟩
      · simpa [horacle, hpostNil] using ListSeg.cons hnodeND3 hsegR3
      · simpa [horacle, hpostNil] using hsortedOut
      · simpa [horacle, hpostNil] using hperm
    | some b =>
      subst hp
      obtain ⟨init, tb, wb, hnodes⟩ := hprevnodes b rfl
      obtain ⟨tb', wb', hnodeP⟩ := hprev b rfl
      -- Carry the predecessor across the allocation+stores.
      have hfbP : memFind m b = some _ := hnodeP
      have hneP : b ≠ m.next :=
        Nat.ne_of_lt (live_lt_of_memFind hmark hfbP)
      have hneP2 : b ≠ (memAlloc m 2).2 := by
        rw [hA]
        exact hneP
      have hnodeP1 : nodeAt (memAlloc m 2).1 b tb' wb' q :=
        nodeAt_alloc_other hnodeP _ hneP
      have hnodeP2 : nodeAt m2 b tb' wb' q :=
        nodeAt_store_other_fwd hnodeP1 hS1 hneP2
      have hnodeP3 : nodeAt m3 b tb' wb' q :=
        nodeAt_store_other_fwd hnodeP2 hS2 hneP2
      have hfindP3 : memFind m3 b =
          some ⟨tb', true, [wb', linkWord q]⟩ := hnodeP3
      have hcellP : cellsAt m3 b tb' [wb', linkWord q] := hnodeP3
      obtain ⟨m4, hS3⟩ := memStore_cellsAt_ok_insert (i := 1)
        (x := linkWord (some (memAlloc m 2).2)) hcellP
        (by simp)
      -- Chain-last and chase-last agree on the payload.
      have hchain0 : PrefixChain m head (init ++ [(b, tb, wb)]) q := by
        rw [← hnodes]; exact hchain
      obtain ⟨_, _, hchainLast0⟩ := PrefixChain.split hchain0
      cases hchainLast0 with
      | cons hnodeB0 hrestB0 =>
        cases hrestB0 with
        | nil =>
          have hmemB : memFind m b =
              some ⟨tb, true, [wb, linkWord q]⟩ := hnodeB0
          have hmemP : memFind m b =
              some ⟨tb', true, [wb', linkWord q]⟩ := hnodeP
          have hwbEq : wb' = wb := by
            rw [hmemP] at hmemB
            cases hmemB
            rfl
          rw [hwbEq] at hnodeP1 hnodeP2 hnodeP3 hfindP3 hcellP
          -- Exactness past the predecessor swing.
          have hagree4 : ∀ a, a ≠ b → memFind m4 a = memFind m3 a :=
            fun a ha => memFind_memStore_other _ _ _ _ _ _ _ hS3 ha
          have hex4 : ∀ x, (memFind m4 x).isSome = true →
              x + 1 < 2 ^ 32 := by
            intro x hx
            by_cases heq : x = b
            · have hnodePc := hnodeP3
              unfold nodeAt cellsAt at hnodePc
              have hfb : (memFind m3 b).isSome = true := by
                simp [hnodePc]
              have h2 := hex3 b hfb
              rwa [heq]
            · have e : memFind m4 x = memFind m3 x := hagree4 x heq
              rw [e] at hx
              exact hex3 x hx
          -- Suffix rides the swing (acyclicity: head not in tail).
          have houtR3b : ∀ x, SegMem (m := m3) q x → x ≠ b :=
            ListSeg_head_notin_tail hnodeP3 hsegR3 hex3
          have hhead3 : ∀ y, q = some y → y ≠ b := by
            intro y hy
            have h := hsegR3
            rw [hy] at h
            cases h with
            | cons hnode _ =>
              have hmem : SegMem (m := m3) q y := by
                rw [hy]
                exact SegMem.here hnode
              exact houtR3b y hmem
          have hsegR4 : ListSeg m4 q rest :=
            ListSeg.store_other_mem hsegR3 houtR3b hS3
          -- Prefix chain rides everything to the swing, then across.
          have hchain1 : PrefixChain (memAlloc m 2).1 head nodes₁ q :=
            prefixChain_alloc_other hmark hchain [0, 0]
          have houtC1 : ∀ a, a ∈ nodes₁ → a.1 ≠ (memAlloc m 2).2 := by
            intro a ha
            have hlt := SegMem_mem_lt (prefixChain_mem hchain a ha) hmark
            rw [hA]
            exact Nat.ne_of_lt hlt
          have hchain2 : PrefixChain m2 head nodes₁ q :=
            prefixChain_store_other hchain1 houtC1 ⟨_, _, _, hS1⟩
          have hchain3 : PrefixChain m3 head nodes₁ q :=
            prefixChain_store_other hchain2 houtC1 ⟨_, _, _, hS2⟩
          -- Head segment rides to the swing (for the acyclicity use).
          have hsegH1 : ListSeg (memAlloc m 2).1 head vs :=
            ListSeg_alloc_other hmark hseg
          have houtH1 : ∀ b, SegMem (m := (memAlloc m 2).1) head b →
              b ≠ (memAlloc m 2).2 := by
            intro b hb
            have hlt := SegMem_alloc_other_lt hex hmark hroom
              hsegH1 hseg hb
            rw [hA]
            exact Nat.ne_of_lt hlt
          have hheadH1 : ∀ y, head = some y → y ≠ (memAlloc m 2).2 := by
            intro y hy
            have h := hseg
            rw [hy] at h
            cases h with
            | cons hnode _ =>
              have hfb : memFind m y = some _ := hnode
              have hlt := live_lt_of_memFind hmark hfb
              rw [hA]
              exact Nat.ne_of_lt hlt
          have hsegH2 : ListSeg m2 head vs :=
            ListSeg.store_other_mem hsegH1 houtH1 hS1
          have houtH2 : ∀ b, SegMem (m := m2) head b →
              b ≠ (memAlloc m 2).2 :=
            SegMem_store_avoid hS1 hsegH1 hex1 hex2 hheadH1 houtH1
          have hsegH3 : ListSeg m3 head vs :=
            ListSeg.store_other_mem hsegH2 houtH2 hS2
          have hseg3 : ListSeg m3 head (post ++ rest) := by
            rw [← hsplit]; exact hsegH3
          -- Chain links are allocated in the swing memory.
          have hagree3b : ∀ a, a ≠ (memAlloc m 2).2 →
              memFind m3 a = memFind m a := by
            intro a ha
            have ha' : a ≠ m.next := by
              rw [hA] at ha
              exact ha
            exact hagree3 a ha'
          have hallocC3 : ∀ i c, chainNext nodes₁ q i = some c →
              (memFind m3 c).isSome = true := by
            intro i c hc
            unfold chainNext at hc
            cases hni : nodes₁[i + 1]? with
            | none =>
              simp only [hni] at hc
              have hfb : (memFind m c).isSome = true := by
                have h := hsegR
                rw [hc] at h
                cases h with
                | cons hnode _ =>
                  unfold nodeAt cellsAt at hnode
                  simp [hnode]
              have hne : c ≠ (memAlloc m 2).2 := by
                have h := hsegR
                rw [hc] at h
                cases h with
                | cons hnode _ =>
                  have hfb' : memFind m c = some _ := hnode
                  have hlt := live_lt_of_memFind hmark hfb'
                  rw [hA]
                  exact Nat.ne_of_lt hlt
              rw [hagree3b c hne]
              exact hfb
            | some y =>
              simp only [hni] at hc
              obtain rfl := Option.some_inj.mp hc
              have hfb : (memFind m y.1).isSome = true :=
                SegMem_mem_alloc (prefixChain_mem hchain y
                  (List.mem_of_getElem? hni))
              have hne : y.1 ≠ (memAlloc m 2).2 := by
                have hlt := SegMem_mem_lt
                  (prefixChain_mem hchain y (List.mem_of_getElem? hni))
                  hmark
                rw [hA]
                exact Nat.ne_of_lt hlt
              rw [hagree3b y.1 hne]
              exact hfb
          have hpost' : preVals (init ++ [(b, tb, wb)]) = post := by
            rw [← hnodes]; exact hpostEq
          have hchain3' : PrefixChain m3 head
              (init ++ [(b, tb, wb)]) q := by
            rw [← hnodes]; exact hchain3
          have hallocC3' : ∀ i c, chainNext (init ++ [(b, tb, wb)]) q i =
              some c → (memFind m3 c).isSome = true := by
            rw [← hnodes]
            exact hallocC3
          have houtC3 : ∀ x ∈ init, x.1 ≠ b :=
            chain_last_notin_init hex3 hchain3' hpost' hseg3 hallocC3'
          obtain ⟨_, hchainInit, hchainLast⟩ :=
            PrefixChain.split hchain3'
          cases hchainLast with
          | cons hnodeB hrestB =>
            cases hrestB with
            | nil =>
              have hchain4 : PrefixChain m4 head init (some b) :=
                prefixChain_store_other hchainInit houtC3
                  ⟨_, _, _, hS3⟩
              -- Tail, fresh node, swung node assemble the output.
              have htail4 : ListSeg m4 q rest := hsegR4
              have hltb : b < m.next :=
                live_lt_of_memFind hmark hfbP
              have hneNDb : (memAlloc m 2).2 ≠ b := by
                rw [hA]
                exact Nat.ne_of_gt hltb
              have hcellND3 : cellsAt m3 (memAlloc m 2).2
                  ((memAlloc m 2).2) [v, linkWord q] := by
                have h := memFind_cellsAt_store m2
                  (memAlloc m 2).2 ((memAlloc m 2).2) 1 [v, 0]
                  (linkWord q) m3 hcell1 (by simp) hS2
                simpa using h
              have hnodeND3 : nodeAt m3 (memAlloc m 2).2
                  ((memAlloc m 2).2) v q := hcellND3
              have hnodeND4 : nodeAt m4 (memAlloc m 2).2
                  ((memAlloc m 2).2) v q :=
                nodeAt_store_other_fwd hnodeND3 hS3 hneNDb
              have hnodeB4 : nodeAt m4 b tb' wb (some (memAlloc m 2).2) :=
                nodeStoreNext_nodeAt hnodeP3 hS3
              have hbridge : preVals (init ++ [(b, tb, wb)]) =
                  preVals init ++ [wb] := by
                simp [preVals]
              have hpostEq2 : preVals init ++ [wb] = post := by
                rw [← hbridge]; exact hpost'
              have hsegOut : ListSeg m4 head (post ++ [v] ++ rest) := by
                have hassem : preVals init ++ (wb :: v :: rest) =
                    post ++ [v] ++ rest := by
                  rw [← hpostEq2, List.append_assoc, List.append_assoc,
                    List.singleton_append, List.singleton_append]
                rw [← hassem]
                exact PrefixChain.appendSeg hchain4
                  (ListSeg.cons hnodeB4
                    (ListSeg.cons hnodeND4 htail4))
              simp only [listSortedInsertFwd, hC0, hfindN, hS1,
                hfindN2, hS2, hfindP3, hS3] at hfwd
              simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
              obtain ⟨e1, e2⟩ := hfwd
              subst e1
              subst e2
              refine ⟨?_, ?_, ?_⟩
              · rw [horacle]; exact hsegOut
              · exact hsortedOut
              · exact hperm

