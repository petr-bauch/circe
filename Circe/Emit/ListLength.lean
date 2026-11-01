/-
Circe.Emit.ListLength — L-ptr second shape: read-only `list_length`
over caller-owned `Node { val, next }`.

The corpus (`tests/cpp/list_length.cpp`, entry
`unsigned long list_length(Node *head)`) captures a single
draining chase: seed `n = 0` / `cur = head`, then
`while_ cur != nullptr` with body `cur = cur->next`
(link load), `n = n + 1` (wrapping `uadd` — no `nsw` in the
corpus). The entry returns the count; memory is never stored
(read-only, so no frame reasoning is needed — this is the
third-use test of the `ListSeg`/`chaseN` bridge after the
reversal: only the `ListSeg` cons walk plus the link
roundtrip). The only branch is the drain condition; the link
load is loud on a dangling cursor (miss aborts, short reads
abort), cyclic input exhausts fuel. Payloads are untouched.

Pointers cross the boundary as opaque node capabilities
(`ptrVal`, `none` null); the counter rides a `Nat` in the
forward and `BitVec.ofNat 64 k` in the environment (the
`ofNat64_add_one` bridge). Termination is by fuel lockstep.
-/
import Circe.Emit.LinkedReverse
import Circe.Emit.Fragment

/-! ## L: `list_length` entry -/

/-- Mangled name of the count entry. -/
def listLengthName : String :=
  "_Z11list_lengthP4Node"

/-- The fused entry seed: zero counter, head cursor (the G5a
    init-all-loop-vars convention). -/
def listLengthSeed : CStmt :=
  .seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
  (.let_ "cur" nodeTy (.var "head"))

/-- One count iteration: chase advance, counter bump. -/
def listLengthBody : CStmt :=
  .seq (.assign "cur" (.pgetNext (.var "cur")))
  (.assign "n" (.uadd (.var "n") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The chase: `cur != nullptr`. -/
def listLengthOuter : CStmt :=
  .while_ (.une (.var "cur") (.lit .nullptr)) listLengthBody

/-- Canonical CoreIR for `list_length`: the seed, the chase, and
    the count return. -/
def listLengthFunc : Func :=
  ⟨listLengthName,
   [{ name := "head", ty := nodeTy, role := .owned }],
   .u 64,
   (.seq listLengthSeed
     (.seq listLengthOuter (.return_ (.var "n"))))⟩

/-- Count environment: the head, counter, and cursor slots (the
    layout stays empty — link ops resolve through the block's
    own tag). -/
def mkListLengthEnv (head : Option Addr) (k : Nat)
    (cur : Option Addr) : Env :=
  [("cur", .ptrVal cur), ("n", .u64 (BitVec.ofNat 64 k)),
    ("head", .ptrVal head)]

theorem mkListLengthEnv_cur (head : Option Addr) (k : Nat)
    (cur : Option Addr) :
    envLookup (mkListLengthEnv head k cur) "cur" =
      some (.ptrVal cur) := by
  simp [mkListLengthEnv, envLookup]

theorem mkListLengthEnv_n (head : Option Addr) (k : Nat)
    (cur : Option Addr) :
    envLookup (mkListLengthEnv head k cur) "n" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkListLengthEnv, envLookup]

theorem mkListLengthEnv_head (head : Option Addr) (k : Nat)
    (cur : Option Addr) :
    envLookup (mkListLengthEnv head k cur) "head" =
      some (.ptrVal head) := by
  simp [mkListLengthEnv, envLookup]

/-! ## Fuel-threaded count forward -/

/-- Count forward: mirrors `listLengthOuter` iteration for
    iteration (same fuel, same memory ops — reads only, so the
    memory is threaded unchanged). Zero fuel exits cleanly on a
    null cursor and aborts loudly on a live one — the S3a fuel
    contract. -/
def listLengthOuterFwd (F : Nat) (m : Mem) (cur : Option Addr)
    (n : Nat) : Result (Mem × Nat) :=
  match F with
  | 0 =>
    match cur with
    | none => .ok (m, n)
    | some _ => .error .AssertFail
  | F + 1 =>
    match cur with
    | none => .ok (m, n)
    | some a =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 1 with
        | .error e => .error e
        | .ok w => listLengthOuterFwd F m (addrOfWord w) (n + 1)

/-- Entry mirror: seed the counter and cursor, then the chase. -/
def listLengthFwd (F : Nat) (m : Mem) (head : Option Addr) :
    Result (Mem × Nat) :=
  listLengthOuterFwd F m head 0

/-! ## Body agreement -/

/-- One count iteration with a live cursor: chase advance, bump
    (any fuel). -/
theorem listLengthBody_ok (F : Nat) (m : Mem) (π : Layout)
    (head : Option Addr) (k : Nat) (a : Addr)
    (nxt : Option Addr)
    (b : Block) (w : BitVec 32)
    (hfind : memFind m a = some b)
    (hmem : memLoad m a b.tag 1 = .ok w)
    (hdec : addrOfWord w = nxt) :
    memEvalStmtFuel F listLengthBody
      (mkListLengthEnv head k (some a)) m π =
      .ok (((mkListLengthEnv head (k + 1) nxt, m, π)),
        .fellThrough) := by
  have hbody : listLengthBody =
      .seq (.assign "cur" (.pgetNext (.var "cur")))
      (.assign "n" (.uadd (.var "n")
        (.lit (.u64 (BitVec.ofNat 64 1))))) := rfl
  have hcur : memEvalExpr (.var "cur")
      (mkListLengthEnv head k (some a)) m π =
      .ok (.ptrVal (some a)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _
      (mkListLengthEnv_cur head k (some a))
  have hget : memEvalExpr (.pgetNext (.var "cur"))
      (mkListLengthEnv head k (some a)) m π =
      .ok (.ptrVal nxt) := by
    have h := memEvalExpr_pgetNext_hit (.var "cur")
      (mkListLengthEnv head k (some a)) m π a w b
      hcur hfind hmem
    rw [hdec] at h
    exact h
  have huC : envUpdate
      (mkListLengthEnv head k (some a)) "cur" (.ptrVal nxt) =
      some (mkListLengthEnv head k nxt) := by
    simp [mkListLengthEnv, envUpdate]
  have hassignC := memEvalStmtFuel_assign_mem F "cur"
    (.pgetNext (.var "cur"))
    (mkListLengthEnv head k (some a)) m π _ _ hget huC
  have hnA : memEvalExpr (.var "n")
      (mkListLengthEnv head k nxt) m π =
      evalExpr (.var "n") (mkListLengthEnv head k nxt) :=
    memEvalExpr_var _ _ _ _
  have honeA : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkListLengthEnv head k nxt) m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (mkListLengthEnv head k nxt) :=
    memEvalExpr_lit _ _ _ _
  have hbumpA := memEvalExpr_uadd_agree (.var "n")
    (.lit (.u64 (BitVec.ofNat 64 1)))
    (mkListLengthEnv head k nxt) m π hnA honeA
  have hbumpV : evalExpr
      (.uadd (.var "n") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkListLengthEnv head k nxt) =
      .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h := evalExpr_uadd_u64 (.var "n")
      (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _
      (evalExpr_var_hit _ _ _ (mkListLengthEnv_n head k nxt)) rfl
    rwa [ofNat64_add_one] at h
  have huN : envUpdate
      (mkListLengthEnv head k nxt) "n"
      (.u64 (BitVec.ofNat 64 (k + 1))) =
      some (mkListLengthEnv head (k + 1) nxt) := by
    simp [mkListLengthEnv, envUpdate]
  have hassignN := memEvalStmtFuel_assign F "n"
    (.uadd (.var "n") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkListLengthEnv head k nxt) m π _ _ hbumpA hbumpV huN
  rw [hbody]
  exact memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
    hassignC hassignN

/-- One count iteration with a dangling cursor aborts loudly. -/
theorem listLengthBody_miss (F : Nat) (m : Mem) (π : Layout)
    (head : Option Addr) (k : Nat) (a : Addr)
    (hfind : memFind m a = none) :
    memEvalStmtFuel F listLengthBody
      (mkListLengthEnv head k (some a)) m π =
      .error .AssertFail := by
  have hbody : listLengthBody =
      .seq (.assign "cur" (.pgetNext (.var "cur")))
      (.assign "n" (.uadd (.var "n")
        (.lit (.u64 (BitVec.ofNat 64 1))))) := rfl
  have hcur : memEvalExpr (.var "cur")
      (mkListLengthEnv head k (some a)) m π =
      .ok (.ptrVal (some a)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _
      (mkListLengthEnv_cur head k (some a))
  have hpg := memEvalExpr_pgetNext_miss (.var "cur")
    (mkListLengthEnv head k (some a)) m π a hcur hfind
  have hassign := memEvalStmtFuel_assign_err F "cur"
    (.pgetNext (.var "cur"))
    (mkListLengthEnv head k (some a)) m π .AssertFail hpg
  rw [hbody]
  exact memEvalStmtFuel_seq_err F _ _ _ _ _ _ hassign

/-! ## Count contract -/

/-- Loop invariant: chasing a whole segment accumulates exactly
    its length (memory untouched — read-only, so no frame
    reasoning; only the `ListSeg` cons walk plus the link
    roundtrip). Induction on fuel; the length bound rules out
    fuel exhaustion on acyclic input. -/
theorem listLengthOuterFwd_invariant (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (cur : Option Addr) (n : Nat) (vs : List (BitVec 32))
      (m' : Mem) (n' : Nat),
    ListSeg m cur vs →
    vs.length ≤ F →
    listLengthOuterFwd F m cur n = .ok (m', n') →
    m' = m ∧ n' = n + vs.length := by
  induction F with
  | zero =>
    intro m hex cur n vs m' n' hseg hlen hf
    cases cur with
    | none =>
      simp only [listLengthOuterFwd] at hf
      cases hf
      cases hseg with
      | nil => exact ⟨rfl, by simp⟩
    | some a =>
      simp only [listLengthOuterFwd] at hf
      cases hf
  | succ F ih =>
    intro m hex cur n vs m' n' hseg hlen hf
    cases cur with
    | none =>
      simp only [listLengthOuterFwd] at hf
      cases hf
      cases hseg with
      | nil => exact ⟨rfl, by simp⟩
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v', nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem : memLoad m a t' 1 = .ok _ := nodeLoadNext hnode
        simp only [listLengthOuterFwd, hfb, hmem] at hf
        have hdec : addrOfWord (linkWord nxt) = nxt :=
          nodeAt_link_roundtrip hnode hex (by
            intro c' hc'
            cases hnxt : nxt with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact ListSeg_head_alloc t2)
        rw [hdec] at hf
        have hlen' : vs'.length ≤ F := by
          simp only [List.length_cons] at hlen
          omega
        have hIH := ih m hex nxt (n + 1) vs' m' n'
          t2 hlen' hf
        obtain ⟨hm', hn'⟩ := hIH
        refine ⟨hm', ?_⟩
        rw [hn']
        simp only [List.length_cons]
        omega

/-- Top-level count contract: chasing a whole segment returns
    its length (seed the counter at zero). -/
theorem listLengthFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (vs : List (BitVec 32))
    (m' : Mem) (n' : Nat)
    (hseg : ListSeg m head vs)
    (hlen : vs.length ≤ F)
    (hfwd : listLengthFwd F m head = .ok (m', n')) :
    m' = m ∧ n' = vs.length := by
  have h := listLengthOuterFwd_invariant F m hex head 0 vs
    m' n' hseg hlen hfwd
  simpa using h

/-! ## Loop/evaluator agreement -/

/-- Loop/evaluator agreement: `listLengthOuter` at any fuel agrees
    with the count forward (same fuel, same memory ops, same
    order). -/
theorem listLengthOuter_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout) (head : Option Addr) (k : Nat)
      (cur : Option Addr),
    memEvalStmtFuel F listLengthOuter
      (mkListLengthEnv head k cur) m π =
      match listLengthOuterFwd F m cur k with
      | .ok (m', k') =>
        .ok (((mkListLengthEnv head k' none, m', π)), .fellThrough)
      | .error e => .error e := by
  induction F with
  | zero =>
    intro m π head k cur
    cases cur with
    | none =>
      have hcur : memEvalExpr (.var "cur")
          (mkListLengthEnv head k none) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListLengthEnv_cur _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListLengthEnv head k none) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListLengthEnv head k none) m π = .ok (.b false) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcur hnull
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
      have hw : memEvalStmtFuel 0 listLengthOuter
          (mkListLengthEnv head k none) m π =
          .ok ((((mkListLengthEnv head k none), m, π)),
            .fellThrough) :=
        memEvalStmtFuel_while_false _ _ listLengthBody _ _ _ hgF
      rw [hw]
      simp only [listLengthOuterFwd]
    | some a =>
      have hcur : memEvalExpr (.var "cur")
          (mkListLengthEnv head k (some a)) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListLengthEnv_cur _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListLengthEnv head k (some a)) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListLengthEnv head k (some a)) m π =
          .ok (.b true) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
          hcur hnull
        have hbe : ((some a) != none) = true := by simp
        rw [hbe] at hg
        exact hg
      have hw : memEvalStmtFuel 0 listLengthOuter
          (mkListLengthEnv head k (some a)) m π =
          .error .AssertFail := by
        simp only [listLengthOuter, memEvalStmtFuel, memEvalStmtZero,
          memEvalStmtWith, memEvalStmtZeroHandler, hgT]
      rw [hw]
      simp only [listLengthOuterFwd]
  | succ F ih =>
    intro m π head k cur
    cases cur with
    | none =>
      have hcur : memEvalExpr (.var "cur")
          (mkListLengthEnv head k none) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListLengthEnv_cur _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListLengthEnv head k none) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListLengthEnv head k none) m π = .ok (.b false) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none hcur hnull
        have hbe : ((none : Option Addr) != none) = false := by simp
        rw [hbe] at hg
        exact hg
      have hw : memEvalStmtFuel (F + 1) listLengthOuter
          (mkListLengthEnv head k none) m π =
          .ok ((((mkListLengthEnv head k none), m, π)),
            .fellThrough) :=
        memEvalStmtFuel_while_false _ _ listLengthBody _ _ _ hgF
      rw [hw]
      simp only [listLengthOuterFwd]
    | some a =>
      have hcur : memEvalExpr (.var "cur")
          (mkListLengthEnv head k (some a)) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListLengthEnv_cur _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListLengthEnv head k (some a)) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkListLengthEnv head k (some a)) m π =
          .ok (.b true) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
          hcur hnull
        have hbe : ((some a) != none) = true := by simp
        rw [hbe] at hg
        exact hg
      have hw := memEvalStmtFuel_while_true F
        (.une (.var "cur") (.lit .nullptr)) listLengthBody _ _ _ hgT
      simp only [listLengthOuter] at hw ⊢
      rw [hw]
      cases hF : memFind m a with
      | none =>
        have hb := listLengthBody_miss F m π head k a hF
        rw [hb]
        simp only [listLengthOuterFwd, hF]
      | some b =>
        cases hL : memLoad m a b.tag 1 with
        | error werr =>
          have hpg := memEvalExpr_pgetNext_err (.var "cur")
            (mkListLengthEnv head k (some a)) m π a b werr
            hcur hF hL
          have hassign := memEvalStmtFuel_assign_err F "cur"
            (.pgetNext (.var "cur"))
            (mkListLengthEnv head k (some a)) m π werr hpg
          have hbody : listLengthBody =
              .seq (.assign "cur" (.pgetNext (.var "cur")))
              (.assign "n" (.uadd (.var "n")
                (.lit (.u64 (BitVec.ofNat 64 1))))) := rfl
          have hb : memEvalStmtFuel F listLengthBody
              (mkListLengthEnv head k (some a)) m π =
              .error werr := by
            rw [hbody]
            exact memEvalStmtFuel_seq_err F _ _ _ _ _ _ hassign
          rw [hb]
          simp only [listLengthOuterFwd, hF, hL]
        | ok w =>
          have hb := listLengthBody_ok F m π head k a
            (addrOfWord w) b w hF hL rfl
          have hIH := ih m π head (k + 1) (addrOfWord w)
          simp only [listLengthOuter] at hIH
          simp only [hb]
          rw [hIH]
          simp only [listLengthOuterFwd, hF, hL]

/-- Entry Hoare triple (thin sugar): the seeded chase returns
    the segment length — seed, loop (bridge), return, then the
    pure contract. -/
theorem listLengthFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (vs : List (BitVec 32))
    (m' : Mem) (n' : Nat)
    (hseg : ListSeg m head vs)
    (hlen : vs.length ≤ F)
    (hfwd : listLengthFwd F m head = .ok (m', n')) :
    ∃ ρ', memEvalStmtFuel F listLengthFunc.body
      [("head", .ptrVal head)] m π =
      .ok ((ρ', m', π),
        .returned (.u64 (BitVec.ofNat 64 vs.length))) ∧
      m' = m ∧ n' = vs.length := by
  have hseg' := listLengthFwd_correct F m hex head vs m' n'
    hseg hlen hfwd
  simp only [listLengthFwd] at hfwd
  -- Seed: counter zero and cursor lets build the count environment.
  have hseed : memEvalStmtFuel F listLengthSeed
      [("head", .ptrVal head)] m π =
      .ok ((mkListLengthEnv head 0 head, m, π), .fellThrough) := by
    have hsu : listLengthSeed = .seq
        (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.let_ "cur" nodeTy (.var "head")) := rfl
    rw [hsu]
    have eN : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("head", .ptrVal head)] m π =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("head", .ptrVal head)] :=
      memEvalExpr_lit _ _ _ _
    have vN : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("head", .ptrVal head)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hL1 := memEvalStmtFuel_let_pure F "n" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      _ _ _ (.u64 (BitVec.ofNat 64 0))
      (by simp) (by simp) (by simp) (by simp) eN vN
    have eC : memEvalExpr (.var "head")
        [("n", .u64 (BitVec.ofNat 64 0)), ("head", .ptrVal head)]
        m π =
        evalExpr (.var "head")
          [("n", .u64 (BitVec.ofNat 64 0)), ("head", .ptrVal head)] :=
      memEvalExpr_var _ _ _ _
    have vC : evalExpr (.var "head")
        [("n", .u64 (BitVec.ofNat 64 0)), ("head", .ptrVal head)] =
        .ok (.ptrVal head) :=
      evalExpr_var_hit _ _ _ (by simp [envLookup])
    have hL2 := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "head")
      _ _ _ (.ptrVal head) (by simp) (by simp) (by simp) (by simp) eC vC
    have s1 := memEvalStmtFuel_seq_fallthrough F
      (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.let_ "cur" nodeTy (.var "head"))
      _ _ _ _ _ _ hL1
    rw [s1]
    exact hL2
  -- Loop: the bridge fires the forward.
  have hloop := listLengthOuter_agree F m π head 0 head
  rw [hfwd, hseg'.2] at hloop
  -- Return: the counter slot.
  have hretE : memEvalExpr (.var "n")
      (mkListLengthEnv head vs.length none) m' π =
      evalExpr (.var "n") (mkListLengthEnv head vs.length none) :=
    memEvalExpr_var _ _ _ _
  have hretV : evalExpr (.var "n")
      (mkListLengthEnv head vs.length none) =
      .ok (.u64 (BitVec.ofNat 64 vs.length)) :=
    evalExpr_var_hit _ _ _ (mkListLengthEnv_n _ _ _)
  have hret := memEvalStmtFuel_return F (.var "n")
    (mkListLengthEnv head vs.length none) m' π _ hretE hretV
  -- Compose: seed, loop, return.
  have hbody : listLengthFunc.body =
      .seq listLengthSeed
        (.seq listLengthOuter (.return_ (.var "n"))) := rfl
  have heval : memEvalStmtFuel F listLengthFunc.body
      [("head", .ptrVal head)] m π =
      .ok ((mkListLengthEnv head vs.length none, m', π),
        .returned (.u64 (BitVec.ofNat 64 vs.length))) := by
    rw [hbody]
    have c1 := memEvalStmtFuel_seq_fallthrough F listLengthSeed
      (.seq listLengthOuter (.return_ (.var "n")))
      _ _ _ _ _ _ hseed
    rw [c1]
    have c2 := memEvalStmtFuel_seq_fallthrough F listLengthOuter
      (.return_ (.var "n")) _ _ _ _ _ _ hloop
    rw [c2]
    exact hret
  exact ⟨_, heval, hseg'.1, hseg'.2⟩
