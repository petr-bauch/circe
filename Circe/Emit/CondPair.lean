/-
Circe.Emit.CondPair — G2b branch-writer admission: one conditional
writer plus one unconditional writer (`cond_pair`: `*p += 1` under
`c`, `*q += 2` always, through two `__restrict__` params,
functionalized to the updated pair with the G1 `pair` carrier).

The disjointness license is gate-side: `isCondPairShape` (the G2
in-order dataflow pin plus branch placement — first run inside the
`cir.if` region into `arg0`'s cell, second outside into `arg1`'s)
plus the explicit `noalias` verdict. The `tif` is lazy on both
sides, so `c = false` masks the first add (and its overflow).
-/
import Circe.Emit.Fragment

/-- Canonical CoreIR for `tests/c/cond_pair.c`
    (`void cond_pair(int32_t *__restrict p, int32_t *__restrict q,
    bool c)`: values in, updated pair out). -/
def condPairFunc : Func :=
  ⟨"cond_pair",
   [{ name := "p", ty := .i 32, role := .mutBorrow 0 },
    { name := "q", ty := .i 32, role := .mutBorrow 0 },
    { name := "c", ty := .bool, role := .owned }],
   .struct "IPair" [.i 32, .i 32],
   .seq (.let_ "a" (.i 32)
     (.tif (.var "c") (.add (.var "p") (.lit (.i32 1))) (.var "p")))
   (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
         (.return_ (.pair (.var "a") (.var "b"))))⟩

/-! ## Verified forward function (Value level) -/

/-- Body check for the `matchFrag` arm, two-level so the giant
    `matchFrag` match stays shallow (F1 precedent): the first
    let-bound `c ? p + 1 : p` plus the rest (second let `q + 2`
    and the `pair` return) with the exact names and increments. -/
def isCondPairBody : CExpr → CStmt → Bool
  | .tif (.var c) (.add (.var p) (.lit (.i32 one))) (.var p'),
    .seq (.let_ "b" _ (.add (.var q) (.lit (.i32 two))))
         (.return_ (.pair (.var a) (.var b))) =>
    c == "c" && p == "p" && p' == "p" && q == "q" && a == "a" &&
      b == "b" && one == 1 && two == 2
  | _, _ => false

/-- Verified forward function for `cond_pair` (cf. rendered
    `cond_pair_fwd`): evaluation order matches the body (branch
    first, then the unconditional add); the first add fires only
    under `c` (masking its overflow when `c = false`). The branch
    matches on `c` rather than `if` so every arm reduces
    definitionally once the discriminants rewrite (an `if`'s
    `Decidable` instance gets stuck under `rw`'s closer). -/
def condPairFwd (p q : BitVec 32) (c : Bool) : Result Value :=
  match c with
  | true =>
    match checkedAddI32 p 1 with
    | .error e => .error e
    | .ok a =>
      match checkedAddI32 q 2 with
      | .error e => .error e
      | .ok b => .ok (.structVal "IPair" [("a", a), ("b", b)])
  | false =>
    match checkedAddI32 q 2 with
    | .error e => .error e
    | .ok b => .ok (.structVal "IPair" [("a", p), ("b", b)])

/-- Bridge: both adds succeed under `c`. -/
theorem condPairFwd_ok_true (p q a b : BitVec 32)
    (h1 : checkedAddI32 p 1 = .ok a) (h2 : checkedAddI32 q 2 = .ok b) :
    condPairFwd p q true =
      .ok (.structVal "IPair" [("a", a), ("b", b)]) := by
  -- NOTE (BitVec literal discipline, F1 precedent): `rw`, never
  -- `simp` arguments, for checked-add hypotheses.
  simp only [condPairFwd]
  rw [h2, h1]

/-- Bridge: `c = false` masks the first add (no `h1` needed — the
    untaken branch is never evaluated). -/
theorem condPairFwd_ok_false (p q b : BitVec 32)
    (h2 : checkedAddI32 q 2 = .ok b) :
    condPairFwd p q false =
      .ok (.structVal "IPair" [("a", p), ("b", b)]) := by
  simp only [condPairFwd]
  rw [h2]

/-- Bridge: second-add failure propagates under `c` (first add
    already succeeded). -/
theorem condPairFwd_err_q_true (p q a : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 p 1 = .ok a)
    (h2 : checkedAddI32 q 2 = .error e) :
    condPairFwd p q true = .error e := by
  simp only [condPairFwd]
  rw [h1, h2]

/-- Bridge: second-add failure propagates with `c = false`. -/
theorem condPairFwd_err_q_false (p q : BitVec 32) (e : Panic)
    (h : checkedAddI32 q 2 = .error e) :
    condPairFwd p q false = .error e := by
  simp only [condPairFwd]
  rw [h]

/-- Bridge: first-add failure propagates under `c` (short-circuits
    exactly like the body — no `h2` needed). -/
theorem condPairFwd_err_p (p q : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 p 1 = .error e) :
    condPairFwd p q true = .error e := by
  simp only [condPairFwd]
  rw [h1]

/-! ## `emit_correct` for the fragment -/

/-- `emit_correct` for `cond_pair` at any fuel (loop-free body):
    the `tif` makes the first add branch-lazy on both sides, then
    the second let and the `pair` return run as in G2. -/
theorem evalFuncFuel_condPair (F : Nat) (p q : BitVec 32) (c : Bool) :
    evalFuncFuel F condPairFunc [.i32 p, .i32 q, .b c] =
      condPairFwd p q c := by
  have hbind : bindArgs condPairFunc.args [.i32 p, .i32 q, .b c] =
      some [("p", .i32 p), ("q", .i32 q), ("c", .b c)] := rfl
  have hbody : condPairFunc.body =
      .seq (.let_ "a" (.i 32)
        (.tif (.var "c") (.add (.var "p") (.lit (.i32 1))) (.var "p")))
      (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
            (.return_ (.pair (.var "a") (.var "b")))) := rfl
  have hp : envLookup [("p", .i32 p), ("q", .i32 q), ("c", .b c)]
      "p" = some (.i32 p) := by
    simp [envLookup]
  have hc0 : envLookup [("p", .i32 p), ("q", .i32 q), ("c", .b c)]
      "c" = some (.b c) := by
    simp [envLookup]
  simp only [evalFuncFuel, hbind, hbody]
  cases c with
  | true =>
    have hcT : evalExpr (.var "c")
        ([("p", .i32 p), ("q", .i32 q), ("c", .b true)] : Env) =
        .ok (.b true) :=
      evalExpr_var_hit _ _ _ hc0
    cases h1 : checkedAddI32 p 1 with
    | error e =>
      have ht1 : evalExpr (.add (.var "p") (.lit (.i32 1)))
          ([("p", .i32 p), ("q", .i32 q), ("c", .b true)] : Env) =
          .error e := by
        rw [evalExpr_add_var_lit _ _ _ _ hp, h1]
        exact i32_map_error e
      have hexpr : evalExpr
          (.tif (.var "c") (.add (.var "p") (.lit (.i32 1)))
            (.var "p"))
          ([("p", .i32 p), ("q", .i32 q), ("c", .b true)] : Env) =
          .error e := by
        rw [evalExpr_tif_true _ _ _ _ hcT, ht1]
      have hlet := evalStmtFuel_let_err F "a" (.i 32) _ _ e hexpr
      rw [evalStmtFuel_seq_err _ _ _ _ _ hlet]
      exact (condPairFwd_err_p p q e h1).symm
    | ok a =>
      have ht1 : evalExpr (.add (.var "p") (.lit (.i32 1)))
          ([("p", .i32 p), ("q", .i32 q), ("c", .b true)] : Env) =
          .ok (.i32 a) := by
        rw [evalExpr_add_var_lit _ _ _ _ hp, h1]
        exact i32_map_ok a
      have hexpr : evalExpr
          (.tif (.var "c") (.add (.var "p") (.lit (.i32 1)))
            (.var "p"))
          ([("p", .i32 p), ("q", .i32 q), ("c", .b true)] : Env) =
          .ok (.i32 a) := by
        rw [evalExpr_tif_true _ _ _ _ hcT, ht1]
      have hlet := evalStmtFuel_let_ F "a" (.i 32) _ _ (.i32 a) hexpr
      have hq : envLookup
          (envExtend [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
            "a" (.i32 a)) "q" = some (.i32 q) := by
        simp [envExtend, envLookup, show ("q" : String) ≠ "a" by decide]
      cases h2 : checkedAddI32 q 2 with
      | error e =>
        have hexpr2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
            (envExtend [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
              "a" (.i32 a)) = .error e := by
          rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
          exact i32_map_error e
        have hlet2 := evalStmtFuel_let_err F "b" (.i 32) _ _ e hexpr2
        rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet,
          evalStmtFuel_seq_err _ _ _ _ _ hlet2]
        exact (condPairFwd_err_q_true p q a e h1 h2).symm
      | ok b =>
        have hexpr2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
            (envExtend [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
              "a" (.i32 a)) = .ok (.i32 b) := by
          rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
          exact i32_map_ok b
        have hlet2 := evalStmtFuel_let_ F "b" (.i 32) _ _ (.i32 b) hexpr2
        have ha : envLookup
            (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] "a" (.i32 a)) "b" (.i32 b)) "a" =
            some (.i32 a) := by
          simp [envExtend, envLookup, show ("a" : String) ≠ "b" by decide]
        have hb : envLookup
            (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] "a" (.i32 a)) "b" (.i32 b)) "b" =
            some (.i32 b) :=
          envExtend_hit _ _ _
        have hava : evalExpr (.var "a")
            (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] "a" (.i32 a)) "b" (.i32 b)) =
            .ok (.i32 a) :=
          evalExpr_var_hit _ _ _ ha
        have havb : evalExpr (.var "b")
            (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] "a" (.i32 a)) "b" (.i32 b)) =
            .ok (.i32 b) :=
          evalExpr_var_hit _ _ _ hb
        have hexprP : evalExpr (.pair (.var "a") (.var "b"))
            (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] "a" (.i32 a)) "b" (.i32 b)) =
            .ok (.structVal "IPair" [("a", a), ("b", b)]) :=
          evalExpr_pair_ok _ _ _ _ _ hava havb
        have hret := evalStmtFuel_return F _ _
          (.structVal "IPair" [("a", a), ("b", b)]) hexprP
        rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet,
          evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet2, hret]
        exact (condPairFwd_ok_true p q a b h1 h2).symm
  | false =>
    -- The untaken branch is never evaluated: no `h1` split here.
    have hcF : evalExpr (.var "c")
        ([("p", .i32 p), ("q", .i32 q), ("c", .b false)] : Env) =
        .ok (.b false) :=
      evalExpr_var_hit _ _ _ hc0
    have hpE : evalExpr (.var "p")
        ([("p", .i32 p), ("q", .i32 q), ("c", .b false)] : Env) =
        .ok (.i32 p) :=
      evalExpr_var_hit _ _ _ hp
    have hexpr : evalExpr
        (.tif (.var "c") (.add (.var "p") (.lit (.i32 1)))
          (.var "p"))
        ([("p", .i32 p), ("q", .i32 q), ("c", .b false)] : Env) =
        .ok (.i32 p) := by
      rw [evalExpr_tif_false _ _ _ _ hcF, hpE]
    have hlet := evalStmtFuel_let_ F "a" (.i 32) _ _ (.i32 p) hexpr
    have hq : envLookup
        (envExtend [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
          "a" (.i32 p)) "q" = some (.i32 q) := by
      simp [envExtend, envLookup, show ("q" : String) ≠ "a" by decide]
    cases h2 : checkedAddI32 q 2 with
    | error e =>
      have hexpr2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
          (envExtend [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
            "a" (.i32 p)) = .error e := by
        rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
        exact i32_map_error e
      have hlet2 := evalStmtFuel_let_err F "b" (.i 32) _ _ e hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet,
        evalStmtFuel_seq_err _ _ _ _ _ hlet2]
      exact (condPairFwd_err_q_false p q e h2).symm
    | ok b =>
      have hexpr2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
          (envExtend [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
            "a" (.i32 p)) = .ok (.i32 b) := by
        rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
        exact i32_map_ok b
      have hlet2 := evalStmtFuel_let_ F "b" (.i 32) _ _ (.i32 b) hexpr2
      have ha : envLookup
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] "a" (.i32 p)) "b" (.i32 b)) "a" =
          some (.i32 p) := by
        simp [envExtend, envLookup, show ("a" : String) ≠ "b" by decide]
      have hb : envLookup
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] "a" (.i32 p)) "b" (.i32 b)) "b" =
          some (.i32 b) :=
        envExtend_hit _ _ _
      have hava : evalExpr (.var "a")
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] "a" (.i32 p)) "b" (.i32 b)) =
          .ok (.i32 p) :=
        evalExpr_var_hit _ _ _ ha
      have havb : evalExpr (.var "b")
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] "a" (.i32 p)) "b" (.i32 b)) =
          .ok (.i32 b) :=
        evalExpr_var_hit _ _ _ hb
      have hexprP : evalExpr (.pair (.var "a") (.var "b"))
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] "a" (.i32 p)) "b" (.i32 b)) =
          .ok (.structVal "IPair" [("a", p), ("b", b)]) :=
        evalExpr_pair_ok _ _ _ _ _ hava havb
      have hret := evalStmtFuel_return F _ _
        (.structVal "IPair" [("a", p), ("b", b)]) hexprP
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet2, hret]
      exact (condPairFwd_ok_false p q b h2).symm

/-- Emitter correctness, `cond_pair` (all inputs, ok and error paths). -/
theorem emit_correct_condPair (p q : BitVec 32) (c : Bool) :
    evalFunc condPairFunc [.i32 p, .i32 q, .b c] = condPairFwd p q c :=
  evalFuncFuel_condPair EVAL_FUEL p q c
