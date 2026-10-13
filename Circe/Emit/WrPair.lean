/-
Circe.Emit.WrPair — G2 writer-pair admission: two disjoint writers
(`wr_pair`: `*p += 1` and `*q += 2` through two `__restrict__`
params, functionalized to the updated pair, the `incr` precedent
doubled with the G1 `pair` carrier).

The disjointness license is gate-side: `isWrPairShape` (the in-order
dataflow pin — each add feeds its in-order store into its in-order
param cell from that same cell) plus the explicit `noalias` verdict.
Disjoint writes commute, so no L2 sequencing license is needed
(unlike F1). Checked-add order is unobservable (uniform
`.Overflow`), but the gate pins the corpus order exactly.
-/
import Circe.Emit.Fragment

/-- Canonical CoreIR for `tests/c/wr_pair.c`
    (`void wr_pair(int32_t *__restrict p, int32_t *__restrict q)`:
    value in, updated pair out). -/
def wrPairFunc : Func :=
  ⟨"wr_pair",
   [{ name := "p", ty := .i 32, role := .mutBorrow 0 },
    { name := "q", ty := .i 32, role := .mutBorrow 0 }],
   .struct "IPair" [.i 32, .i 32],
   .seq (.let_ "a" (.i 32) (.add (.var "p") (.lit (.i32 1))))
   (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
         (.return_ (.pair (.var "a") (.var "b"))))⟩

/-! ## Verified forward function (Value level) -/

/-- Body check for the `matchFrag` arm, two-level so the giant
    `matchFrag` match stays shallow (F1 precedent: a deep nested arm
    times out the equation compiler): the first let-bound `p + 1`
    plus the rest (second let `q + 2` and the `pair` return) with the
    exact names and increments. -/
def isWrPairBody : CExpr → CStmt → Bool
  | .add (.var p) (.lit (.i32 one)),
    .seq (.let_ "b" _ (.add (.var q) (.lit (.i32 two))))
         (.return_ (.pair (.var a) (.var b))) =>
    p == "p" && q == "q" && a == "a" && b == "b" &&
      one == 1 && two == 2
  | _, _ => false

/-- Verified forward function for `wr_pair` (cf. rendered
    `wr_pair_fwd`): two independent checked adds, fail-fast
    first-add-first. -/
def wrPairFwd (p q : BitVec 32) : Result Value :=
  match checkedAddI32 p 1, checkedAddI32 q 2 with
  | .ok a, .ok b => .ok (.structVal "IPair" [("a", a), ("b", b)])
  | .error e, _ => .error e
  | _, .error e => .error e

/-- Bridge: forward ok-path delivers the updated pair. -/
theorem wrPairFwd_ok (p q a b : BitVec 32)
    (h1 : checkedAddI32 p 1 = .ok a) (h2 : checkedAddI32 q 2 = .ok b) :
    wrPairFwd p q = .ok (.structVal "IPair" [("a", a), ("b", b)]) := by
  -- NOTE (BitVec literal discipline, F1 precedent): hypotheses
  -- mentioning checked-add literals rewrite with `rw`, never as
  -- `simp` arguments — separately elaborated `1 : BitVec 32` terms
  -- do not match syntactically (`1` vs `1#32`). The pair match
  -- reduces definitionally once both discriminants rewrite.
  simp only [wrPairFwd]
  rw [h1, h2]

/-- Bridge: first-add failure propagates (and determines the error). -/
theorem wrPairFwd_err1 (p q : BitVec 32) (e : Panic)
    (h : checkedAddI32 p 1 = .error e) :
    wrPairFwd p q = .error e := by
  simp only [wrPairFwd]
  rw [h]

/-- Bridge: second-add failure propagates. -/
theorem wrPairFwd_err2 (p q a : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 p 1 = .ok a) (h2 : checkedAddI32 q 2 = .error e) :
    wrPairFwd p q = .error e := by
  simp only [wrPairFwd]
  rw [h1, h2]

/-! ## `emit_correct` for the fragment -/

/-- `emit_correct` for `wr_pair` at any fuel (loop-free body): both
    lets make their adds single (flat) steps, sequenced like
    `addCaller`/`reborrow`, with the `pair` return assembling the
    outputs. -/
theorem evalFuncFuel_wrPair (F : Nat) (p q : BitVec 32) :
    evalFuncFuel F wrPairFunc [.i32 p, .i32 q] = wrPairFwd p q := by
  have hbind : bindArgs wrPairFunc.args [.i32 p, .i32 q] =
      some [("p", .i32 p), ("q", .i32 q)] := rfl
  have hbody : wrPairFunc.body =
      .seq (.let_ "a" (.i 32) (.add (.var "p") (.lit (.i32 1))))
      (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
            (.return_ (.pair (.var "a") (.var "b")))) := rfl
  have hp : envLookup [("p", .i32 p), ("q", .i32 q)] "p" =
      some (.i32 p) := by
    simp [envLookup]
  simp only [evalFuncFuel, hbind, hbody]
  cases h1 : checkedAddI32 p 1 with
  | error e =>
    have hexpr : evalExpr (.add (.var "p") (.lit (.i32 1)))
        ([("p", .i32 p), ("q", .i32 q)] : Env) = .error e := by
      rw [evalExpr_add_var_lit _ _ _ _ hp, h1]
      exact i32_map_error e
    have hlet := evalStmtFuel_let_err F "a" (.i 32) _ _ e hexpr
    rw [evalStmtFuel_seq_err _ _ _ _ _ hlet]
    exact (wrPairFwd_err1 p q e h1).symm
  | ok a =>
    have hexpr : evalExpr (.add (.var "p") (.lit (.i32 1)))
        ([("p", .i32 p), ("q", .i32 q)] : Env) = .ok (.i32 a) := by
      rw [evalExpr_add_var_lit _ _ _ _ hp, h1]
      exact i32_map_ok a
    have hlet := evalStmtFuel_let_ F "a" (.i 32) _ _ (.i32 a) hexpr
    have hq : envLookup
        (envExtend [("p", .i32 p), ("q", .i32 q)] "a" (.i32 a)) "q" =
        some (.i32 q) := by
      simp [envExtend, envLookup, show ("q" : String) ≠ "a" by decide]
    cases h2 : checkedAddI32 q 2 with
    | error e =>
      have hexpr2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
          (envExtend [("p", .i32 p), ("q", .i32 q)] "a" (.i32 a)) =
          .error e := by
        rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
        exact i32_map_error e
      have hlet2 := evalStmtFuel_let_err F "b" (.i 32) _ _ e hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet,
        evalStmtFuel_seq_err _ _ _ _ _ hlet2]
      exact (wrPairFwd_err2 p q a e h1 h2).symm
    | ok b =>
      have hexpr2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
          (envExtend [("p", .i32 p), ("q", .i32 q)] "a" (.i32 a)) =
          .ok (.i32 b) := by
        rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
        exact i32_map_ok b
      have hlet2 := evalStmtFuel_let_ F "b" (.i 32) _ _ (.i32 b) hexpr2
      have ha : envLookup
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q)]
            "a" (.i32 a)) "b" (.i32 b)) "a" = some (.i32 a) := by
        simp [envExtend, envLookup, show ("a" : String) ≠ "b" by decide]
      have hb : envLookup
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q)]
            "a" (.i32 a)) "b" (.i32 b)) "b" = some (.i32 b) :=
        envExtend_hit _ _ _
      have hava : evalExpr (.var "a")
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q)]
            "a" (.i32 a)) "b" (.i32 b)) = .ok (.i32 a) :=
        evalExpr_var_hit _ _ _ ha
      have havb : evalExpr (.var "b")
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q)]
            "a" (.i32 a)) "b" (.i32 b)) = .ok (.i32 b) :=
        evalExpr_var_hit _ _ _ hb
      have hexprP : evalExpr (.pair (.var "a") (.var "b"))
          (envExtend (envExtend [("p", .i32 p), ("q", .i32 q)]
            "a" (.i32 a)) "b" (.i32 b)) =
          .ok (.structVal "IPair" [("a", a), ("b", b)]) :=
        evalExpr_pair_ok _ _ _ _ _ hava havb
      have hret := evalStmtFuel_return F _ _
        (.structVal "IPair" [("a", a), ("b", b)]) hexprP
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet2, hret]
      exact (wrPairFwd_ok p q a b h1 h2).symm

/-- Emitter correctness, `wr_pair` (all inputs, ok and error paths). -/
theorem emit_correct_wrPair (p q : BitVec 32) :
    evalFunc wrPairFunc [.i32 p, .i32 q] = wrPairFwd p q :=
  evalFuncFuel_wrPair EVAL_FUEL p q

/-- Corollary: `wr_pair` errors are preserved exactly. -/
theorem emit_correct_wrPair_err (p q : BitVec 32) (e : Panic)
    (h : wrPairFwd p q = .error e) :
    evalFunc wrPairFunc [.i32 p, .i32 q] = .error e := by
  rw [emit_correct_wrPair, h]

/-- Corollary: `wr_pair` successes deliver the updated pair. -/
theorem emit_correct_wrPair_ok (p q a b : BitVec 32)
    (h : wrPairFwd p q = .ok (.structVal "IPair" [("a", a), ("b", b)])) :
    evalFunc wrPairFunc [.i32 p, .i32 q] =
      .ok (.structVal "IPair" [("a", a), ("b", b)]) := by
  rw [emit_correct_wrPair, h]
