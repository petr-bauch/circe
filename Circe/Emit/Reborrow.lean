/-
Circe.Emit.Reborrow — F1 first writer admission: sequential reborrows
(`alias_reborrow`: `r += 1` then `s += 2` through two loans to one
address, functionalized value in / updated value out, the `incr`
precedent with two sequenced checked adds).

The fusion is licensed gate-side: `hasSequentialWriterRanges` (L2:
the first writer ends before the second begins) plus `contentRoots`
(F0: both writers resolve to `param0`) mean the text computes
`x + 1 + 2` through one cell — the fused body below. Checked-add
order is unobservable (uniform `.Overflow`), but the gate pins the
corpus order exactly.
-/
import Circe.Emit.Fragment

/-- Mangled name of the reborrow entry. -/
def reborrowName : String :=
  "_Z14alias_reborrowRi"

/-- Canonical CoreIR for `tests/cpp/alias_reborrow.cpp`
    (`void alias_reborrow(int &x) { int &r = x; r += 1; int &s = x;
    s += 2; }`, functionalized: value in, updated value out). -/
def reborrowFunc : Func :=
  ⟨reborrowName, [{ name := "x", ty := .i 32, role := .mutBorrow 0 }],
   .i 32,
   .seq (.let_ "t" (.i 32) (.add (.var "x") (.lit (.i32 1))))
        (.return_ (.add (.var "t") (.lit (.i32 2))))⟩

/-! ## Verified forward function (Value level) -/

/-- Body check for the `matchFrag` arm, two-level so the giant
    `matchFrag` match stays shallow (a deep nested arm times out the
    equation compiler): the let-bound `x + 1` and the returned `t + 2`
    with the exact names and increments. -/
def isReborrowBody : CExpr → CStmt → Bool
  | .add (.var x) (.lit (.i32 one)),
    .return_ (.add (.var t) (.lit (.i32 two))) =>
    x == "x" && t == "t" && one == 1 && two == 2
  | _, _ => false

/-- Verified forward function for `reborrow` (cf. rendered
    `reborrow_fwd`): sequential checked adds, fail-fast. -/
def reborrowFwd (x : BitVec 32) : Result Value :=
  match checkedAddI32 x 1 with
  | .error e => .error e
  | .ok t => .i32 <$> checkedAddI32 t 2

/-- Bridge: forward ok-path threads both adds. -/
theorem reborrowFwd_ok (x t r : BitVec 32)
    (h1 : checkedAddI32 x 1 = .ok t) (h2 : checkedAddI32 t 2 = .ok r) :
    reborrowFwd x = .ok (.i32 r) := by
  -- NOTE (BitVec literal discipline): hypotheses mentioning checked-add
  -- literals must rewrite with `rw` (tolerant `kabstract`), never as
  -- `simp` arguments — separately elaborated `1 : BitVec 32` terms do
  -- not match syntactically (`1` vs `1#32`), so `simp [.., h1]` leaves
  -- `h1` unused and the goal unsolved.
  simp only [reborrowFwd]
  rw [h1]
  dsimp only
  rw [h2]
  exact i32_map_ok r

/-- Bridge: first-add failure propagates (and determines the error). -/
theorem reborrowFwd_err1 (x : BitVec 32) (e : Panic)
    (h : checkedAddI32 x 1 = .error e) :
    reborrowFwd x = .error e := by
  simp only [reborrowFwd]
  rw [h]

/-- Bridge: second-add failure propagates. -/
theorem reborrowFwd_err2 (x t : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 x 1 = .ok t) (h2 : checkedAddI32 t 2 = .error e) :
    reborrowFwd x = .error e := by
  simp only [reborrowFwd]
  rw [h1]
  dsimp only
  rw [h2]
  exact i32_map_error e

/-! ## `emit_correct` for the fragment -/

/-- Env fact for the `reborrow` shape. -/
theorem envLookup_reborrow_x (x : BitVec 32) :
    envLookup [("x", .i32 x)] "x" = some (.i32 x) := by
  simp [envLookup]

/-- `emit_correct` for `reborrow` at any fuel (loop-free body): the
    `let_` makes both adds single (flat) steps, sequenced like
    `addCaller`/`add3`. -/
theorem evalFuncFuel_reborrow (F : Nat) (x : BitVec 32) :
    evalFuncFuel F reborrowFunc [.i32 x] = reborrowFwd x := by
  have hbind : bindArgs reborrowFunc.args [.i32 x] =
      some [("x", .i32 x)] := rfl
  have hbody : reborrowFunc.body =
      .seq (.let_ "t" (.i 32) (.add (.var "x") (.lit (.i32 1))))
           (.return_ (.add (.var "t") (.lit (.i32 2)))) := rfl
  have hx := envLookup_reborrow_x x
  simp only [evalFuncFuel, hbind, hbody]
  cases h1 : checkedAddI32 x 1 with
  | error e =>
    have hexpr : evalExpr (.add (.var "x") (.lit (.i32 1)))
        ([("x", .i32 x)] : Env) = .error e := by
      rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
      exact i32_map_error e
    have hlet := evalStmtFuel_let_err F "t" (.i 32) _ _ e hexpr
    rw [evalStmtFuel_seq_err _ _ _ _ _ hlet]
    exact (reborrowFwd_err1 x e h1).symm
  | ok t =>
    have hexpr : evalExpr (.add (.var "x") (.lit (.i32 1)))
        ([("x", .i32 x)] : Env) = .ok (.i32 t) := by
      rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
      exact i32_map_ok t
    have hlet := evalStmtFuel_let_ F "t" (.i 32) _ _ (.i32 t) hexpr
    have ht : envLookup (envExtend [("x", .i32 x)] "t" (.i32 t)) "t" =
        some (.i32 t) :=
      envExtend_hit _ _ _
    have hx2 : envLookup (envExtend [("x", .i32 x)] "t" (.i32 t)) "x" =
        some (.i32 x) := by
      simp [envExtend, envLookup, show ("x" : String) ≠ "t" by decide]
    cases h2 : checkedAddI32 t 2 with
    | error e =>
      have hexpr2 : evalExpr (.add (.var "t") (.lit (.i32 2)))
          (envExtend [("x", .i32 x)] "t" (.i32 t)) = .error e := by
        rw [evalExpr_add_var_lit _ _ _ _ ht, h2]
        exact i32_map_error e
      have hret := evalStmtFuel_return_err F _ _ e hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet, hret]
      exact (reborrowFwd_err2 x t e h1 h2).symm
    | ok r =>
      have hexpr2 : evalExpr (.add (.var "t") (.lit (.i32 2)))
          (envExtend [("x", .i32 x)] "t" (.i32 t)) = .ok (.i32 r) := by
        rw [evalExpr_add_var_lit _ _ _ _ ht, h2]
        exact i32_map_ok r
      have hret := evalStmtFuel_return F _ _ (.i32 r) hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet, hret]
      exact (reborrowFwd_ok x t r h1 h2).symm

/-- Emitter correctness, `reborrow` (all inputs, ok and error paths). -/
theorem emit_correct_reborrow (x : BitVec 32) :
    evalFunc reborrowFunc [.i32 x] = reborrowFwd x :=
  evalFuncFuel_reborrow EVAL_FUEL x

/-- Corollary: `reborrow` errors are preserved exactly. -/
theorem emit_correct_reborrow_err (x : BitVec 32) (e : Panic)
    (h : reborrowFwd x = .error e) :
    evalFunc reborrowFunc [.i32 x] = .error e := by
  rw [emit_correct_reborrow, h]

/-- Corollary: `reborrow` successes deliver the twice-incremented
    value. -/
theorem emit_correct_reborrow_ok (x r : BitVec 32)
    (h : reborrowFwd x = .ok (.i32 r)) :
    evalFunc reborrowFunc [.i32 x] = .ok (.i32 r) := by
  rw [emit_correct_reborrow, h]
