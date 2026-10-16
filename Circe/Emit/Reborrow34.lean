/-
Circe.Emit.Reborrow34 — L1b second writer admission: sequential
reborrows with different constants (`alias_reborrow34`: `r += 3`
then `s += 4` through two loans to one address, functionalized
value in / updated value out). Same licenses as F1
(`hasSequentialWriterRanges` + `contentRoots` both-to-`param0`);
different consts so the F1 const-use pins exclude it while the
sequential-writer skeleton fires. Mechanical mirror of
`Circe.Emit.Reborrow` with `1/2` replaced by `3/4`.
-/
import Circe.Emit.Fragment

/-- Mangled name of the reborrow34 entry. -/
def reborrow34Name : String :=
  "_Z16alias_reborrow34Ri"

/-- Canonical CoreIR for `tests/cpp/alias_reborrow34.cpp`
    (`void alias_reborrow34(int &x) { int &r = x; r += 1; int &s = x;
    s += 2; }`, functionalized: value in, updated value out). -/
def reborrow34Func : Func :=
  ⟨reborrow34Name, [{ name := "x", ty := .i 32, role := .mutBorrow 0 }],
   .i 32,
   .seq (.let_ "t" (.i 32) (.add (.var "x") (.lit (.i32 3))))
        (.return_ (.add (.var "t") (.lit (.i32 4))))⟩

/-! ## Verified forward function (Value level) -/

/-- Body check for the `matchFrag` arm, two-level so the giant
    `matchFrag` match stays shallow (a deep nested arm times out the
    equation compiler): the let-bound `x + 3` and the returned `t + 4`
    with the exact names and increments. -/
def isReborrow34Body : CExpr → CStmt → Bool
  | .add (.var x) (.lit (.i32 one)),
    .return_ (.add (.var t) (.lit (.i32 two))) =>
    x == "x" && t == "t" && one == 3 && two == 4
  | _, _ => false

/-- Verified forward function for `reborrow34` (cf. rendered
    `reborrow_fwd`): sequential checked adds, fail-fast. -/
def reborrow34Fwd (x : BitVec 32) : Result Value :=
  match checkedAddI32 x 3 with
  | .error e => .error e
  | .ok t => .i32 <$> checkedAddI32 t 4

/-- Bridge: forward ok-path threads both adds. -/
theorem reborrow34Fwd_ok (x t r : BitVec 32)
    (h1 : checkedAddI32 x 3 = .ok t) (h2 : checkedAddI32 t 4 = .ok r) :
    reborrow34Fwd x = .ok (.i32 r) := by
  -- NOTE (BitVec literal discipline): hypotheses mentioning checked-add
  -- literals must rewrite with `rw` (tolerant `kabstract`), never as
  -- `simp` arguments — separately elaborated `1 : BitVec 32` terms do
  -- not match syntactically (`1` vs `1#32`), so `simp [.., h1]` leaves
  -- `h1` unused and the goal unsolved.
  simp only [reborrow34Fwd]
  rw [h1]
  dsimp only
  rw [h2]
  exact i32_map_ok r

/-- Bridge: first-add failure propagates (and determines the error). -/
theorem reborrow34Fwd_err1 (x : BitVec 32) (e : Panic)
    (h : checkedAddI32 x 3 = .error e) :
    reborrow34Fwd x = .error e := by
  simp only [reborrow34Fwd]
  rw [h]

/-- Bridge: second-add failure propagates. -/
theorem reborrow34Fwd_err2 (x t : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 x 3 = .ok t) (h2 : checkedAddI32 t 4 = .error e) :
    reborrow34Fwd x = .error e := by
  simp only [reborrow34Fwd]
  rw [h1]
  dsimp only
  rw [h2]
  exact i32_map_error e

/-! ## `emit_correct` for the fragment -/

/-- Env fact for the `reborrow34` shape. -/
theorem envLookup_reborrow34_x (x : BitVec 32) :
    envLookup [("x", .i32 x)] "x" = some (.i32 x) := by
  simp [envLookup]

/-- `emit_correct` for `reborrow34` at any fuel (loop-free body): the
    `let_` makes both adds single (flat) steps, sequenced like
    `addCaller`/`add3`. -/
theorem evalFuncFuel_reborrow34 (F : Nat) (x : BitVec 32) :
    evalFuncFuel F reborrow34Func [.i32 x] = reborrow34Fwd x := by
  have hbind : bindArgs reborrow34Func.args [.i32 x] =
      some [("x", .i32 x)] := rfl
  have hbody : reborrow34Func.body =
      .seq (.let_ "t" (.i 32) (.add (.var "x") (.lit (.i32 3))))
           (.return_ (.add (.var "t") (.lit (.i32 4)))) := rfl
  have hx := envLookup_reborrow34_x x
  simp only [evalFuncFuel, hbind, hbody]
  cases h1 : checkedAddI32 x 3 with
  | error e =>
    have hexpr : evalExpr (.add (.var "x") (.lit (.i32 3)))
        ([("x", .i32 x)] : Env) = .error e := by
      rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
      exact i32_map_error e
    have hlet := evalStmtFuel_let_err F "t" (.i 32) _ _ e hexpr
    rw [evalStmtFuel_seq_err _ _ _ _ _ hlet]
    exact (reborrow34Fwd_err1 x e h1).symm
  | ok t =>
    have hexpr : evalExpr (.add (.var "x") (.lit (.i32 3)))
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
    cases h2 : checkedAddI32 t 4 with
    | error e =>
      have hexpr2 : evalExpr (.add (.var "t") (.lit (.i32 4)))
          (envExtend [("x", .i32 x)] "t" (.i32 t)) = .error e := by
        rw [evalExpr_add_var_lit _ _ _ _ ht, h2]
        exact i32_map_error e
      have hret := evalStmtFuel_return_err F _ _ e hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet, hret]
      exact (reborrow34Fwd_err2 x t e h1 h2).symm
    | ok r =>
      have hexpr2 : evalExpr (.add (.var "t") (.lit (.i32 4)))
          (envExtend [("x", .i32 x)] "t" (.i32 t)) = .ok (.i32 r) := by
        rw [evalExpr_add_var_lit _ _ _ _ ht, h2]
        exact i32_map_ok r
      have hret := evalStmtFuel_return F _ _ (.i32 r) hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet, hret]
      exact (reborrow34Fwd_ok x t r h1 h2).symm

/-- Emitter correctness, `reborrow34` (all inputs, ok and error paths). -/
theorem emit_correct_reborrow34 (x : BitVec 32) :
    evalFunc reborrow34Func [.i32 x] = reborrow34Fwd x :=
  evalFuncFuel_reborrow34 EVAL_FUEL x

/-- Corollary: `reborrow34` errors are preserved exactly. -/
theorem emit_correct_reborrow34_err (x : BitVec 32) (e : Panic)
    (h : reborrow34Fwd x = .error e) :
    evalFunc reborrow34Func [.i32 x] = .error e := by
  rw [emit_correct_reborrow34, h]

/-- Corollary: `reborrow34` successes deliver the twice-incremented
    value. -/
theorem emit_correct_reborrow34_ok (x r : BitVec 32)
    (h : reborrow34Fwd x = .ok (.i32 r)) :
    evalFunc reborrow34Func [.i32 x] = .ok (.i32 r) := by
  rw [emit_correct_reborrow34, h]
