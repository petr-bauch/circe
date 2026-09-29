/-
Circe.Emit.Choose — borrow-return `choose`: forward + backward functions,
`emit_correct`, the `cir_choose` tactic (lives here next to the definitions
its simp set names), and lens laws.
-/
import Circe.Emit.Fragment

/-! ## `choose`: borrow-return (forward + backward) -/

/-- Canonical CoreIR for `tests/c/choose_ptr.c`
    (`int32_t *choose(bool b, int32_t *__restrict x, int32_t *__restrict y)`).
    Single-region (both borrows share region 0, per `docs/SUBSET.md` rule 6);
    the returned borrow is functionalized to the selected *value*, and writes
    through it are propagated by `chooseBack` (Aeneas §4.3). -/
def chooseFunc : Func :=
  ⟨"choose",
   [{ name := "b", ty := .bool, role := .owned },
    { name := "x", ty := .i 32, role := .mutBorrow 0 },
    { name := "y", ty := .i 32, role := .mutBorrow 0 }],
   .i 32,
   .if_ (.var "b") (.return_ (.var "x")) (.return_ (.var "y"))⟩

/-- Verified forward function for `choose` (cf. rendered `choose_fwd`):
    pure selection, never fails. -/
def chooseFwd (b : Bool) (x y : BitVec 32) : Result Value :=
  .ok (.i32 (if b then x else y))

/-- Verified backward function for `choose` (cf. rendered `choose_back`):
    the updated return value flows back to the selected input; the other
    input is unchanged. -/
def chooseBack (b : Bool) (x y ret : BitVec 32) : Result (Value × Value) :=
  .ok (if b then (.i32 ret, .i32 y) else (.i32 x, .i32 ret))

/-- Env facts for the `choose` shape. -/
theorem envLookup_choose_b (b : Bool) (x y : BitVec 32) :
    envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "b" =
      some (.b b) := by
  simp [envLookup]

theorem envLookup_choose_x (b : Bool) (x y : BitVec 32) :
    envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "x" =
      some (.i32 x) := by
  simp [envLookup, show ("x" : String) ≠ "b" by decide]

theorem envLookup_choose_y (b : Bool) (x y : BitVec 32) :
    envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "y" =
      some (.i32 y) := by
  simp [envLookup, show ("y" : String) ≠ "b" by decide,
    show ("y" : String) ≠ "x" by decide]

/-- Emitter correctness, `choose`: evaluating the CoreIR function agrees with
    the forward function on all inputs. -/
theorem emit_correct_choose (b : Bool) (x y : BitVec 32) :
    evalFunc chooseFunc [.b b, .i32 x, .i32 y] = chooseFwd b x y := by
  have hb := envLookup_choose_b b x y
  have hx := envLookup_choose_x b x y
  have hy := envLookup_choose_y b x y
  cases b <;>
    simp [evalFunc, evalFuncFuel, chooseFunc, bindArgs, evalStmtFuel,
      evalStmtWith, EVAL_FUEL, evalExpr, chooseFwd, hb, hx, hy]

/-- Forward/backward `choose` reasoning (S5; documented in
    `Circe.Tactics`): split on the selector and simplify with the
    verified forward/backward equations. Closes get-put / put-get
    shaped goals. Lives here (not `Tactics`: the simp set names
    `chooseFwd` / `chooseBack`, so they must be in scope where the
    macro is defined). -/
macro "cir_choose" b:Lean.Parser.Tactic.elimTarget : tactic =>
  `(tactic| (cases $b <;> simp [chooseFwd, chooseBack]))

/-- Lens law (get-put): propagating the selected value back unchanged is the
    identity on the inputs. -/
theorem choose_back_get_put (b : Bool) (x y : BitVec 32) :
    chooseBack b x y (if b then x else y) = .ok (.i32 x, .i32 y) := by
  cir_choose b

/-- Lens law (put-get): selecting after a backward update yields the update. -/
theorem choose_back_put_get (b : Bool) (x y r : BitVec 32) :
    (match chooseBack b x y r with
    | .ok (.i32 x', .i32 y') => chooseFwd b x' y'
    | _ => .error .AssertFail) = .ok (.i32 r) := by
  cir_choose b
