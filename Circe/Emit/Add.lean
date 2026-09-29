/-
Circe.Emit.Add — loop-free integer leaves: `add`/`incr` (32-bit) and
`add64`/`addu64` (S3b 64-bit), with forwards and `emit_correct` proofs.
-/
import Circe.Emit.Fragment

/-- Canonical CoreIR for `tests/c/add.c`
    (`int32_t add(int32_t a, int32_t b) { return a + b; }`). -/
def addFunc : Func :=
  ⟨"add", [{ name := "a", ty := .i 32, role := .owned },
           { name := "b", ty := .i 32, role := .owned }],
   .i 32, .return_ (.add (.var "a") (.var "b"))⟩

/-- Canonical CoreIR for `tests/c/incr_ptr.c`
    (`void incr(int32_t *__restrict p) { *p = *p + 1; }`, functionalized:
    value in, updated value out). -/
def incrFunc : Func :=
  ⟨"incr", [{ name := "p", ty := .i 32, role := .mutBorrow 0 }],
   .i 32, .return_ (.add (.var "p") (.lit (.i32 1)))⟩



/-! ## Verified forward functions (Value level) -/

/-- Verified forward function for `add` (cf. rendered `add_fwd`). -/
def addFwd (a b : BitVec 32) : Result Value := .i32 <$> checkedAddI32 a b

/-- Verified forward function for `incr` (cf. rendered `incr_fwd`). -/
def incrFwd (p : BitVec 32) : Result Value := .i32 <$> checkedIncrI32 p



/-! ## `emit_correct` for the fragment -/

/-- Env facts for the `add` shape (closed name (dis)equalities). -/
theorem envLookup_add_a (a b : BitVec 32) :
    envLookup [("a", .i32 a), ("b", .i32 b)] "a" = some (.i32 a) := by
  simp [envLookup]

theorem envLookup_add_b (a b : BitVec 32) :
    envLookup [("a", .i32 a), ("b", .i32 b)] "b" = some (.i32 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

/-- Env fact for the `incr` shape. -/
theorem envLookup_incr_p (p : BitVec 32) :
    envLookup [("p", .i32 p)] "p" = some (.i32 p) := by
  simp [envLookup]

/-- Emitter correctness, `add`: evaluating the CoreIR function agrees with
    the forward function on all inputs (ok and error paths). -/
theorem emit_correct_add (a b : BitVec 32) :
    evalFunc addFunc [.i32 a, .i32 b] = addFwd a b := by
  have ha := envLookup_add_a a b
  have hb := envLookup_add_b a b
  simp only [evalFunc, evalFuncFuel, addFunc, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, addFwd, ha, hb]
  cases checkedAddI32 a b <;> rfl

/-- Emitter correctness, `incr`. -/
theorem emit_correct_incr (p : BitVec 32) :
    evalFunc incrFunc [.i32 p] = incrFwd p := by
  have hp := envLookup_incr_p p
  simp only [evalFunc, evalFuncFuel, incrFunc, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, litVal, incrFwd, checkedIncrI32, hp]
  cases checkedAddI32 p 1 <;> rfl

/-- Corollary: `add` errors are preserved exactly. -/
theorem emit_correct_add_err (a b : BitVec 32) (e : Panic)
    (h : checkedAddI32 a b = .error e) :
    evalFunc addFunc [.i32 a, .i32 b] = .error e := by
  rw [emit_correct_add]
  unfold addFwd
  rw [h]
  exact i32_map_error e

/-- Corollary: `add` successes deliver the wrapped sum as a value. -/
theorem emit_correct_add_ok (a b r : BitVec 32)
    (h : checkedAddI32 a b = .ok r) :
    evalFunc addFunc [.i32 a, .i32 b] = .ok (.i32 r) := by
  rw [emit_correct_add]
  unfold addFwd
  rw [h]
  exact i32_map_ok r

/-- Corollary: `incr` errors are preserved exactly. -/
theorem emit_correct_incr_err (p : BitVec 32) (e : Panic)
    (h : checkedIncrI32 p = .error e) :
    evalFunc incrFunc [.i32 p] = .error e := by
  rw [emit_correct_incr]
  unfold incrFwd
  rw [h]
  exact i32_map_error e

/-- Corollary: `incr` successes deliver the incremented value. -/
theorem emit_correct_incr_ok (p r : BitVec 32)
    (h : checkedIncrI32 p = .ok r) :
    evalFunc incrFunc [.i32 p] = .ok (.i32 r) := by
  rw [emit_correct_incr]
  unfold incrFwd
  rw [h]
  exact i32_map_ok r

/-- `emit_correct` for `add` at any fuel (loop-free body, so every fuel
    agrees; loop proofs and program steps generalize the fuel). -/
theorem evalFuncFuel_add (F : Nat) (a b : BitVec 32) :
    evalFuncFuel F addFunc [.i32 a, .i32 b] = addFwd a b := by
  have ha := envLookup_add_a a b
  have hb := envLookup_add_b a b
  cases F <;>
    simp only [evalFuncFuel, addFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, addFwd, ha, hb] <;>
    (cases checkedAddI32 a b <;> rfl)

/-! ## S3b: 64-bit loop-free widths (`add64`, `addu64`) -/

/-- Canonical CoreIR for `tests/c/add64.c`
    (`int64_t add64(int64_t a, int64_t b) { return a + b; }`):
    same shape as `add`, at width 64. -/
def add64Func : Func :=
  ⟨"add64", [{ name := "a", ty := .i 64, role := .owned },
             { name := "b", ty := .i 64, role := .owned }],
   .i 64, .return_ (.add (.var "a") (.var "b"))⟩

/-- Canonical CoreIR for `tests/c/addu64.c`
    (`uint64_t addu64(uint64_t a, uint64_t b) { return a + b; }`):
    wrapping unsigned addition at width 64. -/
def addu64Func : Func :=
  ⟨"addu64", [{ name := "a", ty := .u 64, role := .owned },
              { name := "b", ty := .u 64, role := .owned }],
   .u 64, .return_ (.uadd (.var "a") (.var "b"))⟩

/-- Verified forward function for `add64` (cf. rendered `add64_fwd`). -/
def add64Fwd (a b : BitVec 64) : Result Value := .i64 <$> checkedAddI64 a b

/-- Verified forward function for `addu64` (cf. rendered `addu64_fwd`):
    wrapping, never fails. -/
def addu64Fwd (a b : BitVec 64) : Result Value := .ok (.u64 (a + b))



/-- Env facts for the 64-bit add shapes. -/
theorem envLookup_add64_a (a b : BitVec 64) :
    envLookup [("a", .i64 a), ("b", .i64 b)] "a" = some (.i64 a) := by
  simp [envLookup]

theorem envLookup_add64_b (a b : BitVec 64) :
    envLookup [("a", .i64 a), ("b", .i64 b)] "b" = some (.i64 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

theorem envLookup_addu64_a (a b : BitVec 64) :
    envLookup [("a", .u64 a), ("b", .u64 b)] "a" = some (.u64 a) := by
  simp [envLookup]

theorem envLookup_addu64_b (a b : BitVec 64) :
    envLookup [("a", .u64 a), ("b", .u64 b)] "b" = some (.u64 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

/-- Emitter correctness, `add64` (all inputs, ok and error paths). -/
theorem emit_correct_add64 (a b : BitVec 64) :
    evalFunc add64Func [.i64 a, .i64 b] = add64Fwd a b := by
  have ha := envLookup_add64_a a b
  have hb := envLookup_add64_b a b
  simp only [evalFunc, evalFuncFuel, add64Func, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, add64Fwd, ha, hb]
  cases checkedAddI64 a b <;> rfl

/-- Emitter correctness, `addu64` (wrapping: always succeeds). -/
theorem emit_correct_addu64 (a b : BitVec 64) :
    evalFunc addu64Func [.u64 a, .u64 b] = addu64Fwd a b := by
  have ha := envLookup_addu64_a a b
  have hb := envLookup_addu64_b a b
  simp [evalFunc, evalFuncFuel, addu64Func, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, addu64Fwd, ha, hb]

/-- Corollary: `add64` errors are preserved exactly. -/
theorem emit_correct_add64_err (a b : BitVec 64) (e : Panic)
    (h : checkedAddI64 a b = .error e) :
    evalFunc add64Func [.i64 a, .i64 b] = .error e := by
  rw [emit_correct_add64]
  unfold add64Fwd
  rw [h]
  exact i64_map_error e

/-- Corollary: `add64` successes deliver the wrap sum as a value. -/
theorem emit_correct_add64_ok (a b r : BitVec 64)
    (h : checkedAddI64 a b = .ok r) :
    evalFunc add64Func [.i64 a, .i64 b] = .ok (.i64 r) := by
  rw [emit_correct_add64]
  unfold add64Fwd
  rw [h]
  exact i64_map_ok r
