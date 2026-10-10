/-
Circe.Emit.Bitwise — loop-free `u32` bitwise leaves for K1 (the crypto
op mix): `xor` / `and` / `or` (total — no UB in C) and `shl` / `shr`
(`cir.shift(left/right, …)`, `OOB` on amounts ≥ 32, the N6 shift-UB
discipline), with forwards and `emit_correct` proofs.
-/
import Circe.Emit.Fragment

/-- Canonical CoreIR for `tests/c/xor_u32.c`: `cir.xor` on `!u32i`. -/
def xorU32Func : Func :=
  ⟨"xor_u32", [{ name := "a", ty := .u 32, role := .owned },
               { name := "b", ty := .u 32, role := .owned }],
   .u 32, .return_ (.bxor (.var "a") (.var "b"))⟩

/-- Canonical CoreIR for `tests/c/and_u32.c`: `cir.and` on `!u32i`. -/
def andU32Func : Func :=
  ⟨"and_u32", [{ name := "a", ty := .u 32, role := .owned },
               { name := "b", ty := .u 32, role := .owned }],
   .u 32, .return_ (.band (.var "a") (.var "b"))⟩

/-- Canonical CoreIR for `tests/c/or_u32.c`: `cir.or` on `!u32i`. -/
def orU32Func : Func :=
  ⟨"or_u32", [{ name := "a", ty := .u 32, role := .owned },
              { name := "b", ty := .u 32, role := .owned }],
   .u 32, .return_ (.bor (.var "a") (.var "b"))⟩

/-- Canonical CoreIR for `tests/c/shl_u32.c`:
    `cir.shift(left, …)` on `!u32i`. -/
def shlU32Func : Func :=
  ⟨"shl_u32", [{ name := "a", ty := .u 32, role := .owned },
               { name := "b", ty := .u 32, role := .owned }],
   .u 32, .return_ (.bshl (.var "a") (.var "b"))⟩

/-- Canonical CoreIR for `tests/c/shr_u32.c`:
    `cir.shift(right, …)` on `!u32i`. -/
def shrU32Func : Func :=
  ⟨"shr_u32", [{ name := "a", ty := .u 32, role := .owned },
               { name := "b", ty := .u 32, role := .owned }],
   .u 32, .return_ (.bshr (.var "a") (.var "b"))⟩

/-- Verified forward for `xor_u32` (total). -/
def xorU32Fwd (a b : BitVec 32) : Result Value := .ok (.u32 (a ^^^ b))

/-- Verified forward for `and_u32` (total). -/
def andU32Fwd (a b : BitVec 32) : Result Value := .ok (.u32 (a &&& b))

/-- Verified forward for `or_u32` (total). -/
def orU32Fwd (a b : BitVec 32) : Result Value := .ok (.u32 (a ||| b))

/-- Verified forward for `shl_u32` (`OOB` on amounts ≥ 32). -/
def shlU32Fwd (a b : BitVec 32) : Result Value :=
  .u32 <$> checkedShiftU32 a b (· <<< ·)

/-- Verified forward for `shr_u32` (`OOB` on amounts ≥ 32). -/
def shrU32Fwd (a b : BitVec 32) : Result Value :=
  .u32 <$> checkedShiftU32 a b (· >>> ·)

/-- Env facts for the binary `u32` leaf shape. -/
theorem envLookup_bitwiseU32_a (a b : BitVec 32) :
    envLookup [("a", .u32 a), ("b", .u32 b)] "a" = some (.u32 a) := by
  simp [envLookup]

theorem envLookup_bitwiseU32_b (a b : BitVec 32) :
    envLookup [("a", .u32 a), ("b", .u32 b)] "b" = some (.u32 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

/-- Emitter correctness, `xor_u32` (total: all inputs agree). -/
theorem emit_correct_xorU32 (a b : BitVec 32) :
    evalFunc xorU32Func [.u32 a, .u32 b] = xorU32Fwd a b := by
  have ha := envLookup_bitwiseU32_a a b
  have hb := envLookup_bitwiseU32_b a b
  simp only [evalFunc, evalFuncFuel, xorU32Func, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, xorU32Fwd, ha, hb]

/-- Emitter correctness, `and_u32` (total). -/
theorem emit_correct_andU32 (a b : BitVec 32) :
    evalFunc andU32Func [.u32 a, .u32 b] = andU32Fwd a b := by
  have ha := envLookup_bitwiseU32_a a b
  have hb := envLookup_bitwiseU32_b a b
  simp only [evalFunc, evalFuncFuel, andU32Func, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, andU32Fwd, ha, hb]

/-- Emitter correctness, `or_u32` (total). -/
theorem emit_correct_orU32 (a b : BitVec 32) :
    evalFunc orU32Func [.u32 a, .u32 b] = orU32Fwd a b := by
  have ha := envLookup_bitwiseU32_a a b
  have hb := envLookup_bitwiseU32_b a b
  simp only [evalFunc, evalFuncFuel, orU32Func, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, orU32Fwd, ha, hb]

/-- Emitter correctness, `shl_u32` (ok and `OOB` paths). -/
theorem emit_correct_shlU32 (a b : BitVec 32) :
    evalFunc shlU32Func [.u32 a, .u32 b] = shlU32Fwd a b := by
  have ha := envLookup_bitwiseU32_a a b
  have hb := envLookup_bitwiseU32_b a b
  simp only [evalFunc, evalFuncFuel, shlU32Func, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, shlU32Fwd, ha, hb]
  cases checkedShiftU32 a b (· <<< ·) <;> rfl

/-- Emitter correctness, `shr_u32` (ok and `OOB` paths). -/
theorem emit_correct_shrU32 (a b : BitVec 32) :
    evalFunc shrU32Func [.u32 a, .u32 b] = shrU32Fwd a b := by
  have ha := envLookup_bitwiseU32_a a b
  have hb := envLookup_bitwiseU32_b a b
  simp only [evalFunc, evalFuncFuel, shrU32Func, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, shrU32Fwd, ha, hb]
  cases checkedShiftU32 a b (· >>> ·) <;> rfl

/-- Corollary: `shl_u32` errors are preserved exactly. -/
theorem emit_correct_shlU32_err (a b : BitVec 32) (e : Panic)
    (h : checkedShiftU32 a b (· <<< ·) = .error e) :
    evalFunc shlU32Func [.u32 a, .u32 b] = .error e := by
  rw [emit_correct_shlU32]
  unfold shlU32Fwd
  rw [h]
  exact u32_map_error e

/-- Corollary: `shl_u32` successes deliver the shifted word. -/
theorem emit_correct_shlU32_ok (a b r : BitVec 32)
    (h : checkedShiftU32 a b (· <<< ·) = .ok r) :
    evalFunc shlU32Func [.u32 a, .u32 b] = .ok (.u32 r) := by
  rw [emit_correct_shlU32]
  unfold shlU32Fwd
  rw [h]
  exact u32_map_ok r

/-- Corollary: `shr_u32` errors are preserved exactly. -/
theorem emit_correct_shrU32_err (a b : BitVec 32) (e : Panic)
    (h : checkedShiftU32 a b (· >>> ·) = .error e) :
    evalFunc shrU32Func [.u32 a, .u32 b] = .error e := by
  rw [emit_correct_shrU32]
  unfold shrU32Fwd
  rw [h]
  exact u32_map_error e

/-- Corollary: `shr_u32` successes deliver the shifted word. -/
theorem emit_correct_shrU32_ok (a b r : BitVec 32)
    (h : checkedShiftU32 a b (· >>> ·) = .ok r) :
    evalFunc shrU32Func [.u32 a, .u32 b] = .ok (.u32 r) := by
  rw [emit_correct_shrU32]
  unfold shrU32Fwd
  rw [h]
  exact u32_map_ok r
