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

/-- `emit_correct` for `add` under a renamed (e.g. mangled) leaf:
    evaluation never inspects the function name, so overload and
    namespace leaves share the body proof (N4a caller programs evaluate
    over `[{addFunc with name := nm}]`). -/
theorem evalFuncFuel_addAt (F : Nat) (nm : String) (a b : BitVec 32) :
    evalFuncFuel F { addFunc with name := nm } [.i32 a, .i32 b] =
      addFwd a b := by
  have ha := envLookup_add_a a b
  have hb := envLookup_add_b a b
  cases F <;>
    simp only [evalFuncFuel, addFunc, bindArgs, evalStmtFuel,
      evalStmtZero, evalStmtWith, evalExpr, addFwd, ha, hb] <;>
    (cases checkedAddI32 a b <;> rfl)

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

/-- `emit_correct` for `add64` under a renamed (e.g. mangled
    instantiation) leaf: evaluation never inspects the function name,
    so the 64-bit instantiation shares the body proof (N4c caller
    programs evaluate over `[{add64Func with name := nm}]`). -/
theorem evalFuncFuel_add64At (F : Nat) (nm : String) (a b : BitVec 64) :
    evalFuncFuel F { add64Func with name := nm } [.i64 a, .i64 b] =
      add64Fwd a b := by
  have ha := envLookup_add64_a a b
  have hb := envLookup_add64_b a b
  cases F <;>
    simp only [evalFuncFuel, add64Func, bindArgs, evalStmtFuel,
      evalStmtZero, evalStmtWith, evalExpr, add64Fwd, ha, hb] <;>
    (cases checkedAddI64 a b <;> rfl)

/-! ## N4a: arity-3 `add` overload leaf (`_Z3addiii`) -/

/-- Canonical CoreIR for the 3-`i32` overload leaf in
    `tests/cpp/overload_add.cpp`
    (`int32_t add(int32_t a, int32_t b, int32_t c)`): the `add` idiom
    with one more threaded operand, the SSA temporary as an explicit
    `let_` (so both `emit_correct` proofs stay flat, like `addCaller`). -/
def add3Func : Func :=
  ⟨"_Z3addiii", [{ name := "a", ty := .i 32, role := .owned },
           { name := "b", ty := .i 32, role := .owned },
           { name := "c", ty := .i 32, role := .owned }],
   .i 32,
   .seq (.let_ "t" (.i 32) (.add (.var "a") (.var "b")))
        (.return_ (.add (.var "t") (.var "c")))⟩

/-- Verified forward function for `add3` (cf. rendered `_Z3addiii_fwd`):
    sequential `Result` binds over the leaf op. -/
def add3Fwd (x y z : BitVec 32) : Result Value :=
  match checkedAddI32 x y with
  | .error e => .error e
  | .ok t => .i32 <$> checkedAddI32 t z

/-- Bridge: forward ok-path threads both adds. -/
theorem add3Fwd_ok (x y z t r : BitVec 32)
    (h1 : checkedAddI32 x y = .ok t) (h2 : checkedAddI32 t z = .ok r) :
    add3Fwd x y z = .ok (.i32 r) := by
  simp [add3Fwd, h1, h2, i32_map_ok]

/-- Bridge: first-add failure propagates (and determines the error). -/
theorem add3Fwd_err (x y z : BitVec 32) (e : Panic)
    (h : checkedAddI32 x y = .error e) :
    add3Fwd x y z = .error e := by
  simp [add3Fwd, h]

/-- Env facts for the `add3` shape. -/
theorem envLookup_add3_a (x y z : BitVec 32) :
    envLookup [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "a" =
      some (.i32 x) := by
  simp [envLookup]

theorem envLookup_add3_b (x y z : BitVec 32) :
    envLookup [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "b" =
      some (.i32 y) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

theorem envLookup_add3_c (x y z : BitVec 32) :
    envLookup [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "c" =
      some (.i32 z) := by
  simp [envLookup, show ("c" : String) ≠ "a" by decide,
    show ("c" : String) ≠ "b" by decide]

/-- `emit_correct` for `add3` at any fuel (loop-free body): the `let_`
    makes both adds single (flat) steps, sequenced like `addCaller`. -/
theorem evalFuncFuel_add3 (F : Nat) (x y z : BitVec 32) :
    evalFuncFuel F add3Func [.i32 x, .i32 y, .i32 z] = add3Fwd x y z := by
  have hbind : bindArgs add3Func.args [.i32 x, .i32 y, .i32 z] =
      some [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] := rfl
  have hbody : add3Func.body =
      .seq (.let_ "t" (.i 32) (.add (.var "a") (.var "b")))
           (.return_ (.add (.var "t") (.var "c"))) := rfl
  have ha := envLookup_add3_a x y z
  have hb := envLookup_add3_b x y z
  have hc := envLookup_add3_c x y z
  simp only [evalFuncFuel, hbind, hbody]
  cases h1 : checkedAddI32 x y with
  | error e =>
    have hexpr : evalExpr (.add (.var "a") (.var "b"))
        ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env) = .error e := by
      simp [evalExpr, ha, hb, h1, Except.map]
    have hlet := evalStmtFuel_let_err F "t" (.i 32) _ _ e hexpr
    rw [evalStmtFuel_seq_err _ _ _ _ _ hlet]
    simp [add3Fwd, h1]
  | ok t =>
    have hexpr : evalExpr (.add (.var "a") (.var "b"))
        ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env) =
        .ok (.i32 t) := by
      simp [evalExpr, ha, hb, h1, Except.map]
    have hlet := evalStmtFuel_let_ F "t" (.i 32) _ _ (.i32 t) hexpr
    have ht : envLookup (envExtend [("a", .i32 x), ("b", .i32 y),
        ("c", .i32 z)] "t" (.i32 t)) "t" = some (.i32 t) :=
      envExtend_hit _ _ _
    have hc2 : envLookup (envExtend [("a", .i32 x), ("b", .i32 y),
        ("c", .i32 z)] "t" (.i32 t)) "c" = some (.i32 z) := by
      simp [envExtend, envLookup, show ("c" : String) ≠ "t" by decide]
    cases h2 : checkedAddI32 t z with
    | error e =>
      have hexpr2 : evalExpr (.add (.var "t") (.var "c"))
          (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t"
            (.i32 t)) = .error e := by
        simp [evalExpr, ht, hc2, h2, Except.map]
      have hret := evalStmtFuel_return_err F _ _ e hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet, hret]
      simp [add3Fwd, h1, h2, i32_map_error]
    | ok r =>
      have hexpr2 : evalExpr (.add (.var "t") (.var "c"))
          (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t"
            (.i32 t)) = .ok (.i32 r) := by
        simp [evalExpr, ht, hc2, h2, Except.map]
      have hret := evalStmtFuel_return F _ _ (.i32 r) hexpr2
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hlet, hret]
      simp [add3Fwd, h1, h2, i32_map_ok]

/-- Emitter correctness, `add3` (all inputs, ok and error paths). -/
theorem emit_correct_add3 (x y z : BitVec 32) :
    evalFunc add3Func [.i32 x, .i32 y, .i32 z] = add3Fwd x y z :=
  evalFuncFuel_add3 EVAL_FUEL x y z

/-! ## N6a: signed-32 negation + division leaves (`neg`, `sdiv`) -/

/-- Canonical CoreIR for `tests/c/neg.c`
    (`int32_t neg(int32_t x) { return -x; }`): `cir.minus nsw`. -/
def negFunc : Func :=
  ⟨"neg", [{ name := "x", ty := .i 32, role := .owned }],
   .i 32, .return_ (.neg (.var "x"))⟩

/-- Canonical CoreIR for `tests/c/sdiv.c`
    (`int32_t sdiv(int32_t a, int32_t b) { return a / b; }`): `cir.div`
    on `!s32i` (signedness from the type, no flag). -/
def sdivFunc : Func :=
  ⟨"sdiv", [{ name := "a", ty := .i 32, role := .owned },
            { name := "b", ty := .i 32, role := .owned }],
   .i 32, .return_ (.sdiv (.var "a") (.var "b"))⟩

/-- Verified forward function for `neg` (cf. rendered `neg_fwd`). -/
def negFwd (x : BitVec 32) : Result Value := .i32 <$> checkedNegI32 x

/-- Verified forward function for `sdiv` (cf. rendered `sdiv_fwd`). -/
def sdivFwd (a b : BitVec 32) : Result Value := .i32 <$> checkedDivI32 a b

/-- Env fact for the `neg` shape. -/
theorem envLookup_neg_x (x : BitVec 32) :
    envLookup [("x", .i32 x)] "x" = some (.i32 x) := by
  simp [envLookup]

/-- Env facts for the `sdiv` shape. -/
theorem envLookup_sdiv_a (a b : BitVec 32) :
    envLookup [("a", .i32 a), ("b", .i32 b)] "a" = some (.i32 a) := by
  simp [envLookup]

theorem envLookup_sdiv_b (a b : BitVec 32) :
    envLookup [("a", .i32 a), ("b", .i32 b)] "b" = some (.i32 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

/-- Emitter correctness, `neg` (all inputs, ok and error paths). -/
theorem emit_correct_neg (x : BitVec 32) :
    evalFunc negFunc [.i32 x] = negFwd x := by
  have hx := envLookup_neg_x x
  simp only [evalFunc, evalFuncFuel, negFunc, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, negFwd, hx]
  cases checkedNegI32 x <;> rfl

/-- Emitter correctness, `sdiv` (all inputs, ok and error paths). -/
theorem emit_correct_sdiv (a b : BitVec 32) :
    evalFunc sdivFunc [.i32 a, .i32 b] = sdivFwd a b := by
  have ha := envLookup_sdiv_a a b
  have hb := envLookup_sdiv_b a b
  simp only [evalFunc, evalFuncFuel, sdivFunc, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, sdivFwd, ha, hb]
  cases checkedDivI32 a b <;> rfl

/-- Corollary: `neg` errors are preserved exactly. -/
theorem emit_correct_neg_err (x : BitVec 32) (e : Panic)
    (h : checkedNegI32 x = .error e) :
    evalFunc negFunc [.i32 x] = .error e := by
  rw [emit_correct_neg]
  unfold negFwd
  rw [h]
  exact i32_map_error e

/-- Corollary: `neg` successes deliver the negated word as a value. -/
theorem emit_correct_neg_ok (x r : BitVec 32)
    (h : checkedNegI32 x = .ok r) :
    evalFunc negFunc [.i32 x] = .ok (.i32 r) := by
  rw [emit_correct_neg]
  unfold negFwd
  rw [h]
  exact i32_map_ok r

/-- Corollary: `sdiv` errors are preserved exactly. -/
theorem emit_correct_sdiv_err (a b : BitVec 32) (e : Panic)
    (h : checkedDivI32 a b = .error e) :
    evalFunc sdivFunc [.i32 a, .i32 b] = .error e := by
  rw [emit_correct_sdiv]
  unfold sdivFwd
  rw [h]
  exact i32_map_error e

/-- Corollary: `sdiv` successes deliver the quotient word as a value. -/
theorem emit_correct_sdiv_ok (a b r : BitVec 32)
    (h : checkedDivI32 a b = .ok r) :
    evalFunc sdivFunc [.i32 a, .i32 b] = .ok (.i32 r) := by
  rw [emit_correct_sdiv]
  unfold sdivFwd
  rw [h]
  exact i32_map_ok r
