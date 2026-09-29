/-
Circe.Emit — verified emitter `CoreIR → Lean` (forward + backward defs).

Emitter for the admitted fragment (`add`/`incr`, borrow-return `choose`,
bounded-loop `sum`, uniquely-owned heap `vec`, S1 DAG calls, S2
struct-by-value, S3a control flow).
- `matchFrag` recognizes the admitted `Func` shapes (by-value `add`;
  single-`mutBorrow` `incr`; single-region borrow-return `choose`;
  bounded-loop `sum`; heap `vec`; S1 callers; S2 `translate`; S3a
  `nested`/`skip`/`findEq`/`cls`; S3b 64-bit `add64`/`addu64`). See the
  `matchFrag` contract note: everything semantically relevant is pinned.
- `addFwd`/`incrFwd`/`chooseFwd`(+`chooseBack`)`/`sumFwd` are the verified
  forward (and backward) functions (Value level); `emit_correct_*` prove
  they agree with `evalFunc` on the canonical `*Func`s, with
  error-preservation corollaries and `choose` lens laws.
- `emitFunc` renders an accepted `Func` to `EmittedFunc` file text
  (`out/*.lean` via `tools/GenOut.lean`); anything else is rejected with
  `EmitError.notFragment` (loudly — never silently modeled).
- `emitSpec` renders the S4 spec stub (`out/*_Spec.lean`: signature +
  body reference + edge list + prop-test entry), dispatched on
  `matchFrag` exactly like `emitFunc`.

Trust note: the *rendering* (Value-tag erasure to `BitVec` text) is
trusted, like the parser; what is verified is that the rendered
definitions have exactly the semantics of `evalFunc` on the fragment.
`tools/check.sh` regenerates the outputs and `diff`s them against
the checked-in goldens (`tests/golden/*.lean`, also spot-checked by the
`native_decide` examples below on clean builds), and `lake env lean`
typechecks the rendered files.
-/
import Circe.Base
import Circe.CoreIR
import Circe.Eval

/-! ## Fragment shapes -/

/-- The admitted fragment: `add`/`incr`/`choose`/`sum`/`vec`, extended in
    S1 with DAG calls (`addCall` = double-`add`, `sumCall` = `sum_array`
    delegation), in S2 with struct-by-value (`translate` = field-wise
    `Point` translation), in S3a with control flow (`nested` =
    nested bounded loops, `skip` = break/continue loop, `findEq` =
    early-return search, `cls` = switch-as-if-chain), and in S3b with
    64-bit loop-free widths (`add64` = signed-`nsw` `i64` add,
    `addu64` = wrapping `u64` add). -/
inductive FragKind : Type
  | add
  | add64
  | addu64
  | incr
  | choose
  | sum
  | vec
  | vec2
  | addCall
  | sumCall
  | translate
  | nested
  | skip
  | findEq
  | cls
  deriving DecidableEq, Repr


/-! ### Small-number word lemmas (loop indices live below 2^32) -/

theorem ofNat32_zero : BitVec.ofNat 32 0 = 0 := rfl

theorem ofNat32_toNat (k : Nat) (h : k < 2 ^ 32) :
    (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- Incrementing a small word stays in `ofNat` form (no wrap).
    Stated with `ofNat 32 1` (not `1`): simp normalizes `1` to `1#32`. -/
theorem ofNat32_add_one (k : Nat) :
    BitVec.ofNat 32 k + BitVec.ofNat 32 1 = BitVec.ofNat 32 (k + 1) :=
  (BitVec.ofNat_add (n := 32) k 1).symm

/-- Unsigned comparison of a small word against any word. -/
theorem ofNat32_ult (k : Nat) (n : BitVec 32) (h : k < 2 ^ 32) :
    (BitVec.ofNat 32 k).ult n = decide (k < n.toNat) := by
  rw [BitVec.ult_eq_decide, ofNat32_toNat k h]

/-- Recognize the admitted `Func` shapes. Anything else is `none`
    (and `emitFunc` rejects it loudly).

    Contract: everything semantically relevant is pinned (param names,
    types relevant to evaluation, borrow-region equality for `choose`,
    exact bodies including the `1`/`0` literals). Ignored fields (function
    name, return type, `let_` annotations, static array bounds, borrow
    region numbers up to single-region equality) are semantically inert:
    `Eval` never inspects them. The pipeline only feeds validator-produced
    canonical `Func`s; per-shape generalized `emit_correct` proofs are
    future work. -/
def matchFrag : Func → Option FragKind
  | ⟨_, [⟨"a", .i 32, .owned⟩, ⟨"b", .i 32, .owned⟩], _,
      .return_ (.add (.var "a") (.var "b"))⟩ => some .add
  | ⟨_, [⟨"a", .i 64, .owned⟩, ⟨"b", .i 64, .owned⟩], _,
      .return_ (.add (.var "a") (.var "b"))⟩ => some .add64
  | ⟨_, [⟨"a", .u 64, .owned⟩, ⟨"b", .u 64, .owned⟩], _,
      .return_ (.uadd (.var "a") (.var "b"))⟩ => some .addu64
  | ⟨_, [⟨"p", .i 32, .mutBorrow _⟩], _,
      .return_ (.add (.var "p") (.lit (.i32 one)))⟩ =>
    if one == 1 then some .incr else none
  | ⟨_, [⟨"b", .bool, .owned⟩, ⟨"x", .i 32, .mutBorrow r1⟩,
         ⟨"y", .i 32, .mutBorrow r2⟩], _,
      .if_ (.var "b") (.return_ (.var "x")) (.return_ (.var "y"))⟩ =>
    if r1 == r2 then some .choose else none
  | ⟨_, [⟨"a", .array (.u 32) _, .sharedBorrow⟩,
         ⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.idx "a" (.var "i"))))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one))))))
            (.return_ (.var "s"))))⟩ =>
    if s0 == 0 && i0 == 0 && one == 1 then some .sum else none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "v" _ (.vnew (.var "n")))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "j" _ (.lit (.u32 j0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.vset "v" (.var "i") (.var "i"))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one1))))))
      (.seq (.while_ (.ult (.var "j") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
                    (.assign "j" (.uadd (.var "j") (.lit (.u32 one2))))))
      (.seq (.vfree "v")
            (.return_ (.var "s"))))))))⟩ =>
    if i0 == 0 && s0 == 0 && j0 == 0 && one1 == 1 && one2 == 1 then
      some .vec
    else none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "a" _ (.vnew (.var "n")))
      (.seq (.let_ "b" _ (.vnew (.var "n")))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "j" _ (.lit (.u32 j0)))
      (.seq (.let_ "k" _ (.lit (.u32 k0)))
      (.seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.vset "a" (.var "i") (.var "i"))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one1))))))
      (.seq (.while_ (.ult (.var "j") (.var "n"))
              (.seq (.vset "b" (.var "j") (.vget "a" (.var "j")))
                    (.assign "j" (.uadd (.var "j") (.lit (.u32 one2))))))
      (.seq (.while_ (.ult (.var "k") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.vget "b" (.var "k"))))
                    (.assign "k" (.uadd (.var "k") (.lit (.u32 one3))))))
      (.seq (.vfree "a")
      (.seq (.vfree "b")
            (.return_ (.var "s"))))))))))))⟩ =>
    if i0 == 0 && j0 == 0 && k0 == 0 && s0 == 0 &&
        one1 == 1 && one2 == 1 && one3 == 1 then
      some .vec2
    else none
  | ⟨_, [⟨"x", .i 32, .owned⟩, ⟨"y", .i 32, .owned⟩,
         ⟨"z", .i 32, .owned⟩], _, body⟩ =>
    -- Body matched separately: list-literal patterns (`["x", "y"]`)
    -- nested inside a `⟨⟩` Func pattern hit a Lean parser quirk
    -- (unexpected `)`); matching `body` at `CStmt` level parses fine.
    match body with
    | .seq (.callRet "t" "add" ["x", "y"])
        (.seq (.callRet "r" "add" ["t", "z"])
              (.return_ (.var "r"))) => some .addCall
    | _ => none
  | ⟨_, [⟨"a", .array (.u 32) _, .sharedBorrow⟩,
         ⟨"n", .u 32, .owned⟩], _, body⟩ =>
    match body with
    | .seq (.callRet "s" "sum_array" ["a", "n"])
        (.return_ (.var "s")) => some .sumCall
    | _ => none
  | ⟨_, [⟨"p", .struct "Point" _, .owned⟩,
         ⟨"dx", .i 32, .owned⟩, ⟨"dy", .i 32, .owned⟩], _,
      .seq (.let_ "qx" _ (.add (.fget "p" "x") (.var "dx")))
      (.seq (.let_ "qy" _ (.add (.fget "p" "y") (.var "dy")))
            (.return_ (.pmk (.var "qx") (.var "qy"))))⟩ =>
    some .translate
  | ⟨_, [⟨"n", .u 32, .owned⟩, ⟨"m", .u 32, .owned⟩], _, body⟩ =>
    -- Nested loop bodies matched separately: deeply-nested `.seq`
    -- patterns inside `⟨⟩` Func patterns hit the same equation-compiler
    -- quirk as S1 list literals (cf. `addCall` note).
    match body with
    | .seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "j" _ (.lit (.u32 j0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.while_ (.ult (.var "j") (.var "m"))
                      (.seq (.assign "s" (.uadd (.var "s")
                        (.umul (.var "i") (.var "j"))))
                            (.assign "j" (.uadd (.var "j")
                              (.lit (.u32 one1))))))
                    (.seq (.assign "i" (.uadd (.var "i")
                            (.lit (.u32 one2))))
                          (.assign "j" (.lit (.u32 z0))))))
            (.return_ (.var "s"))))) =>
      if s0 == 0 && i0 == 0 && j0 == 0 && one1 == 1 && one2 == 1 && z0 == 0 then
        some .nested
      else none
    | _ => none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _, body⟩ =>
    match body with
    | .seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.if_ (.ueq (.var "i") (.lit (.u32 c2)))
                      (.seq (.assign "i" (.uadd (.var "i")
                              (.lit (.u32 one1)))) .continue_) .skip)
                    (.seq (.if_ (.ueq (.var "i") (.lit (.u32 c8)))
                              .break_ .skip)
                          (.seq (.assign "s" (.uadd (.var "s") (.var "i")))
                                (.assign "i" (.uadd (.var "i")
                                  (.lit (.u32 one2))))))))
            (.return_ (.var "s")))) =>
      if s0 == 0 && i0 == 0 && c2 == 2 && c8 == 8 && one1 == 1 && one2 == 1 then
        some .skip
      else none
    | _ => none
  | ⟨_, [⟨"a", .array (.u 32) _, .sharedBorrow⟩,
         ⟨"n", .u 32, .owned⟩, ⟨"k", .u 32, .owned⟩], _, body⟩ =>
    -- Three-param shape: body matched separately (cf. `addCall` note).
    match body with
    | .seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.if_ (.ueq (.idx "a" (.var "i")) (.var "k"))
                      (.return_ (.var "i")) .skip)
                    (.assign "i" (.uadd (.var "i")
                      (.lit (.u32 one))))))
            (.return_ (.var "n"))) =>
      if i0 == 0 && one == 1 then some .findEq else none
    | _ => none
  | ⟨_, [⟨"x", .u 32, .owned⟩], _, body⟩ =>
    match body with
    | .if_ (.ueq (.var "x") (.lit (.u32 c0)))
        (.return_ (.lit (.u32 r0)))
        (.if_ (.ueq (.var "x") (.lit (.u32 c1)))
              (.return_ (.lit (.u32 r1)))
              (.return_ (.lit (.u32 r2)))) =>
      if c0 == 0 && c1 == 1 && r0 == 10 && r1 == 20 && r2 == 30 then
        some .cls
      else none
    | _ => none
  | _ => none

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

theorem matchFrag_add : matchFrag addFunc = some .add := rfl

theorem matchFrag_incr : matchFrag incrFunc = some .incr := rfl

/-! ## Verified forward functions (Value level) -/

/-- Verified forward function for `add` (cf. rendered `add_fwd`). -/
def addFwd (a b : BitVec 32) : Result Value := .i32 <$> checkedAddI32 a b

/-- Verified forward function for `incr` (cf. rendered `incr_fwd`). -/
def incrFwd (p : BitVec 32) : Result Value := .i32 <$> checkedIncrI32 p

/-- `(<$>)` on `Result` computes on both constructors (for the corollaries).
    Proved by `rfl` (needs default transparency to see through the
    `Functor` instance, so later proofs use `exact`, not `simp`). -/
theorem i32_map_error (e : Panic) :
    Value.i32 <$> (Except.error e : Result (BitVec 32)) = .error e := rfl

theorem i32_map_ok (r : BitVec 32) :
    Value.i32 <$> (Except.ok r : Result (BitVec 32)) = .ok (.i32 r) := rfl

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

/-- `(<$>)` on `Result` computes on both constructors (for the 64-bit
    corollaries; cf. `i32_map_error`/`i32_map_ok`). -/
theorem i64_map_error (e : Panic) :
    Value.i64 <$> (Except.error e : Result (BitVec 64)) = .error e := rfl

theorem i64_map_ok (r : BitVec 64) :
    Value.i64 <$> (Except.ok r : Result (BitVec 64)) = .ok (.i64 r) := rfl

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

theorem matchFrag_add64 : matchFrag add64Func = some .add64 := rfl

theorem matchFrag_addu64 : matchFrag addu64Func = some .addu64 := rfl

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

theorem matchFrag_choose : matchFrag chooseFunc = some .choose := rfl

/-! ## `sum_array`: bounded loop over a length-paired array -/


/-- Splitting a drop at a valid index exposes head and tail. -/
theorem drop_cons_getElem (l : List (BitVec 32)) (k : Nat)
    (h : k < l.length) :
    l.drop k = l[k] :: l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk : k < xs.length := by
        simp only [List.length_cons] at h
        omega
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih k hk

/-! ### Canonical CoreIR + verified forward function -/

/-- Loop body: `s = s + a[i]; i = i + 1` (wrapping `u32`, plain `cir.add`;
    `cir.for` step region). The `1` is written `1#32` (`ofNat`-headed):
    simp's simprocs normalize `1` to `1#32`, so rewrite rules must use the
    normal form to match. -/
def sumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.idx "a" (.var "i"))))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Loop: `while (i < n) { ... }` (`cir.for` cond region). -/
def sumWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) sumBody

/-- Canonical CoreIR for `tests/c/sum_array.c`. `a` is a `sharedBorrow`
    (pure list value, copy semantics); `n` is the 32-bit length
    (C `size_t` lengths must fit 32 bits — `validate` narrows
    them, runtime excess is `OOB`). The static array bound (4096) equals
    `EVAL_FUEL`: capacity and fuel coincide by construction. -/
def sumFunc : Func :=
  ⟨"sum_array",
   [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq sumWhile
         (.return_ (.var "s"))))⟩

/-- Value-level forward function for `sum_array` (cf. rendered `sum_fwd`):
    wrapping prefix sum of the first `n` elements; `OOB` when `n` exceeds
    the array (C would read out of bounds there — UB made loud). -/
def sumFwd (l : List (BitVec 32)) (n : BitVec 32) : Result Value :=
  if n.toNat ≤ l.length then .ok (.u32 (prefixSumU32 l n.toNat))
  else .error .OOB

/-- OOB corollary helper: `sumFwd` reports `OOB` exactly off-range. -/
theorem sumFwd_oob (l : List (BitVec 32)) (n : BitVec 32)
    (h : ¬ n.toNat ≤ l.length) : sumFwd l n = .error .OOB := by
  simp [sumFwd, h]

theorem sumFwd_ok (l : List (BitVec 32)) (n : BitVec 32)
    (h : n.toNat ≤ l.length) :
    sumFwd l n = .ok (.u32 (prefixSumU32 l n.toNat)) := by
  simp [sumFwd, h]

theorem matchFrag_sum : matchFrag sumFunc = some .sum := rfl

/-! ### Loop invariant -/

/-- Loop environments: index `k` and accumulator, array and bound fixed. -/
def mkSumEnv (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) : Env :=
  [("i", .u32 (BitVec.ofNat 32 k)), ("s", .u32 acc),
   ("a", .arr32 l), ("n", .u32 nv)]

theorem mkSumEnv_i (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkSumEnv, envLookup]

theorem mkSumEnv_s (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "s" = some (.u32 acc) := by
  simp [mkSumEnv, envLookup, show ("s" : String) ≠ "i" by decide]

theorem mkSumEnv_a (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "a" = some (.arr32 l) := by
  simp [mkSumEnv, envLookup, show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "s" by decide]

theorem mkSumEnv_n (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "n" = some (.u32 nv) := by
  simp [mkSumEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "a" by decide]

/-- Updating `s` in a loop env stays a loop env. -/
theorem sumEnv_update_s (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkSumEnv l nv k acc) "s" (.u32 v) =
      some (mkSumEnv l nv k v) := by
  simp [mkSumEnv, envUpdate, show ("s" : String) ≠ "i" by decide]

/-- Updating `i` in a loop env stays a loop env. -/
theorem sumEnv_update_i (l : List (BitVec 32)) (nv : BitVec 32) (k k' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkSumEnv l nv k acc) "i" (.u32 (BitVec.ofNat 32 k')) =
      some (mkSumEnv l nv k' acc) := by
  simp [mkSumEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem sumCond_eval (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkSumEnv l nv k acc) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSumEnv_i l nv k acc
  have hn := mkSumEnv_n l nv k acc
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- One body step advances index and accumulator (any fuel: loop-free). -/
theorem sumBody_eval (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (k : Nat) (acc : BitVec 32)
    (hklen : k < l.length) (hk32 : k < 2 ^ 32) :
    evalStmtFuel F sumBody (mkSumEnv l nv k acc) =
      .ok (mkSumEnv l nv (k + 1) (acc + l[k]), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hklen
  have hs : evalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv k acc) = .ok (.u32 (acc + l[k])) := by
    have h1 := mkSumEnv_s l nv k acc
    have ha := mkSumEnv_a l nv k acc
    have hii := mkSumEnv_i l nv k acc
    simp only [evalExpr, h1, ha, hii, hkk, hget]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkSumEnv l nv k (acc + l[k])) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSumEnv_i l nv k (acc + l[k])
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := sumEnv_update_s l nv k acc (acc + l[k])
  have up2 := sumEnv_update_i l nv k (k + 1) (acc + l[k])
  cases F <;>
    simp [sumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs, hi2, up1, up2]

/-- The OOB step: at `k = length` the index read fails loudly
    (independent of the bound `n`). -/
theorem sumBody_oob (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (acc : BitVec 32) (h32 : l.length < 2 ^ 32) :
    evalStmtFuel F sumBody
        (mkSumEnv l nv l.length acc) = .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ h32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkSumEnv_a l nv l.length acc
  have hii := mkSumEnv_i l nv l.length acc
  have hs : evalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv l.length acc) = .error .OOB := by
    have h1 := mkSumEnv_s l nv l.length acc
    simp only [evalExpr, h1, ha, hii, hkk, hget]
  cases F <;>
    simp [sumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs]

/-- Loop correctness, in-range: the loop folds the remaining suffix. -/
theorem sumWhile_correct (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hlen : nv.toNat ≤ l.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F sumWhile (mkSumEnv l nv k acc) =
      .ok (mkSumEnv l nv nv.toNat
        (acc + prefixSumU32 (l.drop k) (nv.toNat - k)), .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkSumEnv l nv nv.toNat acc) = .ok (.b false) := by
      simpa using (sumCond_eval l nv nv.toNat acc h32)
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
    simp [sumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler, evalStmtWith,
      hcond, hsub, hpre]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < l.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) = .ok (.b true) := by
        simpa [hlt] using (sumCond_eval l nv k acc hk32)
      have hbody := sumBody_eval F l nv k acc hklen hk32
      have hstep : evalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
          = evalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k])) := by
        simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
          hbody]
      rw [hstep]
      have hrec := ih (k + 1) (acc + l[k]) (by omega) (by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hdrop : l.drop k = l[k] :: l.drop (k + 1) :=
        drop_cons_getElem l k hklen
      have hacc : (acc + l[k]) +
            prefixSumU32 (l.drop (k + 1)) (nv.toNat - (k + 1))
          = acc + prefixSumU32 (l.drop k) (nv.toNat - k) := by
        rw [hkk1, hdrop, prefixSumU32_cons]
        exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv nv.toNat acc) = .ok (.b false) := by
        simpa using (sumCond_eval l nv nv.toNat acc h32)
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
      simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
        hsub, hpre]

/-- Loop correctness, out-of-range: the loop reports `OOB` at the end.
    Note the bound is on the *length* (`hlen32`): `n` itself may exceed
    32 bits here (that is the OOB case); indices never pass `length`. -/
theorem sumWhile_oob (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ l.length)
    (hlt : l.length < nv.toNat)
    (hlen32 : l.length < 2 ^ 32)
    (hF : l.length - k + 1 ≤ F) :
    evalStmtFuel F sumWhile (mkSumEnv l nv k acc) = .error .OOB := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt2 : k < l.length
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) = .ok (.b true) := by
        have hkn : k < nv.toNat := by omega
        simpa [hkn] using (sumCond_eval l nv k acc hk32)
      have hbody := sumBody_eval F l nv k acc hlt2 hk32
      have hstep : evalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
          = evalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k])) := by
        simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
          hbody]
      rw [hstep]
      exact ih (k + 1) (acc + l[k]) (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv l.length acc) = .ok (.b true) := by
        simpa [hlt] using
          (sumCond_eval l nv l.length acc hlen32)
      have hbody := sumBody_oob F l nv acc hlen32
      simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
        hbody]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `sum`, at any fuel covering `n`. -/
theorem evalFuncFuel_sum (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = sumFwd l nv := by
  -- Stated with `ofNat`-headed zeros (simp's simprocs normalize `0` to
  -- `0#32`, so `OfNat`-headed forms would not match after normalization).
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  have hret := mkSumEnv_s l nv nv.toNat (prefixSumU32 l nv.toNat)
  -- The loop `have`s match simp's *unfolded* handler forms (the fuel
  -- equations necessarily unfold the loop while evaluating the lets, so a
  -- folded `evalStmtFuel` statement could never match). Handlers are named
  -- definitions (`evalStmtZeroHandler` / `evalStmtSuccHandler`), so the
  -- rules match syntactically; each is proved from the corresponding loop
  -- theorem by definitional unfolding (`exact` checks up to defeq).
  cases F with
  | zero =>
    -- Inside the zero branch `hF` forces `nv.toNat = 0`.
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            .fellThrough) :=
      sumWhile_correct l nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hle h32
        (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, sumFwd, henv, hloopH0, hret,
      hle]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            .fellThrough) :=
      sumWhile_correct l nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hle
        h32 (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, sumFwd, henv, hloopS, hret, hle]

/-- `emit_correct` for `sum` at the default fuel. -/
theorem emit_correct_sum (l : List (BitVec 32)) (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc sumFunc [.arr32 l, .u32 nv] = sumFwd l nv := by
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  exact evalFuncFuel_sum EVAL_FUEL l nv hle h32 hfuel

/-- OOB corollary: over-long lengths fail loudly on both sides. -/
theorem evalFuncFuel_sum_oob (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hlen32 : l.length < 2 ^ 32)
    (hF : l.length + 1 ≤ F) :
    evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .error .OOB := by
  -- `ofNat`-headed zeros (see `evalFuncFuel_sum`).
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0)) = .error .OOB :=
      sumWhile_oob l nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hlt hlen32
        (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, henv, hloopH0]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0)) = .error .OOB :=
      sumWhile_oob l nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hlt
        hlen32 (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, henv, hloopS]

/-- OOB corollary at the default fuel. -/
theorem emit_correct_sum_oob (l : List (BitVec 32)) (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hfuel : l.length + 1 ≤ EVAL_FUEL) :
    evalFunc sumFunc [.arr32 l, .u32 nv] = .error .OOB := by
  have hlen32 : l.length < 2 ^ 32 := by cir_fuel
  exact evalFuncFuel_sum_oob EVAL_FUEL l nv hlt hlen32 hfuel

/-! ## `vec_alloc`: uniquely-owned heap block (Phase 7, u32-only) -/

/-- Fill body: `v[i] = i; i = i + 1` (the value written is the index).
    The `1` is `1#32` (`ofNat`-headed, cf. `sumBody`). -/
def vecFillBody : CStmt :=
  .seq (.vset "v" (.var "i") (.var "i"))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Fill loop: `while (i < n) { ... }`. -/
def vecFillWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) vecFillBody

/-- Sum body: `s = s + v[j]; j = j + 1`. -/
def vecSumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 1#32))))

/-- Sum loop: `while (j < n) { ... }`. -/
def vecSumWhile : CStmt :=
  .while_ (.ult (.var "j") (.var "n")) vecSumBody

/-- Canonical CoreIR for `tests/c/vec_alloc.c`: allocate a zeroed `u32`
    block of `n` words (`malloc`), fill it with indices, sum it, `free`
    it, return the sum. `n` is the length (`u32`: C `size_t` must fit
    32 bits, like `sum_array`); the block lives in `v` as a `vecVal`. -/
def vecFunc : Func :=
  ⟨"vec_alloc",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "v" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "j" (.u 32) (.lit (.u32 0)))
   (.seq vecFillWhile
   (.seq vecSumWhile
   (.seq (.vfree "v")
         (.return_ (.var "s"))))))))⟩

theorem matchFrag_vec : matchFrag vecFunc = some .vec := rfl

/-- Value-level forward function for `vec_alloc` (cf. rendered
    `vec_alloc_fwd`): the pure heap program from `Circe.Base`. -/
def vecFwd (n : BitVec 32) : Result Value :=
  .u32 <$> vecFillSumU32 n.toNat

/-- `(<$>)` on `Result` computes on both constructors (for the corollaries;
    cf. `i32_map_error`/`i32_map_ok`). -/
theorem u32_map_error (e : Panic) :
    Value.u32 <$> (Except.error e : Result (BitVec 32)) = .error e := rfl

theorem u32_map_ok (r : BitVec 32) :
    Value.u32 <$> (Except.ok r : Result (BitVec 32)) = .ok (.u32 r) := rfl

/-! ### Heap loop environments -/

/-- Heap environments: block plus bound, both indices, accumulator.
    All four lets are bound before the fill loop, so one shape threads
    through both loops (`s`/`j` sit unused during fill). -/
def mkVecEnv (blk : Vec32) (nv iv sv jv : BitVec 32) : Env :=
  [("j", .u32 jv), ("s", .u32 sv), ("i", .u32 iv),
   ("v", .vecVal blk), ("n", .u32 nv)]

theorem mkVecEnv_j (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "j" = some (.u32 jv) := by
  simp [mkVecEnv, envLookup]

theorem mkVecEnv_s (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "s" = some (.u32 sv) := by
  simp [mkVecEnv, envLookup, show ("s" : String) ≠ "j" by decide]

theorem mkVecEnv_i (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "i" = some (.u32 iv) := by
  simp [mkVecEnv, envLookup, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

theorem mkVecEnv_v (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "v" = some (.vecVal blk) := by
  simp [mkVecEnv, envLookup, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem mkVecEnv_n (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "n" = some (.u32 nv) := by
  simp [mkVecEnv, envLookup, show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "v" by decide]

/-- Updating `v` in a heap env stays a heap env. -/
theorem vecEnv_update_v (blk : Vec32) (nv iv sv jv : BitVec 32)
    (blk' : Vec32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "v" (.vecVal blk') =
      some (mkVecEnv blk' nv iv sv jv) := by
  simp [mkVecEnv, envUpdate, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

/-- Updating `i` in a heap env stays a heap env. -/
theorem vecEnv_update_i (blk : Vec32) (nv iv iv' sv jv : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "i" (.u32 iv') =
      some (mkVecEnv blk nv iv' sv jv) := by
  simp [mkVecEnv, envUpdate, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

/-- Updating `s` in a heap env stays a heap env. -/
theorem vecEnv_update_s (blk : Vec32) (nv iv sv sv' jv : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "s" (.u32 sv') =
      some (mkVecEnv blk nv iv sv' jv) := by
  simp [mkVecEnv, envUpdate, show ("s" : String) ≠ "j" by decide]

/-- Updating `j` in a heap env stays a heap env. -/
theorem vecEnv_update_j (blk : Vec32) (nv iv sv jv jv' : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "j" (.u32 jv') =
      some (mkVecEnv blk nv iv sv jv') := by
  simp [mkVecEnv, envUpdate]

/-- The fill-loop condition reads the index against the bound. -/
theorem vecFillCond_eval (blk : Vec32) (nv : BitVec 32) (k : Nat)
    (sv jv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv
  have hn := mkVecEnv_n blk nv (BitVec.ofNat 32 k) sv jv
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- The sum-loop condition reads the index against the bound. -/
theorem vecSumCond_eval (blk : Vec32) (nv iv sv : BitVec 32) (k : Nat)
    (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hn := mkVecEnv_n blk nv iv sv (BitVec.ofNat 32 k)
  simp [evalExpr, hj, hn, ofNat32_ult k nv h]

/-- One fill step stores the index and advances (any fuel: loop-free). -/
theorem vecFillBody_eval (F : Nat) (blk : Vec32) (nv : BitVec 32)
    (k : Nat) (sv jv : BitVec 32) (blkMid : Vec32)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blk.freed = false)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid) :
    evalStmtFuel F vecFillBody
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (mkVecEnv blkMid nv (BitVec.ofNat 32 (k + 1)) sv jv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : evalExpr (.var "i")
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv)
  have harr := mkVecEnv_v blk nv (BitVec.ofNat 32 k) sv jv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vecEnv_update_v blk nv (BitVec.ofNat 32 k) sv jv blkMid
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVecEnv blkMid nv (BitVec.ofNat 32 k) sv jv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_i blkMid nv (BitVec.ofNat 32 k) sv jv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecEnv_update_i blkMid nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) sv jv
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `simp only`
  -- (unlike full `simp`) leaves `(ofNat 32 k).toNat` alone, so `hset'`
  -- fires as-is.
  cases F <;>
    simp only [vecFillBody, evalStmtFuel, evalStmtZero, evalStmtWith, hi, harr,
      hset', up1, hi2, up2]

/-- One sum step accumulates the block element and advances (any fuel). -/
theorem vecSumBody_eval (F : Nat) (blk : Vec32) (nv iv sv : BitVec 32)
    (k : Nat) (hk32 : k < 2 ^ 32)
    (hget : vecGet blk k = .ok (BitVec.ofNat 32 k)) :
    evalStmtFuel F vecSumBody
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
        (BitVec.ofNat 32 (k + 1)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hs0 := mkVecEnv_s blk nv iv sv (BitVec.ofNat 32 k)
  have harr := mkVecEnv_v blk nv iv sv (BitVec.ofNat 32 k)
  have hget' : vecGet blk (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hg : evalExpr (.vget "v" (.var "j"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hj, harr, hget']
  have hs : evalExpr (.uadd (.var "s") (.vget "v" (.var "j")))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hs0, hj, harr, hget']
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k) (BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_j blk nv iv (sv + BitVec.ofNat 32 k)
      (BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vecEnv_update_s blk nv iv sv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k)
  have up2 := vecEnv_update_j blk nv iv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k) (BitVec.ofNat 32 (k + 1))
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `hs`/`hg` are
  -- `evalExpr`-headed (no `evalExpr` unfolding in the set), so they fire
  -- as-is; `hj`/`harr`/`hget'` discharge the inner `vget` matches.
  cases F <;>
    simp only [vecSumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs, hj2,
      up1, up2]

/-! ### Heap loop correctness (fuel-generalized) -/

/-- Fill-loop correctness: the eval loop runs the `Base` fill to completion.
    The `Base` program (`hfill`) is both spec and witness: induction follows
    its unfolding, like `sumWhile_correct`. -/
theorem vecFillWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (sv jv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hfill : vecFillLoopAux blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vecFillWhile
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat) sv jv,
        .fellThrough) := by
  induction F generalizing k blk blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    -- `subst` creates `ofNat 32 nv.toNat`; `simp only` (unlike full `simp`)
    -- leaves it alone, so the cond fact stays in `ofNat` form and `rw`
    -- fires syntactically (cf. probe6).
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) =
        .ok (.b false) := by
      have hc := vecFillCond_eval blk nv nv.toNat sv jv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    simp only [vecFillWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
          .ok (.b true) := by
        simpa [hlt] using (vecFillCond_eval blk nv k sv jv hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      -- hfill : Aux ⟨set ..⟩ (k+1) (n-(k+1)) = ok blkOut
      have hbody := vecFillBody_eval F blk nv k sv jv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vecFillWhile
            (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv)
          = evalStmtFuel F vecFillWhile
            (mkVecEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv
              (BitVec.ofNat 32 (k + 1)) sv jv) := by
        simp [vecFillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blk.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      exact ih ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) =
          .ok (.b false) := by
        have hc := vecFillCond_eval blk nv nv.toNat sv jv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      simp only [vecFillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-- Sum-loop correctness: the eval loop runs the `Base` sum to completion. -/
theorem vecSumWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv : BitVec 32) (sout : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blk j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hsum : vecSumLoopAux blk k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vecSumWhile
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (mkVecEnv blk nv iv sout (BitVec.ofNat 32 nv.toNat),
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) =
        .ok (.b false) := by
      have hc := vecSumCond_eval blk nv iv sv nv.toNat hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vecSumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
          .ok (.b true) := by
        simpa [hlt] using (vecSumCond_eval blk nv iv sv k hk32)
      have hgetk : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := vecSumBody_eval F blk nv iv sv k hk32 hgetk
      have hstep : evalStmtFuel (F + 1) vecSumWhile
            (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k))
          = evalStmtFuel F vecSumWhile
            (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
              (BitVec.ofNat 32 (k + 1))) := by
        simp [vecSumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux, hgetk] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) =
          .ok (.b false) := by
        have hc := vecSumCond_eval blk nv iv sv nv.toNat hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vecSumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `vec_alloc`, at any fuel covering `n`. -/
theorem evalFuncFuel_vec (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    evalFuncFuel F vecFunc [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ : Vec32).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkOut, hfill0⟩ := vecFillLoopAux_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 32 0)) 0 nv.toNat (by simp)
  have hliveOut : blkOut.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hgetOut : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  have hsum0 := vecSumLoopAux_correct blkOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetOut j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range nv.toNat).map
      (BitVec.ofNat 32)) nv.toNat
      = prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfree0 : vecFree blkOut = .ok ⟨blkOut.val, true⟩ :=
    vecFree_ok blkOut hliveOut
  -- The four lets build the heap env (stated `ofNat`-headed: simp's
  -- simprocs normalize `0` to `0#32`).
  have henv : [("j", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("n", .u32 nv)]
      = mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) := rfl
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  -- Loop haves match simp's unfolded handler forms (cf. `evalFuncFuel_sum`).
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by cir_fuel
    have hloopF0 : evalStmtWith evalStmtZeroHandler
          vecFillWhile
          (mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vecFillWhile_correct _ _ 0 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hF0
    have hloopS0 : evalStmtWith evalStmtZeroHandler
          vecSumWhile
          (mkVecEnv blkOut nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv nv
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), .fellThrough) :=
      vecSumWhile_correct blkOut nv 0 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hF0
    have huv := vecEnv_update_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    simp [evalFuncFuel, vecFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, hn0, vecNew, henv,
      hloopF0, hloopS0, hfree0, huv, harv, hars]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    have hloopFS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecFillWhile
          (mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vecFillWhile_correct _ _ (F + 1) 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hFS
    have hloopSS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecSumWhile
          (mkVecEnv blkOut nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv nv
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), .fellThrough) :=
      vecSumWhile_correct blkOut nv (F + 1) 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hFS
    have huv := vecEnv_update_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    simp [evalFuncFuel, vecFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, hn0, vecNew, henv, hloopFS,
      hloopSS, hfree0, huv, harv, hars]

/-- `emit_correct` for `vec_alloc` at the default fuel. -/
theorem emit_correct_vec (nv : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc vecFunc [.u32 nv] = vecFwd nv := by
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  have h := evalFuncFuel_vec EVAL_FUEL nv hfuel h32
  have hc := vecFillSumU32_correct nv.toNat
  simp only [evalFunc, vecFwd, h, hc, u32_map_ok]

/-! ## M1a: two live blocks (`vec_copy_sum`) -/

/-- Fill body over `a`: `a[i] = i; i = i + 1`. -/
def vec2FillBody : CStmt :=
  .seq (.vset "a" (.var "i") (.var "i"))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Fill loop over `a`: `while (i < n) { ... }`. -/
def vec2FillWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) vec2FillBody

/-- Copy body: `b[j] = a[j]; j = j + 1` (cross-block read: both blocks
    live simultaneously — the M1a shape). -/
def vec2CopyBody : CStmt :=
  .seq (.vset "b" (.var "j") (.vget "a" (.var "j")))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 1#32))))

/-- Copy loop: `while (j < n) { ... }`. -/
def vec2CopyWhile : CStmt :=
  .while_ (.ult (.var "j") (.var "n")) vec2CopyBody

/-- Sum body over `b`: `s = s + b[k]; k = k + 1`. -/
def vec2SumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.vget "b" (.var "k"))))
       (.assign "k" (.uadd (.var "k") (.lit (.u32 1#32))))

/-- Sum loop over `b`: `while (k < n) { ... }`. -/
def vec2SumWhile : CStmt :=
  .while_ (.ult (.var "k") (.var "n")) vec2SumBody

/-- Canonical CoreIR for `tests/c/vec_copy_sum.c`: allocate two `u32`
    blocks, fill `a` with indices, copy `a` into `b`, sum `b`, free
    both, return the sum. The two blocks are disjoint by construction
    (two `malloc` results); the model captures this as two separate
    values. -/
def vec2Func : Func :=
  ⟨"vec_copy_sum",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "a" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "b" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "j" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "k" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq vec2FillWhile
   (.seq vec2CopyWhile
   (.seq vec2SumWhile
   (.seq (.vfree "a")
   (.seq (.vfree "b")
         (.return_ (.var "s"))))))))))))⟩

theorem matchFrag_vec2 : matchFrag vec2Func = some .vec2 := rfl

/-- Value-level forward for `vec_copy_sum`: the copy is value-invisible,
    so the forward is the same index-sum as `vec_alloc`
    (cf. rendered `vec_copy_sum_fwd`). -/
def vec2Fwd (n : BitVec 32) : Result Value :=
  .u32 <$> vecFillSumU32 n.toNat

/-- The two-block forward agrees with the single-block forward. -/
theorem vec2Fwd_eq_vecFwd (n : BitVec 32) : vec2Fwd n = vecFwd n := rfl

/-! ### Two-block heap environments -/

/-- Two-block environments: both blocks plus bound, all three indices,
    accumulator. All six lets are bound before the fill loop, so one
    shape threads through all three loops. -/
def mkVec2Env (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) : Env :=
  [("s", .u32 sv), ("k", .u32 kv), ("j", .u32 jv), ("i", .u32 iv),
   ("b", .vecVal blkB), ("a", .vecVal blkA), ("n", .u32 nv)]

theorem mkVec2Env_s (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "s" = some (.u32 sv) := by
  simp [mkVec2Env, envLookup]

theorem mkVec2Env_k (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "k" = some (.u32 kv) := by
  simp [mkVec2Env, envLookup, show ("k" : String) ≠ "s" by decide]

theorem mkVec2Env_j (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "j" = some (.u32 jv) := by
  simp [mkVec2Env, envLookup, show ("j" : String) ≠ "s" by decide,
    show ("j" : String) ≠ "k" by decide]

theorem mkVec2Env_i (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "i" = some (.u32 iv) := by
  simp [mkVec2Env, envLookup, show ("i" : String) ≠ "s" by decide,
    show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide]

theorem mkVec2Env_b (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "b" =
      some (.vecVal blkB) := by
  simp [mkVec2Env, envLookup, show ("b" : String) ≠ "s" by decide,
    show ("b" : String) ≠ "k" by decide,
    show ("b" : String) ≠ "j" by decide,
    show ("b" : String) ≠ "i" by decide]

theorem mkVec2Env_a (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "a" =
      some (.vecVal blkA) := by
  simp [mkVec2Env, envLookup, show ("a" : String) ≠ "s" by decide,
    show ("a" : String) ≠ "k" by decide,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "b" by decide]

theorem mkVec2Env_n (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "n" = some (.u32 nv) := by
  simp [mkVec2Env, envLookup, show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "k" by decide,
    show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "b" by decide,
    show ("n" : String) ≠ "a" by decide]

/-- Updating `a` in a two-block env stays a two-block env. -/
theorem vec2Env_update_a (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32)
    (blkA' : Vec32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "a" (.vecVal blkA') =
      some (mkVec2Env blkA' blkB nv iv jv kv sv) := by
  simp [mkVec2Env, envUpdate, show ("a" : String) ≠ "s" by decide,
    show ("a" : String) ≠ "k" by decide,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "b" by decide]

/-- Updating `b` in a two-block env stays a two-block env. -/
theorem vec2Env_update_b (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32)
    (blkB' : Vec32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "b" (.vecVal blkB') =
      some (mkVec2Env blkA blkB' nv iv jv kv sv) := by
  simp [mkVec2Env, envUpdate, show ("b" : String) ≠ "s" by decide,
    show ("b" : String) ≠ "k" by decide,
    show ("b" : String) ≠ "j" by decide,
    show ("b" : String) ≠ "i" by decide]

/-- Updating `i` in a two-block env stays a two-block env. -/
theorem vec2Env_update_i (blkA blkB : Vec32) (nv iv iv' jv kv sv : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "i" (.u32 iv') =
      some (mkVec2Env blkA blkB nv iv' jv kv sv) := by
  simp [mkVec2Env, envUpdate, show ("i" : String) ≠ "s" by decide,
    show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide]

/-- Updating `j` in a two-block env stays a two-block env. -/
theorem vec2Env_update_j (blkA blkB : Vec32) (nv iv jv jv' kv sv : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "j" (.u32 jv') =
      some (mkVec2Env blkA blkB nv iv jv' kv sv) := by
  simp [mkVec2Env, envUpdate, show ("j" : String) ≠ "s" by decide,
    show ("j" : String) ≠ "k" by decide]

/-- Updating `k` in a two-block env stays a two-block env. -/
theorem vec2Env_update_k (blkA blkB : Vec32) (nv iv jv kv kv' sv : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "k" (.u32 kv') =
      some (mkVec2Env blkA blkB nv iv jv kv' sv) := by
  simp [mkVec2Env, envUpdate, show ("k" : String) ≠ "s" by decide]

/-- Updating `s` in a two-block env stays a two-block env. -/
theorem vec2Env_update_s (blkA blkB : Vec32) (nv iv jv kv sv sv' : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "s" (.u32 sv') =
      some (mkVec2Env blkA blkB nv iv jv kv sv') := by
  simp [mkVec2Env, envUpdate]

/-! ### Two-block loop steps -/

/-- The fill-loop condition reads `i` against the bound. -/
theorem vec2FillCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (jv kv sv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hn := mkVec2Env_n blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- The copy-loop condition reads `j` against the bound. -/
theorem vec2CopyCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv sv kv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "n"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hn := mkVec2Env_n blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  simp [evalExpr, hj, hn, ofNat32_ult k nv h]

/-- The sum-loop condition reads `k` against the bound. -/
theorem vec2SumCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv jv sv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "k") (.var "n"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hn := mkVec2Env_n blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  simp [evalExpr, hk, hn, ofNat32_ult k nv h]

/-- One fill step stores the index into `a` and advances (any fuel). -/
theorem vec2FillBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (jv kv sv : BitVec 32) (blkMid : Vec32)
    (_hklen : k < blkA.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blkA.freed = false)
    (hset : vecSet blkA k (BitVec.ofNat 32 k) = .ok blkMid) :
    evalStmtFuel F vec2FillBody
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (mkVec2Env blkMid blkB nv (BitVec.ofNat 32 (k + 1)) jv kv sv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : evalExpr (.var "i")
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv)
  have harr := mkVec2Env_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hset' : vecSet blkA (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vec2Env_update_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
    blkMid
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVec2Env blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_i blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_i blkMid blkB nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) jv kv sv
  cases F <;>
    simp only [vec2FillBody, evalStmtFuel, evalStmtZero, evalStmtWith, hi,
      harr, hset', up1, hi2, up2]

/-- One copy step reads `a[j]`, stores into `b[j]`, advances (any fuel). -/
theorem vec2CopyBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv sv kv : BitVec 32) (x : BitVec 32) (blkMid : Vec32)
    (hk32 : k < 2 ^ 32)
    (hget : vecGet blkA k = .ok x)
    (hset : vecSet blkB k x = .ok blkMid) :
    evalStmtFuel F vec2CopyBody
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 (k + 1)) kv sv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj : evalExpr (.var "j")
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv)
  have ha := mkVec2Env_a blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hb := mkVec2Env_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hget' : vecGet blkA (BitVec.ofNat 32 k).toNat = .ok x := by
    rw [hkk]; exact hget
  have hg : evalExpr (.vget "a" (.var "j"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 x) := by
    -- `hj` (eval`Expr`-headed) would compete with `evalExpr` unfolding and
    -- lose, so discharge the index lookup with the `envLookup`-headed
    -- `hjl` instead (no competing rule).
    have hjl := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    simp only [evalExpr, hjl, ha, hget']
  have hset' : vecSet blkB (BitVec.ofNat 32 k).toNat x = .ok blkMid := by
    rw [hkk]; exact hset
  have up1 := vec2Env_update_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    blkMid
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_j blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_j blkA blkMid nv iv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) kv sv
  cases F <;>
    simp only [vec2CopyBody, evalStmtFuel, evalStmtZero, evalStmtWith, hj,
      hb, hg, hset', up1, hj2, up2]

/-- One sum step accumulates `b[k]` and advances (any fuel). -/
theorem vec2SumBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv jv sv : BitVec 32)
    (hk32 : k < 2 ^ 32)
    (hget : vecGet blkB k = .ok (BitVec.ofNat 32 k)) :
    evalStmtFuel F vec2SumBody
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
        (sv + BitVec.ofNat 32 k), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hs0 := mkVec2Env_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have harr := mkVec2Env_b blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hget' : vecGet blkB (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hg : evalExpr (.vget "b" (.var "k"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hk, harr, hget']
  have hs : evalExpr (.uadd (.var "s") (.vget "b" (.var "k")))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hs0, hk, harr, hget']
  have hk2 : evalExpr (.uadd (.var "k") (.lit (.u32 1#32)))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k)
          (sv + BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
      (sv + BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vec2Env_update_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
    (sv + BitVec.ofNat 32 k)
  have up2 := vec2Env_update_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) (sv + BitVec.ofNat 32 k)
  cases F <;>
    simp only [vec2SumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs,
      hk2, up1, up2]

/-! ### Two-block loop correctness (fuel-generalized) -/

/-- Fill-loop correctness over `a`: the eval loop runs the `Base` fill
    to completion (mirror of `vecFillWhile_correct`). -/
theorem vec2FillWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (jv kv sv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlen : blkA.val.length = nv.toNat)
    (hlive : blkA.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hfill : vecFillLoopAux blkA k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec2FillWhile
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (mkVec2Env blkOut blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv,
        .fellThrough) := by
  induction F generalizing k blkA blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) =
        .ok (.b false) := by
      have hc := vec2FillCond_eval blkA blkB nv nv.toNat jv kv sv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    simp only [vec2FillWhile, evalStmtFuel, evalStmtZero,
      evalStmtZeroHandler, evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blkA.val.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
            .ok (.b true) := by
        simpa [hlt] using (vec2FillCond_eval blkA blkB nv k jv kv sv hk32)
      have hset : vecSet blkA k (BitVec.ofNat 32 k) =
          .ok ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkA k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      have hbody := vec2FillBody_eval F blkA blkB nv k jv kv sv
        ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vec2FillWhile
            (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv)
          = evalStmtFuel F vec2FillWhile
            (mkVec2Env ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ blkB nv
              (BitVec.ofNat 32 (k + 1)) jv kv sv) := by
        simp [vec2FillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blkA.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      exact ih ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) =
          .ok (.b false) := by
        have hc := vec2FillCond_eval blkA blkB nv nv.toNat jv kv sv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      simp only [vec2FillWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-- Copy-loop correctness: the eval loop runs the `Base` copy to
    completion. `blkA` is fixed (read-only source); `blkB` accumulates
    the copy. -/
theorem vec2CopyWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv kv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlenA : blkA.val.length = nv.toNat)
    (hlenB : blkB.val.length = nv.toNat)
    (_hliveA : blkA.freed = false) (hliveB : blkB.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hpre : ∀ t, t < k → vecGet blkB t = .ok (BitVec.ofNat 32 t))
    (hsrc : ∀ t, t < nv.toNat → vecGet blkA t = .ok (BitVec.ofNat 32 t))
    (hcopy : vecCopyLoopAux blkA blkB k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec2CopyWhile
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (mkVec2Env blkA blkOut nv iv (BitVec.ofNat 32 nv.toNat) kv sv,
        .fellThrough) := by
  -- `hliveA`: the copy loop never touches `a`'s token (reads go through
  -- `hsrc`, which already says they succeed), so liveness is implied.
  -- Kept as a premise to mirror the fill/sum shapes.
  induction F generalizing k blkB blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "j") (.var "n"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) =
        .ok (.b false) := by
      have hc := vec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hcopy
    simp only [vecCopyLoopAux] at hcopy
    cases hcopy
    simp only [vec2CopyWhile, evalStmtFuel, evalStmtZero,
      evalStmtZeroHandler, evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklenB : k < blkB.val.length := by omega
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
            .ok (.b true) := by
        simpa [hlt] using (vec2CopyCond_eval blkA blkB nv k iv sv kv hk32)
      have hgetk : vecGet blkA k = .ok (BitVec.ofNat 32 k) :=
        hsrc k (by omega)
      have hset : vecSet blkB k (BitVec.ofNat 32 k) =
          .ok ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkB k _ hliveB hklenB
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hcopy
      simp only [vecCopyLoopAux, hgetk, hset] at hcopy
      have hbody := vec2CopyBody_eval F blkA blkB nv k iv sv kv
        (BitVec.ofNat 32 k)
        ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩
        hk32 hgetk hset
      have hstep : evalStmtFuel (F + 1) vec2CopyWhile
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv)
          = evalStmtFuel F vec2CopyWhile
            (mkVec2Env blkA
              ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ nv iv
              (BitVec.ofNat 32 (k + 1)) kv sv) := by
        simp [vec2CopyWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blkB.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      have hpre' : ∀ t, t < k + 1 →
          vecGet ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ t =
            .ok (BitVec.ofNat 32 t) := by
        intro t ht
        by_cases htk : t = k
        · subst t
          rw [vecGet_ok _ _ _ rfl]
          exact getElem?_set_self blkB.val k _ hklenB
        · exact vecSet_get_other blkB k t _ _ _ (by omega) hset
            (hpre t (by omega))
      exact ih ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hpre' hcopy (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) =
          .ok (.b false) := by
        have hc := vec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hcopy
      simp only [vecCopyLoopAux] at hcopy
      cases hcopy
      simp only [vec2CopyWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-- Sum-loop correctness over `b`: the eval loop runs the `Base` sum to
    completion (mirror of `vecSumWhile_correct`). -/
theorem vec2SumWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv jv sv : BitVec 32) (sout : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blkB j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hsum : vecSumLoopAux blkB k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec2SumWhile
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sout,
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "k") (.var "n"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) =
        .ok (.b false) := by
      have hc := vec2SumCond_eval blkA blkB nv nv.toNat iv jv sv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vec2SumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "k") (.var "n"))
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
            .ok (.b true) := by
        simpa [hlt] using (vec2SumCond_eval blkA blkB nv k iv jv sv hk32)
      have hgetk : vecGet blkB k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux, hgetk] at hsum
      have hbody := vec2SumBody_eval F blkA blkB nv k iv jv sv hk32 hgetk
      have hstep : evalStmtFuel (F + 1) vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv)
          = evalStmtFuel F vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
              (sv + BitVec.ofNat 32 k)) := by
        simp [vec2SumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (fun j hjlo hjhi => hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "k") (.var "n"))
          (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) =
          .ok (.b false) := by
        have hc := vec2SumCond_eval blkA blkB nv nv.toNat iv jv sv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vec2SumWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `vec_copy_sum`, at any fuel covering `n`. The
    fill produces indices in `a` (existing `Base` facts), the copy
    carries them into `b` (`vecCopyLoopAux_all`), the sum folds `b`
    (existing `vecSumLoopAux_correct`). -/
theorem evalFuncFuel_vec2 (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    evalFuncFuel F vec2Func [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ : Vec32).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkAOut, hfill0⟩ := vecFillLoopAux_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 32 0)) 0 nv.toNat (by simp)
  have hliveAOut : blkAOut.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hlenAOut : blkAOut.val.length = nv.toNat := by
    have h := vecFillLoopAux_length _ _ _ _ hfill0
    simp at h
    exact h
  have hgetA : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkAOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  obtain ⟨blkBOut, hcopy0⟩ := vecCopyLoopAux_fresh_ok blkAOut
    ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ 0 nv.toNat
    hliveAOut rfl (by rw [hlenAOut]; simp) (by omega)
    (fun t ht => hgetA t (by omega) (by omega))
  have hliveBOut : blkBOut.freed = false :=
    vecCopyLoopAux_live _ _ _ _ _ rfl hcopy0
  have hlenBOut : blkBOut.val.length = nv.toNat := by
    have h := vecCopyLoopAux_length _ _ _ _ _ hcopy0
    simp at h
    exact h
  have hgetB : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkBOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + (nv.toNat - 0) := by omega
    exact vecCopyLoopAux_all blkAOut
      ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ 0
      (nv.toNat - 0) blkBOut rfl (by rw [hlenAOut]; simp) (by omega)
      (fun t ht => absurd ht (by omega))
      (fun t ht => hgetA t (by omega) (by omega)) hcopy0 j hjhi'
  have hsum0 := vecSumLoopAux_correct blkBOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetB j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range nv.toNat).map
      (BitVec.ofNat 32)) nv.toNat
      = prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfreeA : vecFree blkAOut = .ok ⟨blkAOut.val, true⟩ :=
    vecFree_ok blkAOut hliveAOut
  have hfreeB : vecFree blkBOut = .ok ⟨blkBOut.val, true⟩ :=
    vecFree_ok blkBOut hliveBOut
  -- The second `vnew` reads `n` past the `a` binding: no `hn0`-shaped
  -- fact covers it (contrast `vec`, whose single `vnew` is the first
  -- let), so state it exactly. `simp` never unfolds `envLookup` on its
  -- own (probed) — every lookup redex needs a rewrite fact.
  have hna : envLookup [("a", .vecVal
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
      ("n", .u32 nv)] "n" = some (.u32 nv) := by
    simp [envLookup, show ("n" : String) ≠ "a" by decide]
  -- The six lets build the two-block env (stated `ofNat`-headed: simp's
  -- simprocs normalize `0` to `0#32`).
  have henv : [("s", .u32 (BitVec.ofNat 32 0)),
        ("k", .u32 (BitVec.ofNat 32 0)),
        ("j", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("b", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("a", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("n", .u32 nv)]
      = mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) := rfl
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  -- Loop haves match simp's unfolded handler forms (cf. `evalFuncFuel_sum`).
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by cir_fuel
    have hloopF0 : evalStmtWith evalStmtZeroHandler
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vec2FillWhile_correct _ _ _ 0 0 _ _ _ blkAOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hF0
    have hloopC0 : evalStmtWith evalStmtZeroHandler
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), .fellThrough) :=
      vec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0 nv
        (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) blkBOut (Nat.zero_le _) hlenAOut (by simp)
        hliveAOut rfl hn32
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 hF0
    have hloopS0 : evalStmtWith evalStmtZeroHandler
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), .fellThrough) :=
      vec2SumWhile_correct blkAOut blkBOut nv 0 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hsum0 hF0
    have hfreeA' := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have hfreeB' := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have hrets := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [evalFuncFuel, vec2Func, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, hn0, hna, vecNew, henv,
      mkVec2Env_a, mkVec2Env_b, hloopF0, hloopC0, hloopS0, hfreeA, hfreeB,
      hfreeA', hfreeB', hrets]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    have hloopFS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vec2FillWhile_correct _ _ _ (F + 1) 0 _ _ _ blkAOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hFS
    have hloopCS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), .fellThrough) :=
      vec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0
        nv (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) blkBOut (Nat.zero_le _) hlenAOut (by simp)
        hliveAOut rfl hn32
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 hFS
    have hloopSS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), .fellThrough) :=
      vec2SumWhile_correct blkAOut blkBOut nv (F + 1) 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hsum0 hFS
    have hfreeA' := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have hfreeB' := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have hrets := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [evalFuncFuel, vec2Func, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, hn0, hna, vecNew, henv, mkVec2Env_a,
      mkVec2Env_b, hloopFS,
      hloopCS, hloopSS, hfreeA, hfreeB, hfreeA', hfreeB', hrets]

/-- `emit_correct` for `vec_copy_sum` at the default fuel. -/
theorem emit_correct_vec2 (nv : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc vec2Func [.u32 nv] = vec2Fwd nv := by
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  have h := evalFuncFuel_vec2 EVAL_FUEL nv hfuel h32
  have hc := vecFillSumU32_correct nv.toNat
  simp only [evalFunc, vec2Fwd, h, hc, u32_map_ok]

/-- Corollary: `vec_copy_sum` delivers the `range` prefix sum on success. -/
theorem emit_correct_vec2_ok (nv : BitVec 32) (r : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL)
    (h : vecFillSumU32 nv.toNat = .ok r) :
    evalFunc vec2Func [.u32 nv] = .ok (.u32 r) := by
  rw [emit_correct_vec2 nv hfuel]
  unfold vec2Fwd
  rw [h]
  exact u32_map_ok r

/-! ## S1: DAG calls (`add_caller`, `sum_caller`) -/

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

/-- Canonical CoreIR for `tests/c/add_caller.c`: two DAG calls into `add`
    (`t = add(x,y); return add(t,z)`). Both call sites target the
    call-free leaf `addFunc` (matched by name in `evalProgStmt`). -/
def addCallerFunc : Func :=
  ⟨"add_caller",
   [{ name := "x", ty := .i 32, role := .owned },
    { name := "y", ty := .i 32, role := .owned },
    { name := "z", ty := .i 32, role := .owned }],
   .i 32,
   .seq (.callRet "t" "add" ["x", "y"])
   (.seq (.callRet "r" "add" ["t", "z"])
         (.return_ (.var "r")))⟩

/-- Canonical CoreIR for `tests/c/sum_caller.c`: single DAG call
    delegating to `sum_array`. -/
def sumCallerFunc : Func :=
  ⟨"sum_caller",
   [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.callRet "s" "sum_array" ["a", "n"])
        (.return_ (.var "s"))⟩

theorem matchFrag_addCaller : matchFrag addCallerFunc = some .addCall := rfl

theorem matchFrag_sumCaller : matchFrag sumCallerFunc = some .sumCall := rfl

/-- Value-level forward for `add_caller`: sequential `Result` binds over
    the leaf op (cf. rendered `add_caller_fwd`). -/
def addCallerFwd (x y z : BitVec 32) : Result Value :=
  match checkedAddI32 x y with
  | .error e => .error e
  | .ok t => .i32 <$> checkedAddI32 t z

/-- The forward is literally two `add_fwd` calls sequenced (call structure
    explicit; the second match arm is unreachable since `addFwd` only
    produces `i32` values). -/
theorem addCallerFwd_as_calls (x y z : BitVec 32) :
    addCallerFwd x y z =
      match addFwd x y with
      | .error e => .error e
      | .ok (.i32 t) => .i32 <$> checkedAddI32 t z
      | .ok _ => .error .AssertFail := by
  cases h : checkedAddI32 x y <;>
    simp [addCallerFwd, addFwd, h, i32_map_error, i32_map_ok]

/-- Value-level forward for `sum_caller`: direct delegation to `sumFwd`
    (cf. rendered `sum_caller_fwd`). -/
def sumCallerFwd (l : List (BitVec 32)) (n : BitVec 32) : Result Value :=
  sumFwd l n

theorem sumCallerFwd_is_call (l : List (BitVec 32)) (n : BitVec 32) :
    sumCallerFwd l n = sumFwd l n := rfl

/-- Env facts for the `add_caller` shape. -/
theorem envLookup_addCaller_x (x y z : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] "x" =
      some (.i32 x) := by
  simp [envLookup]

theorem envLookup_addCaller_y (x y z : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] "y" =
      some (.i32 y) := by
  simp [envLookup, show ("y" : String) ≠ "x" by decide]

theorem envLookup_addCaller_z (x y z : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] "z" =
      some (.i32 z) := by
  simp [envLookup, show ("z" : String) ≠ "x" by decide,
    show ("z" : String) ≠ "y" by decide]

/-- Env facts for the `sum_caller` shape. -/
theorem envLookup_sumCaller_a (l : List (BitVec 32)) (nv : BitVec 32) :
    envLookup [("a", .arr32 l), ("n", .u32 nv)] "a" =
      some (.arr32 l) := by
  simp [envLookup]

theorem envLookup_sumCaller_n (l : List (BitVec 32)) (nv : BitVec 32) :
    envLookup [("a", .arr32 l), ("n", .u32 nv)] "n" = some (.u32 nv) := by
  simp [envLookup, show ("n" : String) ≠ "a" by decide]

/-- `emit_correct` for `add_caller`: program evaluation over `[addFunc]`
    agrees with the forward on all inputs (ok and error paths). -/
theorem evalProgFunc_addCaller (F : Nat) (x y z : BitVec 32) :
    evalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] =
      addCallerFwd x y z := by
  have hbind : bindArgs addCallerFunc.args [.i32 x, .i32 y, .i32 z] =
      some [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] := rfl
  have hbody : addCallerFunc.body =
      .seq (.callRet "t" "add" ["x", "y"])
      (.seq (.callRet "r" "add" ["t", "z"])
            (.return_ (.var "r"))) := rfl
  have hx := envLookup_addCaller_x x y z
  have hy := envLookup_addCaller_y x y z
  have hfind : findFunc [addFunc] "add" = some addFunc :=
    findFunc_hit addFunc []
  cases h1 : checkedAddI32 x y with
  | error e =>
    have hc1 : evalFuncFuel F addFunc [.i32 x, .i32 y] = .error e := by
      rw [evalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_error e
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := evalProgStmt_callRet_err [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
      [.i32 x, .i32 y] addFunc e hargs1 hfind hc1
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep1]
    simp [addCallerFwd, h1]
  | ok t =>
    have hc1 : evalFuncFuel F addFunc [.i32 x, .i32 y] =
        .ok (.i32 t) := by
      rw [evalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_ok t
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := evalProgStmt_callRet_ok [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
      [.i32 x, .i32 y] addFunc (.i32 t) hargs1 hfind hc1
    have htz : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "t" = some (.i32 t) :=
      envExtend_hit _ _ _
    have htz2 : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "z" = some (.i32 z) := by
      simp [envExtend, envLookup, show ("z" : String) ≠ "t" by decide]
    cases h2 : checkedAddI32 t z with
    | error e =>
      have hc2 : evalFuncFuel F addFunc [.i32 t, .i32 z] = .error e := by
        rw [evalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_error e
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := evalProgStmt_callRet_err [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t))
        [.i32 t, .i32 z] addFunc e hargs2 hfind hc2
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_err _ _ _ _ _ _ hstep2]
      simp [addCallerFwd, h1, h2, i32_map_error]
    | ok r =>
      have hc2 : evalFuncFuel F addFunc [.i32 t, .i32 z] =
          .ok (.i32 r) := by
        rw [evalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_ok r
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := evalProgStmt_callRet_ok [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t))
        [.i32 t, .i32 z] addFunc (.i32 r) hargs2 hfind hc2
      have hret : evalProgStmt [addFunc] F (.return_ (.var "r"))
          (envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r)) =
          .ok (envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r),
            .returned (.i32 r)) :=
        evalProgStmt_return [addFunc] F (.var "r") _
          (.i32 r) (evalExpr_var_hit _ _ _ (envExtend_hit _ _ _))
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2, hret]
      simp [addCallerFwd, h1, h2, i32_map_ok]

/-- `emit_correct` for `sum_caller`: program evaluation over `[sumFunc]`
    agrees with the delegating forward (fuel must cover `n`). -/
theorem evalProgFunc_sumCaller (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    evalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] =
      sumCallerFwd l nv := by
  have hbind : bindArgs sumCallerFunc.args [.arr32 l, .u32 nv] =
      some [("a", .arr32 l), ("n", .u32 nv)] := rfl
  have hbody : sumCallerFunc.body =
      .seq (.callRet "s" "sum_array" ["a", "n"])
           (.return_ (.var "s")) := rfl
  have ha := envLookup_sumCaller_a l nv
  have hn := envLookup_sumCaller_n l nv
  have hfind : findFunc [sumFunc] "sum_array" = some sumFunc :=
    findFunc_hit sumFunc []
  have hargs : lookupArgs [("a", .arr32 l), ("n", .u32 nv)] ["a", "n"] =
      some [.arr32 l, .u32 nv] := by
    simp [lookupArgs, ha, hn]
  have hcall := evalFuncFuel_sum F l nv hle h32 hF
  cases hsum : sumFwd l nv with
  | error e =>
    have hcall' : evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .error e := by
      rw [hcall, hsum]
    have hstep := evalProgStmt_callRet_err [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      [.arr32 l, .u32 nv] sumFunc e hargs hfind hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep]
    simp [sumCallerFwd, hsum]
  | ok v =>
    have hcall' : evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .ok v := by
      rw [hcall, hsum]
    have hstep := evalProgStmt_callRet_ok [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      [.arr32 l, .u32 nv] sumFunc v hargs hfind hcall'
    have hret : evalProgStmt [sumFunc] F (.return_ (.var "s"))
        (envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v) =
        .ok (envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v,
          .returned v) :=
      evalProgStmt_return [sumFunc] F (.var "s") _
        v (evalExpr_var_hit _ _ _ (envExtend_hit _ _ _))
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep, hret]
    simp [sumCallerFwd, hsum]

/-! ## S2: struct-by-value (`translate`) -/

/-- Canonical CoreIR for `tests/c/struct_by_value.c`: project both
    fields, checked-add the deltas, build the result `Point`
    (field-wise update functionalized; `cir.get_member` + `cir.load`
    fused into `fget`, stores + return fused into `pmk`). -/
def translateFunc : Func :=
  ⟨"translate",
   [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
    { name := "dx", ty := .i 32, role := .owned },
    { name := "dy", ty := .i 32, role := .owned }],
   .struct "Point" [.i 32, .i 32],
   .seq (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
   (.seq (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
         (.return_ (.pmk (.var "qx") (.var "qy"))))⟩

theorem matchFrag_translate : matchFrag translateFunc = some .translate := rfl

/-- Value-level forward for `translate`: field-wise checked addition
    (cf. rendered `translate_fwd`, which delegates to `pointTranslate`). -/
def translateFwd (px py dx dy : BitVec 32) : Result Value :=
  match checkedAddI32 px dx, checkedAddI32 py dy with
  | .ok x', .ok y' => .ok (.structVal "Point" [("x", x'), ("y", y')])
  | .error e, _ => .error e
  | _, .error e => .error e

/-- Bridge: forward ok-path equals `pointTranslate` ok-path. -/
theorem translateFwd_ok_bridge (px py dx dy x' y' : BitVec 32)
    (hx : checkedAddI32 px dx = .ok x')
    (hy : checkedAddI32 py dy = .ok y') :
    translateFwd px py dx dy =
      .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
  simp [translateFwd, hx, hy]

theorem translateFwd_err_x (px py dx dy : BitVec 32) (e : Panic)
    (hx : checkedAddI32 px dx = .error e) :
    translateFwd px py dx dy = .error e := by
  simp [translateFwd, hx]

theorem translateFwd_err_y (px py dx dy : BitVec 32) (x' : BitVec 32)
    (e : Panic)
    (hx : checkedAddI32 px dx = .ok x')
    (hy : checkedAddI32 py dy = .error e) :
    translateFwd px py dx dy = .error e := by
  simp [translateFwd, hx, hy]

/-- Env facts for the `translate` shape. -/
theorem envLookup_translate_p (px py dx dy : BitVec 32) :
    envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "p" =
      some (.structVal "Point" [("x", px), ("y", py)]) := by
  simp [envLookup]

theorem envLookup_translate_dx (px py dx dy : BitVec 32) :
    envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dx" = some (.i32 dx) := by
  simp [envLookup, show ("dx" : String) ≠ "p" by decide]

theorem envLookup_translate_dy (px py dx dy : BitVec 32) :
    envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dy" = some (.i32 dy) := by
  simp [envLookup, show ("dy" : String) ≠ "p" by decide,
    show ("dy" : String) ≠ "dx" by decide]

/-- Field facts for the bound `Point` value. -/
theorem fieldLookup_translate_x (px py : BitVec 32) :
    fieldLookup [("x", px), ("y", py)] "x" = some px :=
  fieldLookup_hit "x" px _

theorem fieldLookup_translate_y (px py : BitVec 32) :
    fieldLookup [("x", px), ("y", py)] "y" = some py := by
  rw [fieldLookup_miss "x" "y" px _ (by decide)]
  exact fieldLookup_hit "y" py _

/-- `emit_correct` for `translate`: evaluation agrees with the forward
    on all inputs (ok and both error paths). Loop-free body, so every
    fuel agrees. -/
theorem evalFuncFuel_translate (F : Nat) (px py dx dy : BitVec 32) :
    evalFuncFuel F translateFunc
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
      translateFwd px py dx dy := by
  have hbind : bindArgs translateFunc.args
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
      some [("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)] := rfl
  have hbody : translateFunc.body =
      .seq (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
      (.seq (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
            (.return_ (.pmk (.var "qx") (.var "qy")))) := rfl
  have hp := envLookup_translate_p px py dx dy
  have hdx := envLookup_translate_dx px py dx dy
  have hdy := envLookup_translate_dy px py dx dy
  have hfx : fieldLookup [("x", px), ("y", py)] "x" = some px :=
    fieldLookup_translate_x px py
  have hfy : fieldLookup [("x", px), ("y", py)] "y" = some py :=
    fieldLookup_translate_y px py
  have haddx : evalExpr (.add (.fget "p" "x") (.var "dx"))
      [("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)] =
      (checkedAddI32 px dx).map .i32 :=
    evalExpr_add_fget_var _ _ _ _ _ _ _ _ hp hfx hdx
  cases hx : checkedAddI32 px dx with
  | error e =>
    have haddx' : evalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] = .error e := by
      rw [haddx, hx]
      exact i32_map_error e
    have hlet : evalStmtFuel F
        (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] = .error e := by
      cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddx']
    simp only [evalFuncFuel, hbind, hbody]
    rw [evalStmtFuel_seq_err _ _ _ _ _ hlet]
    simp [translateFwd, hx]
  | ok x' =>
    have haddx' : evalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] = .ok (.i32 x') := by
      rw [haddx, hx]
      exact i32_map_ok x'
    have hletx : evalStmtFuel F
        (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] =
        .ok (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x'),
          .fellThrough) := by
      cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddx']
    have hobj2 : envLookup (envExtend [("p", .structVal "Point"
        [("x", px), ("y", py)]), ("dx", .i32 dx), ("dy", .i32 dy)]
        "qx" (.i32 x')) "p" =
        some (.structVal "Point" [("x", px), ("y", py)]) := by
      simp [envExtend, envLookup, show ("p" : String) ≠ "qx" by decide]
    have hvar2 : envLookup (envExtend [("p", .structVal "Point"
        [("x", px), ("y", py)]), ("dx", .i32 dx), ("dy", .i32 dy)]
        "qx" (.i32 x')) "dy" = some (.i32 dy) := by
      simp [envExtend, envLookup, show ("dy" : String) ≠ "qx" by decide]
    have haddy : evalExpr (.add (.fget "p" "y") (.var "dy"))
        (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
        (checkedAddI32 py dy).map .i32 :=
      evalExpr_add_fget_var _ _ _ _ _ _ _ _ hobj2 hfy hvar2
    cases hy : checkedAddI32 py dy with
    | error e =>
      have haddy' : evalExpr (.add (.fget "p" "y") (.var "dy"))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .error e := by
        rw [haddy, hy]
        exact i32_map_error e
      have hlety : evalStmtFuel F
          (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .error e := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddy']
      simp only [evalFuncFuel, hbind, hbody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hletx,
        evalStmtFuel_seq_err _ _ _ _ _ hlety]
      simp [translateFwd, hx, hy]
    | ok y' =>
      have haddy' : evalExpr (.add (.fget "p" "y") (.var "dy"))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .ok (.i32 y') := by
        rw [haddy, hy]
        exact i32_map_ok y'
      have hlety : evalStmtFuel F
          (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .ok (envExtend (envExtend [("p", .structVal "Point"
            [("x", px), ("y", py)]), ("dx", .i32 dx), ("dy", .i32 dy)]
            "qx" (.i32 x')) "qy" (.i32 y'), .fellThrough) := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddy']
      have hqx : evalExpr (.var "qx")
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (.i32 x') :=
        evalExpr_var_hit _ _ _
          (by simp [envExtend, envLookup,
            show ("qx" : String) ≠ "qy" by decide])
      have hqy : evalExpr (.var "qy")
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (.i32 y') :=
        evalExpr_var_hit _ _ _ (envExtend_hit _ _ _)
      have hmk : evalExpr (.pmk (.var "qx") (.var "qy"))
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) :=
        evalExpr_pmk_ok _ _ _ _ _ hqx hqy
      have hret : evalStmtFuel F
          (.return_ (.pmk (.var "qx") (.var "qy")))
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y'),
            .returned (.structVal "Point" [("x", x'), ("y", y')])) :=
        evalStmtFuel_return _ _ _ _ hmk
      simp only [evalFuncFuel, hbind, hbody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hletx,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ hlety, hret]
      simp [translateFwd, hx, hy]

/-! ## S3a: control-flow hardening (nested loops, break/continue,
early return, switch-as-if-chain) -/

/-! ### Word bridges for the new ops -/

/-- `umul` on `ofNat` words is `ofNat` of the product (wrapping
    unsigned multiplication; cf. `ofNat32_add_one`). -/
theorem ofNat32_mul (k j : Nat) :
    BitVec.ofNat 32 k * BitVec.ofNat 32 j = BitVec.ofNat 32 (k * j) :=
  (BitVec.ofNat_mul (n := 32) k j).symm

/-- `ofNat` is injective below `2^32` (for `ueq` condition reasoning). -/
theorem ofNat32_inj (k c : Nat) (hk : k < 2 ^ 32) (hc : c < 2 ^ 32)
    (h : BitVec.ofNat 32 k = BitVec.ofNat 32 c) : k = c := by
  have hcongr := congrArg BitVec.toNat h
  rw [ofNat32_toNat k hk, ofNat32_toNat c hc] at hcongr
  exact hcongr

/-- Word `==` on `ofNat` values decides `Nat` equality (below `2^32`). -/
theorem ofNat32_beq (k c : Nat) (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 k == BitVec.ofNat 32 c) = decide (k = c) := by
  by_cases h : k = c
  · subst h; simp
  · have hne : BitVec.ofNat 32 k ≠ BitVec.ofNat 32 c :=
      fun heq => h (ofNat32_inj k c hk hc heq)
    simp [h, hne]

/-! ### `nested_sum`: nested bounded `u32` loops -/

/-- Suffix row sum: `Σ_{j∈[t,m)} ofNat (i*j)` (inner-loop invariant). -/
def rowSuffixU32 (i t m : Nat) : BitVec 32 :=
  (((List.range' t (m - t)).map (fun j => BitVec.ofNat 32 (i * j)))).sum

/-- Suffix nest sum: `Σ_{i∈[k,n)} rowU32 i m` (outer-loop invariant). -/
def nestSuffixU32 (k n m : Nat) : BitVec 32 :=
  (((List.range' k (n - k)).map (fun i => rowU32 i m))).sum

/-- Inner step: peeling `t < m` exposes the head product. -/
theorem rowSuffix_step (i t m : Nat) (h : t < m) :
    rowSuffixU32 i t m =
      BitVec.ofNat 32 (i * t) + rowSuffixU32 i (t + 1) m := by
  have hsub : m - t = (m - (t + 1)) + 1 := by omega
  simp [rowSuffixU32, hsub, List.range'_succ, List.map_cons, List.sum_cons,
    BitVec.add_comm (BitVec.ofNat 32 (i * t)) _]

/-- Inner exit: empty suffix sums to zero. -/
theorem rowSuffix_nil (i t : Nat) :
    rowSuffixU32 i t t = 0 := by
  simp [rowSuffixU32]

/-- Full row is the suffix from zero. -/
theorem rowSuffix_full (i m : Nat) :
    rowSuffixU32 i 0 m = rowU32 i m := by
  simp [rowSuffixU32, rowU32, List.range_eq_range']

/-- Outer step: peeling `k < n` exposes the head row. -/
theorem nestSuffix_step (k n m : Nat) (h : k < n) :
    nestSuffixU32 k n m = rowU32 k m + nestSuffixU32 (k + 1) n m := by
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  simp [nestSuffixU32, hsub, List.range'_succ, List.map_cons, List.sum_cons,
    BitVec.add_comm (rowU32 k m) _]

/-- Outer exit: empty suffix sums to zero. -/
theorem nestSuffix_nil (k n m : Nat) (h : n ≤ k) :
    nestSuffixU32 k n m = 0 := by
  have hsub : n - k = 0 := by omega
  simp [nestSuffixU32, hsub]

/-- Full nest is the suffix from zero. -/
theorem nestSuffix_full (n m : Nat) :
    nestSuffixU32 0 n m = nestedSumU32 n m := by
  simp [nestSuffixU32, nestedSumU32, List.range_eq_range']

/-- Inner body: `s = s + i*j; j = j+1` (wrapping `u32`). -/
def nestedBodyInner : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.umul (.var "i") (.var "j"))))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 (BitVec.ofNat 32 1)))))

/-- Inner loop: `while (j < m) { ... }`. -/
def nestedInner : CStmt :=
  .while_ (.ult (.var "j") (.var "m")) nestedBodyInner

/-- Outer body: run the inner loop, step `i`, reset `j` to `0`.
    The reset comes last so the outer-loop-head invariant (`j = 0`)
    holds every iteration (first iteration from the initial `let`). -/
def nestedBodyOuter : CStmt :=
  .seq nestedInner (.seq (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))) (.assign "j" (.lit (.u32 (BitVec.ofNat 32 0)))))

/-- Outer loop: `while (i < n) { ... }`. -/
def nestedOuter : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) nestedBodyOuter

/-- Canonical CoreIR for `tests/c/nested_sum.c`. Both bounds are plain
    `u32` values (no array: no `OOB`; fuel exhaustion past `EVAL_FUEL`
    is `AssertFail`, discharged by the `hF` side condition). -/
def nestedFunc : Func :=
  ⟨"nested_sum",
   [{ name := "n", ty := .u 32, role := .owned },
    { name := "m", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "j" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq nestedOuter
         (.return_ (.var "s")))))⟩

/-- Value-level forward for `nested_sum` (cf. rendered `nested_sum_fwd`,
    which references `Base.nestedSumU32`). -/
def nestedFwd (n m : BitVec 32) : Result Value :=
  .ok (.u32 (nestedSumU32 n.toNat m.toNat))

/-- Loop environments: outer index `k`, accumulator, inner index `t`,
    bounds fixed. -/
def mkNestedEnv (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) : Env :=
  [("j", .u32 (BitVec.ofNat 32 t)), ("i", .u32 (BitVec.ofNat 32 k)),
   ("s", .u32 acc), ("n", .u32 nv), ("m", .u32 mv)]

theorem mkNestedEnv_j (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "j" =
      some (.u32 (BitVec.ofNat 32 t)) := by
  simp [mkNestedEnv, envLookup]

theorem mkNestedEnv_i (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkNestedEnv, envLookup, show ("i" : String) ≠ "j" by decide]

theorem mkNestedEnv_s (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "s" = some (.u32 acc) := by
  simp [mkNestedEnv, envLookup, show ("s" : String) ≠ "j" by decide,
    show ("s" : String) ≠ "i" by decide]

theorem mkNestedEnv_n (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "n" = some (.u32 nv) := by
  simp [mkNestedEnv, envLookup, show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide]

theorem mkNestedEnv_m (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "m" = some (.u32 mv) := by
  simp [mkNestedEnv, envLookup, show ("m" : String) ≠ "j" by decide,
    show ("m" : String) ≠ "i" by decide,
    show ("m" : String) ≠ "s" by decide,
    show ("m" : String) ≠ "n" by decide]

/-- Updating `s` stays in the env family. -/
theorem nestedEnv_update_s (nv mv : BitVec 32) (k t : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkNestedEnv nv mv k acc t) "s" (.u32 v) =
      some (mkNestedEnv nv mv k v t) := by
  simp [mkNestedEnv, envUpdate, show ("s" : String) ≠ "j" by decide,
    show ("s" : String) ≠ "i" by decide]

/-- Updating `j` stays in the env family. -/
theorem nestedEnv_update_j (nv mv : BitVec 32) (k t t' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkNestedEnv nv mv k acc t) "j"
        (.u32 (BitVec.ofNat 32 t')) =
      some (mkNestedEnv nv mv k acc t') := by
  simp [mkNestedEnv, envUpdate]

/-- Updating `i` stays in the env family. -/
theorem nestedEnv_update_i (nv mv : BitVec 32) (k k' t : Nat)
    (acc : BitVec 32) :
    envUpdate (mkNestedEnv nv mv k acc t) "i"
        (.u32 (BitVec.ofNat 32 k')) =
      some (mkNestedEnv nv mv k' acc t) := by
  simp [mkNestedEnv, envUpdate, show ("i" : String) ≠ "j" by decide]

/-- Inner condition reads `j` against `m`. -/
theorem nestedCondInner_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (h : t < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "m")) (mkNestedEnv nv mv k acc t) =
      .ok (.b (decide (t < mv.toNat))) := by
  have hj := mkNestedEnv_j nv mv k acc t
  have hm := mkNestedEnv_m nv mv k acc t
  simp [evalExpr, hj, hm, ofNat32_ult t mv h]

/-- Outer condition reads `i` against `n`. -/
theorem nestedCondOuter_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkNestedEnv nv mv k acc t) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkNestedEnv_i nv mv k acc t
  have hn := mkNestedEnv_n nv mv k acc t
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- One inner step advances `j` and accumulates `ofNat (k*t)` (any fuel:
    loop-free). -/
theorem nestedBodyInner_eval (F : Nat) (nv mv : BitVec 32)
    (k t : Nat) (acc : BitVec 32) :
    evalStmtFuel F nestedBodyInner (mkNestedEnv nv mv k acc t) =
      .ok (mkNestedEnv nv mv k
        (acc + BitVec.ofNat 32 (k * t)) (t + 1), .fellThrough) := by
  have hs : evalExpr (.uadd (.var "s") (.umul (.var "i") (.var "j")))
        (mkNestedEnv nv mv k acc t) =
        .ok (.u32 (acc + BitVec.ofNat 32 (k * t))) := by
    have h1 := mkNestedEnv_s nv mv k acc t
    have hii := mkNestedEnv_i nv mv k acc t
    have hj := mkNestedEnv_j nv mv k acc t
    simp only [evalExpr, h1, hii, hj, ofNat32_mul]
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) t) =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    have hj := mkNestedEnv_j nv mv k (acc + BitVec.ofNat 32 (k * t)) t
    simp only [evalExpr, litVal, hj, ofNat32_add_one]
  have up1 := nestedEnv_update_s nv mv k t acc
    (acc + BitVec.ofNat 32 (k * t))
  have up2 := nestedEnv_update_j nv mv k t (t + 1)
    (acc + BitVec.ofNat 32 (k * t))
  cases F <;>
    simp [nestedBodyInner, evalStmtFuel, evalStmtZero, evalStmtWith,
      hs, hj2, up1, up2]

/-- Inner loop correctness: folds the row suffix (fuel-generalized). -/
theorem nestedInner_correct (nv mv : BitVec 32)
    (F k t : Nat) (acc : BitVec 32)
    (ht32 : t ≤ mv.toNat) (ht2 : t < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : mv.toNat - t ≤ F) :
    evalStmtFuel F nestedInner (mkNestedEnv nv mv k acc t) =
      .ok (mkNestedEnv nv mv k
        (acc + rowSuffixU32 k t mv.toNat) mv.toNat, .fellThrough) := by
  induction F generalizing t acc with
  | zero =>
    have htt : t = mv.toNat := by omega
    subst htt
    have hcond : evalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc mv.toNat) = .ok (.b false) := by
      simpa using
        (nestedCondInner_eval nv mv k mv.toNat acc (by omega : mv.toNat < 2 ^ 32))
    have hnil := rowSuffix_nil k mv.toNat
    simp [nestedInner, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcond, hnil, BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : t < mv.toNat
    · have hcond : evalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc t) = .ok (.b true) := by
        simpa [hlt] using (nestedCondInner_eval nv mv k t acc ht2)
      have hbody := nestedBodyInner_eval F nv mv k t acc
      have hstep : evalStmtFuel (F + 1) nestedInner
            (mkNestedEnv nv mv k acc t)
          = evalStmtFuel F nestedInner
            (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) (t + 1)) := by
        simp [nestedInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hrec := ih (t + 1) (acc + BitVec.ofNat 32 (k * t))
        (by omega) (by omega) (by omega)
      rw [hrec]
      have hrow := rowSuffix_step k t mv.toNat hlt
      have hacc : (acc + BitVec.ofNat 32 (k * t)) +
            rowSuffixU32 k (t + 1) mv.toNat
          = acc + rowSuffixU32 k t mv.toNat := by
        rw [hrow]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have htt : t = mv.toNat := by omega
      subst htt
      have hcond : evalExpr (.ult (.var "j") (.var "m"))
            (mkNestedEnv nv mv k acc mv.toNat) = .ok (.b false) := by
        simpa using
          (nestedCondInner_eval nv mv k mv.toNat acc (by omega : mv.toNat < 2 ^ 32))
      have hnil := rowSuffix_nil k mv.toNat
      simp [nestedInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil, BitVec.add_zero]

/-- Outer body evaluation: run the inner loop, step `i`, reset `j`.
    Needs `m ≤ F` so the inner loop has fuel (the three steps are
    handler-independent, so one inner fact covers all fuels via
    `cases`, ascribed to the unfolded handler form in the `succ`
    branch). -/
theorem nestedBodyOuter_eval (F : Nat) (nv mv : BitVec 32)
    (k : Nat) (acc : BitVec 32)
    (hmF : mv.toNat ≤ F)
    (hm32 : mv.toNat < 2 ^ 32) :
    evalStmtFuel F nestedBodyOuter (mkNestedEnv nv mv k acc 0) =
      .ok (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0,
        .fellThrough) := by
  have hinner : evalStmtFuel F nestedInner (mkNestedEnv nv mv k acc 0) =
        .ok (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
          .fellThrough) := by
    have h := nestedInner_correct nv mv F k 0 acc
      (Nat.zero_le _) (by omega) hm32 (by omega)
    rwa [rowSuffix_full] at h
  have hincr : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have hii := mkNestedEnv_i nv mv k (acc + rowU32 k mv.toNat) mv.toNat
    simp only [evalExpr, litVal, hii, ofNat32_add_one]
  have up1 := nestedEnv_update_i nv mv k (k + 1) mv.toNat
    (acc + rowU32 k mv.toNat)
  have hreset : evalExpr (.lit (.u32 (BitVec.ofNat 32 0)))
        (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) mv.toNat) =
        .ok (.u32 (BitVec.ofNat 32 0)) := rfl
  have up0 := nestedEnv_update_j nv mv (k + 1) mv.toNat 0
    (acc + rowU32 k mv.toNat)
  cases F with
  | zero =>
    have hinner0 : evalStmtWith evalStmtZeroHandler
          nestedInner (mkNestedEnv nv mv k acc 0) =
          .ok (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            .fellThrough) := hinner
    simp [nestedBodyOuter, evalStmtFuel, evalStmtZero, evalStmtWith,
      hinner0, hincr, up1, hreset, up0]
  | succ F =>
    have hinnerS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          nestedInner (mkNestedEnv nv mv k acc 0) =
          .ok (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            .fellThrough) := hinner
    simp [nestedBodyOuter, evalStmtFuel, evalStmtWith,
      hinnerS, hincr, up1, hreset, up0]

/-- Outer loop correctness: folds the nest suffix (fuel-generalized;
    one outer iteration costs `m+1` fuel units). -/
theorem nestedOuter_correct (nv mv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ nv.toNat) (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : (nv.toNat - k) * (mv.toNat + 1) ≤ F) :
    evalStmtFuel F nestedOuter (mkNestedEnv nv mv k acc 0) =
      .ok (mkNestedEnv nv mv nv.toNat
        (acc + nestSuffixU32 k nv.toNat mv.toNat) 0, .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by
      have hpos : 0 < nv.toNat - k ∨ k = nv.toNat := by omega
      rcases hpos with hpos | hkk
      · have hge := Nat.le_mul_of_pos_left (mv.toNat + 1) hpos
        omega
      · exact hkk
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkNestedEnv nv mv nv.toNat acc 0) = .ok (.b false) := by
      simpa using (nestedCondOuter_eval nv mv nv.toNat 0 acc hn)
    have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
    simp [nestedOuter, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcond, hnil, BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv k acc 0) = .ok (.b true) := by
        simpa [hlt] using (nestedCondOuter_eval nv mv k 0 acc hk32)
      have hbody := nestedBodyOuter_eval F nv mv k acc
        (by have hge := Nat.le_mul_of_pos_left (mv.toNat + 1)
              (show 0 < nv.toNat - k by omega)
            omega)
        hm
      have hstep : evalStmtFuel (F + 1) nestedOuter
            (mkNestedEnv nv mv k acc 0)
          = evalStmtFuel F nestedOuter
            (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0) := by
        simp [nestedOuter, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hsplit : (nv.toNat - k) * (mv.toNat + 1)
          = (nv.toNat - (k + 1)) * (mv.toNat + 1) + (mv.toNat + 1) := by
        have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
        rw [hkk1, Nat.add_mul, Nat.one_mul]
      have hrec := ih (k + 1) (acc + rowU32 k mv.toNat)
        (by omega)
        (show (nv.toNat - (k + 1)) * (mv.toNat + 1) ≤ F by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hnest := nestSuffix_step k nv.toNat mv.toNat hlt
      have hacc : (acc + rowU32 k mv.toNat) +
            nestSuffixU32 (k + 1) nv.toNat mv.toNat
          = acc + nestSuffixU32 k nv.toNat mv.toNat := by
        rw [hnest]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv nv.toNat acc 0) = .ok (.b false) := by
        simpa using (nestedCondOuter_eval nv mv nv.toNat 0 acc hn)
      have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
      simp [nestedOuter, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil, BitVec.add_zero]

/-- `emit_correct` for `nested_sum`, fuel-generalized. -/
theorem evalFuncFuel_nested (F : Nat) (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : nv.toNat * (mv.toNat + 1) ≤ F) :
    evalFuncFuel F nestedFunc [.u32 nv, .u32 mv] = nestedFwd nv mv := by
  have hbind : bindArgs nestedFunc.args [.u32 nv, .u32 mv] =
      some [("n", .u32 nv), ("m", .u32 mv)] := rfl
  have hbody : nestedFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "j" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq nestedOuter
            (.return_ (.var "s"))))) := rfl
  -- Stated with `ofNat`-headed zeros (simp's simprocs normalize `0` to
  -- `0#32`, so `OfNat`-headed forms would not match after normalization).
  have henv : [("j", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv), ("m", .u32 mv)]
      = mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0 := rfl
  have hfull := nestSuffix_full nv.toNat mv.toNat
  have hsret : envLookup
        (mkNestedEnv nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0)
        "s" = some (.u32 (nestedSumU32 nv.toNat mv.toNat)) :=
    mkNestedEnv_s nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
        = .ok (mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            .fellThrough) :=
      nestedOuter_correct nv mv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _)
        hn hm (by omega)
    simp [evalFuncFuel, nestedFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, nestedFwd, henv, hloopH0,
      hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
        = .ok (mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            .fellThrough) :=
      nestedOuter_correct nv mv (F + 1) 0 (BitVec.ofNat 32 0)
        (Nat.zero_le _) hn hm (by omega)
    simp [evalFuncFuel, nestedFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, nestedFwd, henv, hloopS, hsret, hfull,
      BitVec.zero_add]

/-- `emit_correct` for `nested_sum` at the default fuel. -/
theorem emit_correct_nested (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hfuel : nv.toNat * (mv.toNat + 1) ≤ EVAL_FUEL) :
    evalFunc nestedFunc [.u32 nv, .u32 mv] = nestedFwd nv mv :=
  evalFuncFuel_nested EVAL_FUEL nv mv hn hm hfuel

theorem matchFrag_nested : matchFrag nestedFunc = some .nested := rfl

/-! ### `skip_sum`: break/continue in a bounded `u32` loop -/

/-- Suffix sum: `Σ` of `i ∈ [t,e)`, skipping `2` (loop invariant;
    `e` is always `min n 8`: `break` at `8` caps the range,
    `continue` filters `2`). -/
def skipSuffixU32 (t e : Nat) : BitVec 32 :=
  ((((List.range' t (e - t)).filter (fun i => i != 2)).map
    (fun i => BitVec.ofNat 32 i))).sum

/-- Step: peeling `t < e`, `t ≠ 2` exposes the head summand. -/
theorem skipSuffix_step (t e : Nat) (hlt : t < e) (hne : t ≠ 2) :
    skipSuffixU32 t e =
      BitVec.ofNat 32 t + skipSuffixU32 (t + 1) e := by
  have hsub : e - t = (e - (t + 1)) + 1 := by omega
  have hkeep : (t != 2) = true := by simp [hne]
  simp [skipSuffixU32, hsub, List.range'_succ, hkeep,
    BitVec.add_comm (BitVec.ofNat 32 t) _]

/-- `continue` at `2` drops it: suffixes from `2` and `3` agree. -/
theorem skipSuffix_skip2 (e : Nat) (h : 2 < e) :
    skipSuffixU32 2 e = skipSuffixU32 3 e := by
  have hsub : e - 2 = (e - 3) + 1 := by omega
  have hdrop : ((2 != 2)) = false := by simp
  simp [skipSuffixU32, hsub, List.range'_succ]

/-- Empty suffix sums to zero. -/
theorem skipSuffix_nil (t e : Nat) (h : e ≤ t) :
    skipSuffixU32 t e = 0 := by
  have hsub : e - t = 0 := by omega
  simp [skipSuffixU32, hsub]

/-- Full suffix is the rendered forward reference. -/
theorem skipSuffix_full (n : Nat) :
    skipSuffixU32 0 (min n 8) = skipSumU32 n := by
  simp [skipSuffixU32, skipSumU32, List.range_eq_range']

/-- `continue` branch: `i = i+1` then signal (mirrors the `cir.for`
    step region, which runs on `continue`). -/
def skipContBranch : CStmt :=
  .seq (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1)))))
    .continue_

/-- Fall-through tail: `s = s+i; i = i+1`. -/
def skipTail : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.var "i")))
    (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1)))))

/-- Loop body: skip `2`, break at `8`, else accumulate. -/
def skipBody : CStmt :=
  .seq (.if_ (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        skipContBranch .skip)
    (.seq (.if_ (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
            .break_ .skip)
          skipTail)

/-- Loop: `while (i < n) { ... }`. -/
def skipWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) skipBody

/-- Canonical CoreIR for `tests/c/skip_sum.c`. `break` caps iterations
    at `9`, so the default-fuel correctness is unconditional (the
    fuel side condition discharges by `omega` over `min n 8`). -/
def skipFunc : Func :=
  ⟨"skip_sum",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq skipWhile
         (.return_ (.var "s"))))⟩

/-- Value-level forward for `skip_sum` (cf. rendered `skip_sum_fwd`,
    which references `Base.skipSumU32`). -/
def skipFwd (n : BitVec 32) : Result Value :=
  .ok (.u32 (skipSumU32 n.toNat))

/-- Loop environments: index `k` and accumulator, bound fixed. -/
def mkSkipEnv (nv : BitVec 32) (k : Nat) (acc : BitVec 32) : Env :=
  [("i", .u32 (BitVec.ofNat 32 k)), ("s", .u32 acc), ("n", .u32 nv)]

theorem mkSkipEnv_i (nv : BitVec 32) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSkipEnv nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkSkipEnv, envLookup]

theorem mkSkipEnv_s (nv : BitVec 32) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSkipEnv nv k acc) "s" = some (.u32 acc) := by
  simp [mkSkipEnv, envLookup, show ("s" : String) ≠ "i" by decide]

theorem mkSkipEnv_n (nv : BitVec 32) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSkipEnv nv k acc) "n" = some (.u32 nv) := by
  simp [mkSkipEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide]

/-- Updating `s` stays in the env family. -/
theorem skipEnv_update_s (nv : BitVec 32) (k : Nat) (acc v : BitVec 32) :
    envUpdate (mkSkipEnv nv k acc) "s" (.u32 v) =
      some (mkSkipEnv nv k v) := by
  simp [mkSkipEnv, envUpdate, show ("s" : String) ≠ "i" by decide]

/-- Updating `i` stays in the env family. -/
theorem skipEnv_update_i (nv : BitVec 32) (k k' : Nat) (acc : BitVec 32) :
    envUpdate (mkSkipEnv nv k acc) "i" (.u32 (BitVec.ofNat 32 k')) =
      some (mkSkipEnv nv k' acc) := by
  simp [mkSkipEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem skipCond_eval (nv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkSkipEnv nv k acc) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSkipEnv_i nv k acc
  have hn := mkSkipEnv_n nv k acc
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- `ueq` against a const decides `Nat` equality (index below `2^32`). -/
theorem skipCond_eq (nv : BitVec 32) (k c : Nat) (acc : BitVec 32)
    (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) :
    evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 c))))
      (mkSkipEnv nv k acc) = .ok (.b (decide (k = c))) := by
  have hi := mkSkipEnv_i nv k acc
  simp [evalExpr, hi, litVal, ofNat32_beq k c hk hc]

/-- Body at `k = 2`: increment, signal `continued` (any fuel). -/
theorem skipBody_continue (F : Nat) (nv : BitVec 32) (acc : BitVec 32) :
    evalStmtFuel F skipBody (mkSkipEnv nv 2 acc) =
      .ok (mkSkipEnv nv 3 acc, .continued) := by
  have hcond1 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 2 acc) = .ok (.b true) := by
    simpa using (skipCond_eq nv 2 2 acc (by decide) (by decide))
  have hincr : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv 2 acc) = .ok (.u32 (BitVec.ofNat 32 3)) := by
    have hi := mkSkipEnv_i nv 2 acc
    have h3 : BitVec.ofNat 32 2 + BitVec.ofNat 32 1
        = BitVec.ofNat 32 3 :=
      ofNat32_add_one 2
    simp only [evalExpr, litVal, hi, h3]
  have upi := skipEnv_update_i nv 2 3 acc
  cases F <;>
    simp [skipBody, skipContBranch, evalStmtFuel, evalStmtZero, evalStmtWith,
      hcond1, hincr, upi]

/-- Body at `k = 8`: signal `broke`, env untouched (any fuel). -/
theorem skipBody_break (F : Nat) (nv : BitVec 32) (acc : BitVec 32) :
    evalStmtFuel F skipBody (mkSkipEnv nv 8 acc) =
      .ok (mkSkipEnv nv 8 acc, .broke) := by
  have hcond1 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 8 acc) = .ok (.b false) := by
    have h := skipCond_eq nv 8 2 acc (by decide) (by decide)
    simpa using h
  have hcond2 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv 8 acc) = .ok (.b true) := by
    simpa using (skipCond_eq nv 8 8 acc (by decide) (by decide))
  cases F <;>
    simp [skipBody, evalStmtFuel, evalStmtZero, evalStmtWith, hcond1, hcond2]

/-- Body elsewhere: accumulate and step (any fuel). -/
theorem skipBody_step (F : Nat) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32)
    (hne2 : k ≠ 2) (hne8 : k ≠ 8) (hk32 : k < 2 ^ 32) :
    evalStmtFuel F skipBody (mkSkipEnv nv k acc) =
      .ok (mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k),
        .fellThrough) := by
  have hcond1 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv k acc) = .ok (.b false) := by
    have h := skipCond_eq nv k 2 acc hk32 (by decide)
    simpa [hne2] using h
  have hcond2 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv k acc) = .ok (.b false) := by
    have h := skipCond_eq nv k 8 acc hk32 (by decide)
    simpa [hne8] using h
  have hs : evalExpr (.uadd (.var "s") (.var "i"))
        (mkSkipEnv nv k acc) = .ok (.u32 (acc + BitVec.ofNat 32 k)) := by
    have h1 := mkSkipEnv_s nv k acc
    have hii := mkSkipEnv_i nv k acc
    simp only [evalExpr, h1, hii]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv k (acc + BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSkipEnv_i nv k (acc + BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := skipEnv_update_s nv k acc (acc + BitVec.ofNat 32 k)
  have up2 := skipEnv_update_i nv k (k + 1) (acc + BitVec.ofNat 32 k)
  cases F <;>
    simp [skipBody, skipTail, evalStmtFuel, evalStmtZero, evalStmtWith,
      hcond1, hcond2, hs, hi2, up1, up2]

/-- Loop correctness: folds the skip suffix, exits with `i = min n 8`
    (fuel-generalized; the `+1` absorbs the final exit iteration, so
    the zero-fuel case is vacuous). -/
theorem skipWhile_correct (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ min nv.toNat 8)
    (hF : min nv.toNat 8 - k + 1 ≤ F) :
    evalStmtFuel F skipWhile (mkSkipEnv nv k acc) =
      .ok (mkSkipEnv nv (min nv.toNat 8)
        (acc + skipSuffixU32 k (min nv.toNat 8)), .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · by_cases h2 : k = 2
      · subst h2
        have hcond : evalExpr (.ult (.var "i") (.var "n"))
              (mkSkipEnv nv 2 acc) = .ok (.b true) := by
          have hk32 : (2 : Nat) < 2 ^ 32 := by decide
          simpa [hlt] using (skipCond_eval nv 2 acc hk32)
        have hbody := skipBody_continue F nv acc
        have hstep : evalStmtFuel (F + 1) skipWhile (mkSkipEnv nv 2 acc)
            = evalStmtFuel F skipWhile (mkSkipEnv nv 3 acc) := by
          simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep]
        have hrec := ih 3 acc (by omega) (by omega)
        rw [hrec]
        have hskip := skipSuffix_skip2 (min nv.toNat 8) (by omega)
        have hacc : acc + skipSuffixU32 3 (min nv.toNat 8)
            = acc + skipSuffixU32 2 (min nv.toNat 8) := by
          rw [hskip]
        rw [hacc]
      · by_cases h8 : k = 8
        · subst h8
          have he : min nv.toNat 8 = 8 := by omega
          have hcond : evalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv 8 acc) = .ok (.b true) := by
            have hk32 : (8 : Nat) < 2 ^ 32 := by decide
            simpa [hlt] using (skipCond_eval nv 8 acc hk32)
          have hbody := skipBody_break F nv acc
          have hnil8 := skipSuffix_nil 8 8 (Nat.le_refl 8)
          simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody, he, hnil8, BitVec.add_zero]
        · have hk32 : k < 2 ^ 32 := by omega
          have hcond : evalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv k acc) = .ok (.b true) := by
            simpa [hlt] using (skipCond_eval nv k acc hk32)
          have hbody := skipBody_step F nv k acc h2 h8 hk32
          have hstep : evalStmtFuel (F + 1) skipWhile (mkSkipEnv nv k acc)
              = evalStmtFuel F skipWhile
                (mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k)) := by
            simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
              hcond, hbody]
          rw [hstep]
          have hrec := ih (k + 1) (acc + BitVec.ofNat 32 k)
            (by omega) (by omega)
          rw [hrec]
          have hlt' : k < min nv.toNat 8 := by omega
          have hstep' := skipSuffix_step k (min nv.toNat 8) hlt' h2
          have hacc : (acc + BitVec.ofNat 32 k) +
                skipSuffixU32 (k + 1) (min nv.toNat 8)
              = acc + skipSuffixU32 k (min nv.toNat 8) := by
            rw [hstep']; exact BitVec.add_assoc _ _ _
          rw [hacc]
    · have hkk : k = min nv.toNat 8 := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkSkipEnv nv (min nv.toNat 8) acc) = .ok (.b false) := by
        have hfalse : (decide (min nv.toNat 8 < nv.toNat)) = false := by
          have : ¬ min nv.toNat 8 < nv.toNat := by omega
          simp [this]
        have hk32 : min nv.toNat 8 < 2 ^ 32 := by omega
        have h := skipCond_eval nv (min nv.toNat 8) acc hk32
        rwa [hfalse] at h
      have hnil := skipSuffix_nil (min nv.toNat 8) (min nv.toNat 8)
        (Nat.le_refl _)
      simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil, BitVec.add_zero]

/-- `emit_correct` for `skip_sum`, fuel-generalized. -/
theorem evalFuncFuel_skip (F : Nat) (nv : BitVec 32)
    (hF : min nv.toNat 8 + 1 ≤ F) :
    evalFuncFuel F skipFunc [.u32 nv] = skipFwd nv := by
  have hbind : bindArgs skipFunc.args [.u32 nv] =
      some [("n", .u32 nv)] := rfl
  have hbody : skipFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq skipWhile
            (.return_ (.var "s")))) := rfl
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv)]
      = mkSkipEnv nv 0 (BitVec.ofNat 32 0) := rfl
  have hfull := skipSuffix_full nv.toNat
  have hsret : envLookup
        (mkSkipEnv nv (min nv.toNat 8) (skipSumU32 nv.toNat)) "s" =
        some (.u32 (skipSumU32 nv.toNat)) :=
    mkSkipEnv_s nv (min nv.toNat 8) (skipSumU32 nv.toNat)
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            .fellThrough) :=
      skipWhile_correct nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) (by omega)
    simp [evalFuncFuel, skipFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, skipFwd, henv, hloopH0,
      hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            .fellThrough) :=
      skipWhile_correct nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _)
        (by omega)
    simp [evalFuncFuel, skipFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, skipFwd, henv, hloopS, hsret, hfull,
      BitVec.zero_add]

/-- `emit_correct` for `skip_sum` at the default fuel — unconditional:
    `break` caps iterations at `9 ≤ EVAL_FUEL`. -/
theorem emit_correct_skip (nv : BitVec 32) :
    evalFunc skipFunc [.u32 nv] = skipFwd nv := by
  apply evalFuncFuel_skip
  have h8 := Nat.min_le_right nv.toNat 8
  simp only [EVAL_FUEL] at h8 ⊢
  omega

theorem matchFrag_skip : matchFrag skipFunc = some .skip := rfl


/-! ### `find_eq`: early return inside a bounded loop -/

/-- `ofNat` round-trips `toNat` (for narrowing the found index back). -/
theorem ofNat32_toNat_inv (v : BitVec 32) :
    BitVec.ofNat 32 v.toNat = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.isLt

/-- First match of `k` in `l[j]?` over `j ∈ [t,e)` (loop invariant;
    `decide` predicate keeps `find?` simp-friendly). -/
def findSuffixU32 (l : List (BitVec 32)) (t e : Nat)
    (k : BitVec 32) : Option Nat :=
  ((List.range' t (e - t)).find? (fun j => decide (l[j]? = some k)))

/-- Hit at the head: the suffix finds `t` itself. -/
theorem findSuffix_hit (l : List (BitVec 32)) (t e : Nat)
    (k : BitVec 32) (x : BitVec 32)
    (hget : l[t]? = some x) (heq : x = k) (hlt : t < e) :
    findSuffixU32 l t e k = some t := by
  have hsub : e - t = (e - (t + 1)) + 1 := by omega
  have hpt : (fun j => decide (l[j]? = some k)) t = true := by
    simp [hget, heq]
  simp [findSuffixU32, hsub, List.range'_succ, hpt]

/-- Miss at the head: the suffix agrees with the tail. -/
theorem findSuffix_miss (l : List (BitVec 32)) (t e : Nat)
    (k : BitVec 32)
    (hmiss : ∀ x, l[t]? = some x → x ≠ k) (hlt : t < e) :
    findSuffixU32 l t e k = findSuffixU32 l (t + 1) e k := by
  have hsub : e - t = (e - (t + 1)) + 1 := by omega
  have hpt : (fun j => decide (l[j]? = some k)) t = false := by
    match ht : l[t]? with
    | some x =>
      have hne := hmiss x ht
      simp [ht, hne]
    | none => simp [ht]
  simp [findSuffixU32, hsub, List.range'_succ, hpt]

/-- Empty suffix finds nothing. -/
theorem findSuffix_nil (l : List (BitVec 32)) (t : Nat) (k : BitVec 32) :
    findSuffixU32 l t t k = none := by
  have hsub : t - t = 0 := Nat.sub_self _
  simp [findSuffixU32, hsub]

/-- Suffix from zero is the whole-prefix find (bridge to `findEqOut`). -/
theorem findSuffix_zero_idx (l : List (BitVec 32)) (n : Nat)
    (k : BitVec 32) :
    findSuffixU32 l 0 (min n l.length) k = findIdxU32 l n k := by
  simp [findSuffixU32, findIdxU32, Nat.sub_zero, List.range_eq_range']

/-- Loop body: return the index on match, else step. -/
def findBody : CStmt :=
  .seq (.if_ (.ueq (.idx "a" (.var "i")) (.var "k"))
        (.return_ (.var "i")) .skip)
       (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1)))))

/-- Loop: `while (i < n) { ... }`. -/
def findWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) findBody

/-- Canonical CoreIR for `tests/c/find_eq.c`. `a` is a `sharedBorrow`
    (pure list value); `n` is the 32-bit length (C `size_t` lengths must
    fit 32 bits — `validate` narrows them, runtime excess is `OOB`,
    exactly as in `sum`). -/
def findEqFunc : Func :=
  ⟨"find_eq",
   [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 32, role := .owned },
    { name := "k", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq findWhile
         (.return_ (.var "n")))⟩

/-- Value-level forward for `find_eq` (cf. rendered `find_eq_fwd`,
    which references `Base.findEqOut`). Stated by matching (not
    `Functor.map`) so `simp` closes goal sides syntactically. -/
def findEqFwd (l : List (BitVec 32)) (n k : BitVec 32) : Result Value :=
  match findEqOut l n.toNat k with
  | .ok w => .ok (.u32 w)
  | .error e => .error e

/-- Loop environments: index `t`, array and bound/needle fixed. -/
def mkFindEnv (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) : Env :=
  [("i", .u32 (BitVec.ofNat 32 t)), ("a", .arr32 l),
   ("n", .u32 nv), ("k", .u32 kv)]

theorem mkFindEnv_i (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "i" =
      some (.u32 (BitVec.ofNat 32 t)) := by
  simp [mkFindEnv, envLookup]

theorem mkFindEnv_a (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "a" = some (.arr32 l) := by
  simp [mkFindEnv, envLookup, show ("a" : String) ≠ "i" by decide]

theorem mkFindEnv_n (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "n" = some (.u32 nv) := by
  simp [mkFindEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "a" by decide]

theorem mkFindEnv_k (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "k" = some (.u32 kv) := by
  simp [mkFindEnv, envLookup, show ("k" : String) ≠ "i" by decide,
    show ("k" : String) ≠ "a" by decide,
    show ("k" : String) ≠ "n" by decide]

/-- Updating `i` stays in the env family. -/
theorem findEnv_update_i (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t t' : Nat) :
    envUpdate (mkFindEnv l nv kv t) "i"
        (.u32 (BitVec.ofNat 32 t')) =
      some (mkFindEnv l nv kv t') := by
  simp [mkFindEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem findCond_eval (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (h : t < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkFindEnv l nv kv t) =
      .ok (.b (decide (t < nv.toNat))) := by
  have hi := mkFindEnv_i l nv kv t
  have hn := mkFindEnv_n l nv kv t
  simp [evalExpr, hi, hn, ofNat32_ult t nv h]

/-- Body on match: return the index (any fuel). -/
theorem findBody_hit (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (x : BitVec 32)
    (hget : l[t]? = some x) (heq : x = kv) (ht32 : t < 2 ^ 32) :
    evalStmtFuel F findBody (mkFindEnv l nv kv t) =
      .ok (mkFindEnv l nv kv t,
        .returned (.u32 (BitVec.ofNat 32 t))) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hidx : evalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) =
        .ok (.u32 x) := by
    simp only [evalExpr, ha, hii, hkk, hget]
  have hk := mkFindEnv_k l nv kv t
  have hcond : evalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) = .ok (.b true) := by
    simp [evalExpr, ha, hii, hkk, hget, hk, heq]
  have hret : evalExpr (.var "i") (mkFindEnv l nv kv t) =
        .ok (.u32 (BitVec.ofNat 32 t)) :=
    evalExpr_var_hit _ _ _ (mkFindEnv_i l nv kv t)
  cases F <;>
    simp [findBody, evalStmtFuel, evalStmtZero, evalStmtWith, hcond, hret]

/-- Body on miss: step the index (any fuel). -/
theorem findBody_miss (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat)
    (hmiss : ∀ x, l[t]? = some x → x ≠ kv)
    (htlen : t < l.length) (ht32 : t < 2 ^ 32) :
    evalStmtFuel F findBody (mkFindEnv l nv kv t) =
      .ok (mkFindEnv l nv kv (t + 1), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htlen
  have hne : l[t] ≠ kv := hmiss _ hget
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hidx : evalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) =
        .ok (.u32 l[t]) := by
    simp only [evalExpr, ha, hii, hkk, hget]
  have hk := mkFindEnv_k l nv kv t
  have hcond : evalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) = .ok (.b false) := by
    simp only [evalExpr, ha, hii, hkk, hget, hk]
    simp [hne]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkFindEnv l nv kv t) =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    have hii := mkFindEnv_i l nv kv t
    simp only [evalExpr, litVal, hii, ofNat32_add_one]
  have up := findEnv_update_i l nv kv t (t + 1)
  cases F <;>
    simp [findBody, evalStmtFuel, evalStmtZero, evalStmtWith, hcond, hi2, up]

/-- Body past the end: the index read fails `OOB` (any fuel). -/
theorem findBody_oob (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (hlen32 : l.length < 2 ^ 32) :
    evalStmtFuel F findBody (mkFindEnv l nv kv l.length) =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ hlen32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkFindEnv_a l nv kv l.length
  have hii := mkFindEnv_i l nv kv l.length
  have herr : evalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv l.length) = .error .OOB := by
    simp only [evalExpr, ha, hii, hkk, hget]
  cases F <;>
    simp [findBody, evalStmtFuel, evalStmtZero, evalStmtWith, herr]

/-- Loop correctness, hit: when the suffix finds `j`, the loop returns
    it (fuel-generalized; the `+1` absorbs the final exit iteration, so
    the zero-fuel case is vacuous). -/
theorem findWhile_some (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t j : Nat)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = some j) :
    evalStmtFuel F findWhile (mkFindEnv l nv kv t) =
      .ok (mkFindEnv l nv kv j,
        .returned (.u32 (BitVec.ofNat 32 j))) := by
  induction F generalizing t j with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) = .ok (.b true) := by
        simpa [htn] using (findCond_eval l nv kv t ht32)
      match hget : l[t]? with
      | some x =>
        by_cases heq : x = kv
        · have hbody := findBody_hit F l nv kv t x hget heq ht32
          have hfound := findSuffix_hit l t (min nv.toNat l.length) kv x
            hget heq hlt
          have hjt : t = j := by
            rw [hfound] at hfind
            exact Option.some_inj.mp hfind
          have hstep : evalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t)
              = .ok (mkFindEnv l nv kv t,
                .returned (.u32 (BitVec.ofNat 32 t))) := by
            simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
              hcond, hbody]
          rw [← hjt]
          exact hstep
        · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
            intro y hy
            rw [hget] at hy
            cases hy
            exact heq
          have hbody := findBody_miss F l nv kv t hmiss htl ht32
          have htail := findSuffix_miss l t (min nv.toNat l.length) kv
            hmiss hlt
          have hstep : evalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t)
              = evalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1)) := by
            simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
              hcond, hbody]
          rw [hstep]
          rw [htail] at hfind
          exact ih (t + 1) j (by omega) (by omega) hfind
      | none =>
        have hsome : l[t]? = some l[t] := List.getElem?_eq_getElem htl
        rw [hsome] at hget
        simp at hget
    · have htt : t = min nv.toNat l.length := by omega
      subst htt
      have hnil := findSuffix_nil l (min nv.toNat l.length) kv
      rw [hnil] at hfind
      simp at hfind

/-- Loop correctness, miss: when the suffix finds nothing, the loop
    falls through with `i = n` (exact length) or reports `OOB`
    (over-long length) — mirroring `sumWhile_correct`/`sumWhile_oob`
    in one induction. -/
theorem findWhile_none (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t : Nat)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = none) :
    evalStmtFuel F findWhile (mkFindEnv l nv kv t) =
      if decide (nv.toNat ≤ l.length) then
        .ok (mkFindEnv l nv kv nv.toNat, .fellThrough)
      else .error .OOB := by
  induction F generalizing t with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) = .ok (.b true) := by
        simpa [htn] using (findCond_eval l nv kv t ht32)
      have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htl
      by_cases heq : l[t] = kv
      · exfalso
        have hfound := findSuffix_hit l t (min nv.toNat l.length) kv l[t]
          hget heq hlt
        rw [hfound] at hfind
        simp at hfind
      · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
          intro y hy
          rw [hget] at hy
          cases hy
          exact heq
        have hbody := findBody_miss F l nv kv t hmiss htl ht32
        have htail := findSuffix_miss l t (min nv.toNat l.length) kv
          hmiss hlt
        have hstep : evalStmtFuel (F + 1) findWhile
              (mkFindEnv l nv kv t)
            = evalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1)) := by
          simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep]
        rw [htail] at hfind
        exact ih (t + 1) (by omega) (by omega) hfind
    · have htt : t = min nv.toNat l.length := by omega
      by_cases hnlen : nv.toNat ≤ l.length
      · have htn : t = nv.toNat := by omega
        subst htn
        have hcond : evalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv nv.toNat) = .ok (.b false) := by
          simpa using (findCond_eval l nv kv nv.toNat h32n)
        have htrue : (decide (nv.toNat ≤ l.length)) = true := by
          simp [hnlen]
        simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, htrue]
      · have htl2 : t = l.length := by omega
        subst htl2
        have hlt' : l.length < nv.toNat := by omega
        have hcond : evalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv l.length) = .ok (.b true) := by
          simpa [hlt'] using (findCond_eval l nv kv l.length h32l)
        have hbody := findBody_oob F l nv kv h32l
        have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
          simp [hnlen]
        simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody, hfalse]

/-- `emit_correct` for `find_eq`, fuel-generalized (split on the
    whole-prefix find, then on length exactness). -/
theorem evalFuncFuel_find (F : Nat) (l : List (BitVec 32))
    (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length + 1 ≤ F) :
    evalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] =
      findEqFwd l nv kv := by
  have hbind : bindArgs findEqFunc.args [.arr32 l, .u32 nv, .u32 kv] =
      some [("a", .arr32 l), ("n", .u32 nv), ("k", .u32 kv)] := rfl
  have hbody : findEqFunc.body =
      .seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq findWhile
            (.return_ (.var "n"))) := rfl
  have henv : [("i", .u32 (BitVec.ofNat 32 0)), ("a", .arr32 l),
        ("n", .u32 nv), ("k", .u32 kv)]
      = mkFindEnv l nv kv 0 := rfl
  have hbridge := findSuffix_zero_idx l nv.toNat kv
  match hfi : findIdxU32 l nv.toNat kv with
  | some j =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        evalStmtFuel G findWhile (mkFindEnv l nv kv 0) =
          .ok (mkFindEnv l nv kv j,
            .returned (.u32 (BitVec.ofNat 32 j))) := by
      intro G hG
      exact findWhile_some l nv kv G 0 j (Nat.zero_le _) h32n
        (by omega) (by rw [hbridge, hfi])
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            findWhile (mkFindEnv l nv kv 0) =
          .ok (mkFindEnv l nv kv j,
            .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop 0 (by omega)
      simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtZero,
        evalStmtWith, evalExpr, litVal, envExtend, findEqFwd, findEqOut,
        henv, hloopH0, hfi]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            findWhile (mkFindEnv l nv kv 0) =
          .ok (mkFindEnv l nv kv j,
            .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop (F + 1) (by omega)
      simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtWith,
        evalExpr, litVal, envExtend, findEqFwd, findEqOut, henv, hloopS, hfi]
  | none =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        evalStmtFuel G findWhile (mkFindEnv l nv kv 0) =
          if decide (nv.toNat ≤ l.length) then
            .ok (mkFindEnv l nv kv nv.toNat, .fellThrough)
          else .error .OOB := by
      intro G hG
      exact findWhile_none l nv kv G 0 (Nat.zero_le _) h32n h32l
        (by omega) (by rw [hbridge, hfi])
    by_cases hle : nv.toNat ≤ l.length
    · have htrue : (decide (nv.toNat ≤ l.length)) = true := by simp [hle]
      have hsnret : envLookup (mkFindEnv l nv kv nv.toNat) "n" =
            some (.u32 nv) :=
        mkFindEnv_n l nv kv nv.toNat
      have hinv : BitVec.ofNat 32 nv.toNat = nv := ofNat32_toNat_inv nv
      cases F with
      | zero =>
        have hloopH0 : evalStmtWith evalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0) =
            .ok (mkFindEnv l nv kv nv.toNat, .fellThrough) := by
          have h := hloop 0 (by omega)
          rwa [htrue] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envExtend, findEqFwd, findEqOut,
          henv, hloopH0, hsnret, hfi, htrue, hinv]
      | succ F =>
        have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0) =
            .ok (mkFindEnv l nv kv nv.toNat, .fellThrough) := by
          have h := hloop (F + 1) (by omega)
          rwa [htrue] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtWith,
          evalExpr, litVal, envExtend, findEqFwd, findEqOut, henv, hloopS,
          hsnret, hfi, htrue, hinv]
    · have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
        simp [hle]
      cases F with
      | zero =>
        have hloopH0 : evalStmtWith evalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0) = .error .OOB := by
          have h := hloop 0 (by omega)
          rwa [hfalse] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envExtend, findEqFwd, findEqOut,
          henv, hloopH0, hfi, hfalse]
      | succ F =>
        have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0) = .error .OOB := by
          have h := hloop (F + 1) (by omega)
          rwa [hfalse] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtWith,
          evalExpr, litVal, envExtend, findEqFwd, findEqOut, henv, hloopS,
          hfi, hfalse]

/-- `emit_correct` for `find_eq` at the default fuel. -/
theorem emit_correct_find (l : List (BitVec 32)) (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hfuel : min nv.toNat l.length + 1 ≤ EVAL_FUEL) :
    evalFunc findEqFunc [.arr32 l, .u32 nv, .u32 kv] = findEqFwd l nv kv :=
  evalFuncFuel_find EVAL_FUEL l nv kv h32n h32l hfuel
/-! ### `cls`: switch-as-if-chain (loop-free) -/

/-- Canonical CoreIR for `tests/c/cls.c`: the `cir.switch` (equality
    cases on `0`/`1` + `default`, every case a bare const `return`)
    lowered to a nested `if_` chain. The validator admits exactly this
    lowered shape (`isClsShape` pins the scrutinee type, case consts,
    and result consts); any other `cir.switch` is rejected loudly. -/
def clsFunc : Func :=
  ⟨"cls",
   [{ name := "x", ty := .u 32, role := .owned }],
   .u 32,
   .if_ (.ueq (.var "x") (.lit (.u32 0)))
     (.return_ (.lit (.u32 10)))
     (.if_ (.ueq (.var "x") (.lit (.u32 1)))
       (.return_ (.lit (.u32 20)))
       (.return_ (.lit (.u32 30))))⟩

/-- Value-level forward for `cls` (cf. rendered `cls_fwd`). -/
def clsFwd (x : BitVec 32) : Result Value :=
  if x == 0 then .ok (.u32 10)
  else if x == 1 then .ok (.u32 20)
  else .ok (.u32 30)

/-- `emit_correct` for `cls` (loop-free: any fuel). -/
theorem evalFuncFuel_cls (F : Nat) (x : BitVec 32) :
    evalFuncFuel F clsFunc [.u32 x] = clsFwd x := by
  have hbind : bindArgs clsFunc.args [.u32 x] =
      some [("x", .u32 x)] := rfl
  have hbody : clsFunc.body =
      .if_ (.ueq (.var "x") (.lit (.u32 0)))
        (.return_ (.lit (.u32 10)))
        (.if_ (.ueq (.var "x") (.lit (.u32 1)))
          (.return_ (.lit (.u32 20)))
          (.return_ (.lit (.u32 30)))) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) :=
    envExtend_hit _ _ _
  by_cases h0 : x = 0
  · subst h0
    cases F <;>
      simp [evalFuncFuel, clsFunc, bindArgs, evalStmtFuel, evalStmtZero,
        evalStmtWith, evalExpr, litVal, envLookup, clsFwd]
  · have h0' : x ≠ 0#32 := h0
    by_cases h1 : x = 1
    · subst h1
      cases F <;>
        simp [evalFuncFuel, clsFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, clsFwd]
    · have h1' : x ≠ 1#32 := h1
      have e0 : (x == 0#32) = false := by simp [h0']
      have e1 : (x == 1#32) = false := by simp [h1']
      cases F <;>
        simp [evalFuncFuel, clsFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, clsFwd, e0, e1]

/-- `emit_correct` for `cls` at the default fuel. -/
theorem emit_correct_cls (x : BitVec 32) :
    evalFunc clsFunc [.u32 x] = clsFwd x :=
  evalFuncFuel_cls EVAL_FUEL x

theorem matchFrag_findEq : matchFrag findEqFunc = some .findEq := rfl

theorem matchFrag_cls : matchFrag clsFunc = some .cls := rfl

/-! ## Rendering to Lean file text -/

/-- Emission failures: only "not in the admitted fragment" exists
    (oracle/aliasing rejections live in `validate`). -/
inductive EmitError : Type
  | notFragment : String → EmitError
  deriving DecidableEq, Repr

/-- Emitted Lean code for one function: forward definition file text, plus
    an optional backward definition for borrow-returns (`choose`-shape,
    Phase 4). -/
structure EmittedFunc : Type where
  forward : String
  backward : Option String
  deriving DecidableEq, Repr

/-- File header shared by all rendered outputs. -/
def emitHeader : String :=
  "-- Generated by the Circe emitter (Phase 4) from validated CoreIR. Do not edit.\n"
  ++ "-- Emitter correctness (`Circe.Emit.emit_correct_add/incr/choose/sum`):\n"
  ++ "-- this file is the tag-erased rendering of the verified forward function\n"
  ++ "-- (value tags dropped; pretty-printing is trusted, semantics verified).\n"
  ++ "-- Checked by `lake env lean`; see `tools/check-phase4.sh`.\n"

/-- Render the `add` forward definition (`add_fwd`). -/
def emitAddText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}`: values in, value out (no memory). -/\n"
  ++ s!"def {name}_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedAddI32 a b\n"

/-- Render the `incr` forward definition (`incr_fwd`), with the
    caller-side rewrite in the doc comment. -/
def emitIncrText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (`*p = *p + 1`, functionalized).\n"
  ++ s!"    Caller rewrite: `incr(&y)` becomes `y ← {name}_fwd y`. -/\n"
  ++ s!"def {name}_fwd (p : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedIncrI32 p\n"

/-- Render the `add64` forward definition (`add64_fwd`, S3b). -/
def emitAdd64Text (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}`: values in, value out (no memory). -/\n"
  ++ s!"def {name}_fwd (a b : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  checkedAddI64 a b\n"

/-- Render the `addu64` forward definition (`addu64_fwd`, S3b:
    wrapping unsigned addition, never fails). -/
def emitAddu64Text (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (wrapping `u64` addition). -/\n"
  ++ s!"def {name}_fwd (a b : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  .ok (a + b)\n"

/-- Render the `choose` forward definition (`choose_fwd`). -/
def emitChooseFwdText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (borrow-return): forward selection. -/\n"
  ++ s!"def {name}_fwd (b : Bool) (x y : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (if b then x else y)\n"

/-- Render the `choose` backward definition (`choose_back`): file-local,
    concatenated after the forward text (no import of its own). -/
def emitChooseBackText (name : String) : String :=
  s!"/-- Backward propagation for `{name}`: the updated return value flows back to the selected input; the other input is unchanged. -/\n"
  ++ s!"def {name}_back (b : Bool) (x y ret : BitVec 32) : Result (BitVec 32 × BitVec 32) :=\n"
  ++ "  .ok (if b then (ret, y) else (x, ret))\n"

/-- Render the `sum_array` forward definition (`sum_fwd`): the length
    hypothesis travels in the type (`BoundedList`), so the loop bound is
    structural and the body is the verified `prefixSumU32` fold. -/
def emitSumText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ "/-- Pure translation of `" ++ name ++ "` (bounded `u32` accumulation, wrapping). -/\n"
  ++ "def " ++ name ++ "_fwd {n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=\n"
  ++ "  .ok (prefixSumU32 a.val a.val.length)\n"

/-- Render the `vec_alloc` forward definition (`vec_alloc_fwd`): the
    length comes in as a word, so the body is the verified
    `vecFillSumU32` fold over `n.toNat`. -/
def emitVecText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ "/-- Pure translation of `" ++ name ++ "` (uniquely-owned `u32` heap block: allocate, fill with indices, sum, free). -/\n"
  ++ "def " ++ name ++ "_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecFillSumU32 n.toNat\n"

/-- Render the `vec_copy_sum` forward definition (M1a): two live `u32`
    blocks, but the copy is value-invisible, so the body is the same
    verified `vecFillSumU32` fold over `n.toNat`. -/
def emitVec2Text (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ "/-- Pure translation of `" ++ name ++ "` (two live `u32` heap blocks: allocate two, fill `a` with indices, copy `a` into `b`, sum `b`, free both). -/\n"
  ++ "def " ++ name ++ "_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecFillSumU32 n.toNat\n"

/-- Render the `add_caller` forward definition: two sequential DAG calls
    into `add_fwd`. The file stays self-contained (only `Circe.Base` is
    imported — cross-file imports need oleans, which plain `out/` sources
    lack): the leaf body `checkedAddI32` is inlined, and
    `addCallerFwd_as_calls` certifies this is literally two `add_fwd`
    calls sequenced. -/
def emitAddCallerText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (DAG calls into `add_fwd`, twice;\n"
  ++ "    leaf body `checkedAddI32` inlined, see `addCallerFwd_as_calls`). -/\n"
  ++ s!"def {name}_fwd (x y z : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  do let t ← checkedAddI32 x y\n"
  ++ "     checkedAddI32 t z\n"

/-- Render the `sum_caller` forward definition: direct delegation to the
    `sum_array` body (same `Base` op, see `sumCallerFwd_is_call`). -/
def emitSumCallerText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (delegates to `sum_array_fwd`). -/\n"
  ++ "def " ++ name ++ "_fwd {n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=\n"
  ++ "  .ok (prefixSumU32 a.val a.val.length)\n"

/-- Render the `translate` forward definition: direct delegation to the
    verified `Base` op `pointTranslate` (field-wise checked addition;
    `translateFwd_*` bridge lemmas certify the delegation). -/
def emitTranslateText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (field-wise `Point` translation). -/\n"
  ++ s!"def {name}_fwd (p : Point) (dx dy : BitVec 32) : Result Point :=\n"
  ++ "  pointTranslate p dx dy\n"

/-- Render the `nested_sum` forward definition: the double fold over
    `Base.nestedSumU32` (both bounds travel as words; fuel sufficiency
    is the `emit_correct_nested` side condition). -/
def emitNestedText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (nested bounded `u32` loops, wrapping). -/\n"
  ++ s!"def {name}_fwd (n m : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (nestedSumU32 n.toNat m.toNat)\n"

/-- Render the `skip_sum` forward definition (`break` caps iterations
    at 9, so no fuel hypothesis is needed downstream). -/
def emitSkipText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (bounded loop with `break`/`continue`, wrapping). -/\n"
  ++ s!"def {name}_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (skipSumU32 n.toNat)\n"

/-- Render the `find_eq` forward definition (early return lowered to
    `Base.findEqOut`: first match, else length, else `OOB`). Stated
    over `BitVec` (not `Value`): rendered files import only
    `Circe.Base`, and tag erasure is trusted rendering anyway. -/
def emitFindEqText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (bounded search with early return). -/\n"
  ++ s!"def {name}_fwd (a : List (BitVec 32)) (n k : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  findEqOut a n.toNat k\n"

/-- Render the `cls` forward definition (switch lowered to an
    if-chain on `ueq`). -/
def emitClsText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (`switch` lowered to an if-chain). -/\n"
  ++ s!"def {name}_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  if x == 0 then .ok 10\n"
  ++ "  else if x == 1 then .ok 20\n"
  ++ "  else .ok 30\n"

/-! ## S4 spec stubs (`out/*_Spec.lean`)

Unverified scaffolding, not trusted code: each stub re-states the
function signature, names the `Base`-op body reference (the same body
the emitted forward uses — body identity is the transfer argument in
`docs/VERIFYING.md`), lists edge cases, and provides a `Diff`-style
prop-test entry (`_check : Bool`). The user copies the stub into
`Circe.Specs` (or a per-project spec file) and fills the equation;
the `_check` placeholder states whatever equation is already known
(self-agreement where the spec is still TODO, the real equation for
`sum`/`vec`). Out-of-subset input never reaches here: `emitSpec`
dispatches on `matchFrag`, exactly like `emitFunc`. -/

/-- File header shared by all rendered spec stubs. -/
def emitSpecHeader : String :=
  "-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.\n"
  ++ "-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec\n"
  ++ "-- file) and fill the equation. The `_fwd` mirror below is body-identical\n"
  ++ "-- to the emitted forward (same `Base` op); specs proved against it\n"
  ++ "-- transfer verbatim by body identity (see docs/VERIFYING.md).\n"

/-- Spec stub for the `add` shape. -/
def emitAddSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `int32_t {name}(int32_t a, int32_t b)`.\n"
  ++ s!"    Base body reference: `checkedAddI32` (cf. emitted `{name}_fwd`, `emit_correct_add`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedAddI32 a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, `INT32_MAX`/`INT32_MIN` boundaries, wrap. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1),\n"
  ++ "   (0x80000000, 0), (0x80000000, 0xFFFFFFFF), (0xFFFFFFFF, 0xFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to the equation, e.g. ok implies `r = a + b`\n"
  ++ "    with the `nsw` certificate (see `incr_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty == (repr (checkedAddI32 p.1 p.2)).pretty\n"

/-- Spec stub for the `incr` shape. -/
def emitIncrSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `void {name}(int32_t *p)` (`*p = *p + 1`, functionalized).\n"
  ++ s!"    Base body reference: `checkedIncrI32` (cf. emitted `{name}_fwd`, `emit_correct_incr`). -/\n"
  ++ s!"def {name}_spec_fwd (p : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedIncrI32 p\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, `INT32_MAX` (overflow), `INT32_MIN`, `-1`. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to `incr_correct` (successor + certificate). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p => (repr ({name}_spec_fwd p)).pretty == (repr (checkedIncrI32 p)).pretty\n"

/-- Spec stub for the 64-bit `add64` shape (S3b). -/
def emitAdd64SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `int64_t {name}(int64_t a, int64_t b)`.\n"
  ++ s!"    Base body reference: `checkedAddI64` (cf. emitted `{name}_fwd`, `emit_correct_add64`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  checkedAddI64 a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, `INT64_MAX`/`INT64_MIN` boundaries, wrap. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × BitVec 64) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFFFFFFFFFF, 0), (0x7FFFFFFFFFFFFFFF, 1),\n"
  ++ "   (0x8000000000000000, 0), (0x8000000000000000, 0xFFFFFFFFFFFFFFFF),\n"
  ++ "   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err equation (see `emit_correct_add64_ok`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty == (repr (checkedAddI64 p.1 p.2)).pretty\n"

/-- Spec stub for the 64-bit `addu64` shape (S3b, wrapping). -/
def emitAddu64SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint64_t {name}(uint64_t a, uint64_t b)` (wrapping, never fails).\n"
  ++ s!"    Base body reference: `a + b` (cf. emitted `{name}_fwd`, `emit_correct_addu64`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  .ok (a + b)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, `UINT64_MAX` wrap edges. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × BitVec 64) :=\n"
  ++ "  [(0, 0), (1, 2), (0xFFFFFFFFFFFFFFFF, 0), (0xFFFFFFFFFFFFFFFF, 1),\n"
  ++ "   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: wrapping equation holds on every edge (this one is\n"
  ++ "    already the spec — unsigned addition never fails). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty == (repr ((Except.ok (p.1 + p.2) : Result (BitVec 64)))).pretty\n"

/-- Spec stub for the `choose` shape (forward + backward). -/
def emitChooseSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: borrow-return `{name}(bool b, int32_t *x, int32_t *y)`.\n"
  ++ s!"    Base body references: `if b then x else y` / back-propagation pair\n"
  ++ s!"    (cf. emitted `{name}_fwd` / `{name}_back`, `choose_lens_laws`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Bool) (x y : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (if b then x else y)\n"
  ++ s!"def {name}_spec_back (b : Bool) (x y ret : BitVec 32) : Result (BitVec 32 × BitVec 32) :=\n"
  ++ "  .ok (if b then (ret, y) else (x, ret))\n"
  ++ "\n"
  ++ s!"/-- Edge cases: both selectors, zero / distinct / max inputs. -/\n"
  ++ s!"def {name}_spec_edges : List (Bool × BitVec 32 × BitVec 32) :=\n"
  ++ "  [(true, 0, 0), (true, 1, 2), (false, 1, 2), (false, 0xFFFFFFFF, 0)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: get-put holds on every edge (see `choose_lens_laws`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_back t.1 t.2.1 t.2.2 (if t.1 then t.2.1 else t.2.2))).pretty\n"
  ++ s!"      == (repr ((Except.ok (t.2.1, t.2.2) : Result (BitVec 32 × BitVec 32)))).pretty\n"

/-- Spec stub for the `sum_array` shape. -/
def emitSumSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t *a, uint32_t n)` (length-paired, wrapping).\n"
  ++ s!"    Base body reference: `prefixSumU32` (cf. emitted `{name}_fwd`, `emit_correct_sum`). -/\n"
  ++ s!"def {name}_spec_fwd " ++ "{n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=\n"
  ++ "  .ok (prefixSumU32 a.val a.val.length)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / max-fuel (length = bound). -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32)) :=\n"
  ++ "  [[], [0], [1], [1, 2, 3], [0xFFFFFFFF, 1]]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the `List.sum` equation holds on every edge\n"
  ++ "    (this one is already the spec — see `sum_correct`; copy into\n"
  ++ "    `Circe.Specs` to build on it). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun l =>\n"
  ++ "    (repr (prefixSumU32 l l.length)).pretty == (repr ((l.take l.length).sum)).pretty\n"

/-- Spec stub for the `vec_alloc` shape. -/
def emitVecSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n)` (allocate, fill with indices, sum, free).\n"
  ++ s!"    Base body reference: `vecFillSumU32` (cf. emitted `{name}_fwd`, `emit_correct_vec`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecFillSumU32 n.toNat\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / small / page-ish. -/\n"
  ++ s!"def {name}_spec_edges : List Nat :=\n"
  ++ "  [0, 1, 2, 10, 256]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the index-sum equation holds on every edge\n"
  ++ "    (this one is already the spec — see `vec_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ "    (repr (vecFillSumU32 n)).pretty\n"
  ++ "      == (repr ((Except.ok (((List.range n).map (BitVec.ofNat 32)).sum) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `vec_copy_sum` shape (M1a: two live blocks). -/
def emitVec2SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n)` (allocate two, fill `a` with indices, copy `a` into `b`, sum `b`, free both).\n"
  ++ s!"    Base body reference: `vecFillSumU32` — the copy is value-invisible (cf. emitted `{name}_fwd`, `emit_correct_vec2`, `vec2Fwd_eq_vecFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecFillSumU32 n.toNat\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / small / page-ish. -/\n"
  ++ s!"def {name}_spec_edges : List Nat :=\n"
  ++ "  [0, 1, 2, 10, 256]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the index-sum equation holds on every edge\n"
  ++ "    (this one is already the spec — see `vec_correct`; the copy adds\n"
  ++ "    no observable behavior). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ "    (repr (vecFillSumU32 n)).pretty\n"
  ++ "      == (repr ((Except.ok (((List.range n).map (BitVec.ofNat 32)).sum) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `add_caller` shape (S1 DAG calls). -/
def emitAddCallerSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `{name}(x, y, z)` = two DAG calls into `add_fwd`.\n"
  ++ s!"    Base body reference: two sequenced `checkedAddI32` binds, leaf bodies\n"
  ++ s!"    inlined (cf. emitted `{name}_fwd`, `addCallerFwd_as_calls`). -/\n"
  ++ s!"def {name}_spec_fwd (x y z : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  do let t ← checkedAddI32 x y\n"
  ++ "     checkedAddI32 t z\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, first-add overflow, second-add overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0, 0), (1, 2, 3), (0x7FFFFFFF, 1, 0), (0x7FFFFFFF, 0, 1), (1, 0x7FFFFFFF, 1)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the two-call bind structure holds on every edge\n"
  ++ "    (cf. `addCallerFwd_as_calls`). TODO (user): fill the ok/err equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2)).pretty\n"
  ++ s!"      == (repr ((checkedAddI32 t.1 t.2.1).bind fun u => checkedAddI32 u t.2.2)).pretty\n"

/-- Spec stub for the `sum_caller` shape (S1 delegation). -/
def emitSumCallerSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `{name}(a, n)` delegates to `sum_array_fwd`.\n"
  ++ s!"    Base body reference: `prefixSumU32` (cf. emitted `{name}_fwd`, `sumCallerFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd " ++ "{n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=\n"
  ++ "  .ok (prefixSumU32 a.val a.val.length)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / max-fuel (length = bound). -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32)) :=\n"
  ++ "  [[], [0], [1], [1, 2, 3], [0xFFFFFFFF, 1]]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the `List.sum` equation holds on every edge\n"
  ++ "    (cf. `sumCallerFwd_is_call`, `sum_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun l =>\n"
  ++ "    (repr (prefixSumU32 l l.length)).pretty == (repr ((l.take l.length).sum)).pretty\n"

/-- Spec stub for the `translate` shape (S2 struct-by-value). -/
def emitTranslateSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `struct Point {name}(struct Point p, int32_t dx, int32_t dy)`.\n"
  ++ s!"    Base body reference: `pointTranslate` (cf. emitted `{name}_fwd`, `evalFuncFuel_translate`). -/\n"
  ++ s!"def {name}_spec_fwd (p : Point) (dx dy : BitVec 32) : Result Point :=\n"
  ++ "  pointTranslate p dx dy\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, x-overflow, y-overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (Point × BitVec 32 × BitVec 32) :=\n"
  ++ "  [((⟨0, 0⟩ : Point), 0, 0), ((⟨1, 2⟩ : Point), 3, 4),\n"
  ++ "   ((⟨0x7FFFFFFF, 0⟩ : Point), 1, 0), ((⟨0, 0x7FFFFFFF⟩ : Point), 0, 1)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `pointTranslate` on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err bridges (`translateFwd_ok_bridge`,\n"
  ++ "    `translateFwd_err_x/y` — all three fire in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2)).pretty\n"
  ++ s!"      == (repr (pointTranslate t.1 t.2.1 t.2.2)).pretty\n"

/-- Spec stub for the `nested_sum` shape (S3a). -/
def emitNestedSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n, uint32_t m)` (nested bounded loops, wrapping).\n"
  ++ s!"    Base body reference: `nestedSumU32` (cf. emitted `{name}_fwd`, `emit_correct_nested`). -/\n"
  ++ s!"def {name}_spec_fwd (n m : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (nestedSumU32 n.toNat m.toNat)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty outer / empty inner / unit / small square. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (0, 5), (5, 0), (1, 1), (3, 4), (10, 10)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `nestedSumU32` on every edge.\n"
  ++ "    TODO (user): strengthen to the double-fold equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty\n"
  ++ s!"      == (repr ((Except.ok (nestedSumU32 p.1.toNat p.2.toNat) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `skip_sum` shape (S3a break/continue). -/
def emitSkipSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n)` (`continue` at 2, `break` at 8).\n"
  ++ s!"    Base body reference: `skipSumU32` (cf. emitted `{name}_fwd`, `emit_correct_skip`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (skipSumU32 n.toNat)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / the skipped 2 / the break cap 8–9 / above cap. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 2, 3, 8, 9, 100]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `skipSumU32` on every edge.\n"
  ++ "    TODO (user): strengthen to the capped-range equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ s!"    (repr ({name}_spec_fwd n)).pretty\n"
  ++ s!"      == (repr ((Except.ok (skipSumU32 n.toNat) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `find_eq` shape (S3a early return). -/
def emitFindEqSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t *a, uint32_t n, uint32_t k)`\n"
  ++ "    (first match, else length, else `OOB`).\n"
  ++ s!"    Base body reference: `findEqOut` (cf. emitted `{name}_fwd`, `emit_correct_find`). -/\n"
  ++ s!"def {name}_spec_fwd (a : List (BitVec 32)) (n k : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  findEqOut a n.toNat k\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton hit / hit / miss / over-long length. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × BitVec 32 × BitVec 32) :=\n"
  ++ "  [([], 0, 0), ([1], 1, 1), ([1, 2, 3], 3, 2), ([1, 2, 3], 3, 9), ([1, 2, 3], 9, 2)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `findEqOut` on every edge.\n"
  ++ "    TODO (user): strengthen to the hit/miss/`OOB` equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2)).pretty\n"
  ++ s!"      == (repr (findEqOut t.1 t.2.1.toNat t.2.2)).pretty\n"

/-- Spec stub for the `cls` shape (S3a switch-as-if-chain). -/
def emitClsSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t x)` (`switch` on 0/1 + default).\n"
  ++ s!"    Base body reference: the if-chain (cf. emitted `{name}_fwd`, `emit_correct_cls`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  if x == 0 then .ok 10\n"
  ++ "  else if x == 1 then .ok 20\n"
  ++ "  else .ok 30\n"
  ++ "\n"
  ++ s!"/-- Edge cases: both cases, default, max. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 2, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the class equation holds on every edge (this one is\n"
  ++ "    already the spec — the if-chain is the whole body). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun x =>\n"
  ++ s!"    (repr ({name}_spec_fwd x)).pretty\n"
  ++ "      == (repr (((if x == (0 : BitVec 32) then (Except.ok (10 : BitVec 32)) else if x == (1 : BitVec 32) then (Except.ok (20 : BitVec 32)) else (Except.ok (30 : BitVec 32))) : Result (BitVec 32)))).pretty\n"

/-- The spec emitter: accepted fragment renders to stub text; everything
    else is rejected loudly (never silently modeled). -/
def emitSpec (f : Func) : Except EmitError String :=
  match matchFrag f with
  | some .add => .ok (emitAddSpecText f.name)
  | some .add64 => .ok (emitAdd64SpecText f.name)
  | some .addu64 => .ok (emitAddu64SpecText f.name)
  | some .incr => .ok (emitIncrSpecText f.name)
  | some .choose => .ok (emitChooseSpecText f.name)
  | some .sum => .ok (emitSumSpecText f.name)
  | some .vec => .ok (emitVecSpecText f.name)
  | some .vec2 => .ok (emitVec2SpecText f.name)
  | some .addCall => .ok (emitAddCallerSpecText f.name)
  | some .sumCall => .ok (emitSumCallerSpecText f.name)
  | some .translate => .ok (emitTranslateSpecText f.name)
  | some .nested => .ok (emitNestedSpecText f.name)
  | some .skip => .ok (emitSkipSpecText f.name)
  | some .findEq => .ok (emitFindEqSpecText f.name)
  | some .cls => .ok (emitClsSpecText f.name)
  | none => .error (.notFragment s!"not in the admitted fragment: {f.name}")

/-- The emitter: accepted fragment renders to file text; everything else
    is rejected loudly (never silently modeled). -/
def emitFunc (f : Func) : Except EmitError EmittedFunc :=
  match matchFrag f with
  | some .add => .ok ⟨emitAddText f.name, none⟩
  | some .add64 => .ok ⟨emitAdd64Text f.name, none⟩
  | some .addu64 => .ok ⟨emitAddu64Text f.name, none⟩
  | some .incr => .ok ⟨emitIncrText f.name, none⟩
  | some .choose =>
    .ok ⟨emitChooseFwdText f.name, some (emitChooseBackText f.name)⟩
  | some .sum => .ok ⟨emitSumText f.name, none⟩
  | some .vec => .ok ⟨emitVecText f.name, none⟩
  | some .vec2 => .ok ⟨emitVec2Text f.name, none⟩
  | some .addCall => .ok ⟨emitAddCallerText f.name, none⟩
  | some .sumCall => .ok ⟨emitSumCallerText f.name, none⟩
  | some .translate => .ok ⟨emitTranslateText f.name, none⟩
  | some .nested => .ok ⟨emitNestedText f.name, none⟩
  | some .skip => .ok ⟨emitSkipText f.name, none⟩
  | some .findEq => .ok ⟨emitFindEqText f.name, none⟩
  | some .cls => .ok ⟨emitClsText f.name, none⟩
  | none => .error (.notFragment s!"not in the admitted fragment: {f.name}")

/-- Rejection is loud and names the function. -/
theorem emitFunc_rejects (f : Func) (h : matchFrag f = none) :
    ∃ msg, emitFunc f = .error (.notFragment msg) := by
  simp [emitFunc, h]

/-! ## Golden linkage (machine-checked) -/

/-- Project an emission to its forward text (`""` on rejection, so a
    rejection also fails the golden examples below). Top-level def so
    `native_decide` can compile it. -/
def emitForwardText : Except EmitError EmittedFunc → String
  | .ok e => e.forward
  | .error _ => ""

/-- File bytes for one emission: forward text plus the backward definition
    (if any). Top-level def so `native_decide` can compile it. -/
def emitFileText : Except EmitError EmittedFunc → String
  | .ok e =>
    match e.backward with
    | none => e.forward
    | some b => e.forward ++ "\n" ++ b
  | .error _ => ""

/-- The emitter output for `addFunc` is byte-identical to the checked-in
    golden. Verified on (re)elaboration (clean and CI builds); incremental
    local drift is caught by the `diff` in `tools/check-phase3.sh`, since
    `lake` does not track `include_str` dependencies. -/
example : emitForwardText (emitFunc addFunc) =
    include_str "../tests/golden/Add.lean" := by native_decide

/-- The emitter output for `incrFunc` is byte-identical to the checked-in
    golden. -/
example : emitForwardText (emitFunc incrFunc) =
    include_str "../tests/golden/Incr.lean" := by native_decide

/-- The emitter output for `chooseFunc` (forward + backward) is
    byte-identical to the checked-in golden. -/
example : emitFileText (emitFunc chooseFunc) =
    include_str "../tests/golden/Choose.lean" := by native_decide

/-- The emitter output for `sumFunc` is byte-identical to the checked-in
    golden. -/
example : emitFileText (emitFunc sumFunc) =
    include_str "../tests/golden/SumArray.lean" := by native_decide

/-- The emitter output for `vecFunc` is byte-identical to the checked-in
    golden. -/
example : emitFileText (emitFunc vecFunc) =
    include_str "../tests/golden/VecAlloc.lean" := by native_decide

/-- The emitter output for `vec2Func` is byte-identical to the checked-in
    two-block golden. -/
example : emitFileText (emitFunc vec2Func) =
    include_str "../tests/golden/VecCopySum.lean" := by native_decide

/-- The emitter output for `addCallerFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc addCallerFunc) =
    include_str "../tests/golden/AddCaller.lean" := by native_decide

/-- The emitter output for `sumCallerFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc sumCallerFunc) =
    include_str "../tests/golden/SumCaller.lean" := by native_decide

/-- The emitter output for `translateFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc translateFunc) =
    include_str "../tests/golden/StructByValue.lean" := by native_decide
