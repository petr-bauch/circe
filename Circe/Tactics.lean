/-
Circe.Tactics — proof tactics for the Phase 5 functional-verification
workflow (see docs/VERIFYING.md).

`cir_simp` bundles the equation lemmas a user reaches for when reasoning
about emitted code: checked-op unfoldings (+ ok/err + range bridges,
32- and 64-bit), `prefixSumU32`/`prefixSumU64` computation + their
`List.sum` bridges, `bget` / `pointTranslate` shapes (+ struct-field
ok/err bridges), call-unfold (`addCallerFwd_as_calls`,
`sumCallerFwd_is_call`), vector ops (`vecFillSumU32`/`vecFillSumU64` +
whole-program bridges), S3a flow folds, and the `Except`
(`Result`) bind/map computation rules (caller-side `←` chains compute
by `rfl`, with assoc/pure for nested binds). Stage 2 (S5) adds two
tactics beside it: `cir_fuel` (fuel automation) and `cir_choose`
(selector split + forward/backward equations), plus the
`word32_lt_two32_of_fuel` bound lemma. Stage 3 (N5) adds two
more: `fuel_step_down` (composer fuel split: `k + 1 ≤ F` gives
`F = F' + 1` with `k ≤ F'` in one `obtain`) and `cir_step`
(registered program-step cascade: evaluator unfolding + `Except.map`
normalization with per-step hypotheses as arguments). Plain `simp` /
`omega` / `bv_decide` suffice in the common case; `cir_simp` just
saves re-listing the set.
-/
import Circe.Emit

/-- `Result` bind on success computes (for caller-side `←` chains). -/
theorem result_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a : Result α).bind f = f a := rfl

/-- `Result` bind on failure short-circuits. -/
theorem result_bind_err {α β : Type} (e : Panic) (f : α → Result β) :
    (Except.error e : Result α).bind f = .error e := rfl

/-- `Result` map on success computes. -/
theorem result_map_ok {α β : Type} (a : α) (f : α → β) :
    (Except.ok a : Result α).map f = .ok (f a) := rfl

/-- `Result` map on failure propagates. -/
theorem result_map_err {α β : Type} (e : Panic) (f : α → β) :
    (Except.error e : Result α).map f = .error e := rfl

/-- `Result` bind associates (for nested caller-side `←` chains). -/
theorem result_bind_assoc {α β γ : Type} (a : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (a.bind f).bind g = a.bind (fun x => (f x).bind g) := by
  cases a <;> rfl

/-- `pure` on the left of a bind computes (for `do`-desugared code). -/
theorem result_pure_bind {α β : Type} (a : α) (f : α → Result β) :
    (pure a : Result α).bind f = f a := rfl

/-! ## S5 helpers: fuel automation + forward/backward `choose` reasoning.

No new subset: these discharge proof obligations the existing
fuel-generalized loop proofs already carry. Placement follows
dependencies (`Tactics` imports `Emit`, so `Emit` cannot import
`Tactics`): fuel automation lives in `Circe.Eval` next to `EVAL_FUEL`,
`cir_choose` lives in `Circe.Emit.Choose` next to the `choose` forward /
backward functions (its simp set names them, so they must be in scope
where the macro is defined). All three are in scope for
`import Circe.Tactics` users via the import chain. -/

/-- Base `cir_simp` set, as a single simp call. Compose with plain `simp`
    for goal-specific lemmas: `cir_simp; simp [my_lemma]`. (A parameterized
    `cir_simp [...]` form is deliberately absent: `simp` argument splicing
    does not accept raw `term` lists, so composition is the interface.) -/
macro "cir_simp" : tactic =>
  `(tactic| simp [checkedAddI32, checkedAddI32_ok, checkedAddI32_err,
    inInt32Range, inInt32Range_iff,
    checkedAddI64, checkedAddI64_ok, checkedAddI64_err,
    inInt64Range, inInt64Range_iff,
    checkedIncrI32, checkedAddU32,
    checkedAddU32Strict, checkedNegI32, checkedNegI32_ok, checkedNegI32_err,
    checkedDivI32, checkedDivI32_zero,
    prefixSumU32, prefixSumU32_take_sum, prefixSumU32_full,
    prefixSumU32_nil, prefixSumU32_zero, prefixSumU32_cons, bget,
    pointTranslate, pointTranslate_ok, pointTranslate_err_x,
    pointTranslate_err_y, translateFwd_ok_bridge, translateFwd_err_x,
    translateFwd_err_y,
    pointSum, pointSum_ok, pointSum_err, methodSumFwd_ok,
    methodSumFwd_err, pointSumRefFwd_is_call,
    accTwo, accTwo_ok, accTwo_err_a, accTwo_err_b, accAddFwd_ok,
    accAddFwd_err, accTwoFwd_is_accTwo,
    accCtorFwd, accCtor, accGetFwd, accDtorFwd,
    moveAcc, moveAcc_ok, moveAcc_err_a, moveAcc_err_b,
    moveAccFwd_is_moveAcc, accMoveCtor, accMoveCtorFwd_is_ok,
    scopeEarly, scopeEarly_ok_eq, scopeEarly_ok_ne,
    scopeEarly_err_a, scopeEarly_err_b, scopeEarlyFwd_is_scopeEarly,
    add3Fwd, add3Fwd_ok, add3Fwd_err,
    useAddFwd_is_call, useNsAddFwd_is_call,
    useTadd32Fwd_is_call, useTadd64Fwd_is_call,
    boxThrough, boxThrough_ok, boxThroughFwd_is_boxThrough,
    boxNew, boxNew_ok, boxGet, boxGet_ok, boxFree, boxFree_ok,
    addCallerFwd_as_calls, sumCallerFwd_is_call,
    vecFillSumU32_correct, vecNew, vecSet, vecGet, vecFree,
    vecReallocFillSumU32_correct, vecRealloc,
    vecFillSumU64_correct, vecNew64, vecSet64, vecGet64, vecFree64,
    prefixSumU64, prefixSumU64_take_sum, prefixSumU64_full,
    prefixSumU64_nil, prefixSumU64_zero, prefixSumU64_cons,
    nestedSumU32, rowU32, skipSumU32, findEqOut, findIdxU32,
    result_bind_ok, result_bind_err, result_map_ok, result_map_err,
    result_bind_assoc, result_pure_bind,
    i32_map_ok, i32_map_error, i64_map_ok, i64_map_error,
    u32_map_ok, u32_map_error, u64_map_ok, u64_map_error,
    addFwd_ok, addFwd_err, sumFwd_ok, sumFwd_oob,
    nestedFwd, skipFwd, findEqFwd, clsFwd, clsFallFwd, clsDenseFwd,
    clsBreakFwd, add64Fwd, addu64Fwd])
