/-
Circe.Tactics — proof tactics for the Phase 5 functional-verification
workflow (see docs/VERIFYING.md).

`cir_simp` bundles the equation lemmas a user reaches for when reasoning
about emitted code: checked-op unfoldings, `prefixSumU32` computation +
its `List.sum` bridge, `bget`/`pointTranslate` shapes, and the `Except`
(`Result`) bind/map computation rules. Plain `simp`/`omega`/`bv_decide`
suffice in the common case; `cir_simp` just saves re-listing the set.
-/
import Circe.Base

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

/-- Base `cir_simp` set, as a single simp call. Compose with plain `simp`
    for goal-specific lemmas: `cir_simp; simp [my_lemma]`. (A parameterized
    `cir_simp [...]` form is deliberately absent: `simp` argument splicing
    does not accept raw `term` lists, so composition is the interface.) -/
macro "cir_simp" : tactic =>
  `(tactic| simp [checkedAddI32, checkedIncrI32, checkedAddU32,
    checkedAddU32Strict, checkedNegI32, checkedDivI32,
    prefixSumU32, prefixSumU32_take_sum, bget, pointTranslate,
    result_bind_ok, result_bind_err, result_map_ok, result_map_err])
