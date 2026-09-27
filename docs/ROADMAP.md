# Circe — Roadmap: short-term plan + mid-term notes

Mid-term goal: non-aliasing C/C++ code, more syntax, tactics that
simplify working with the Lean versions, scaffolding for simple
verification of the input programs on the Lean side.

Short-term scope (locked 2026-09-27): C + struct-by-value only,
calls first, `cir_simp` now + DSL next, spec skeletons in
`out/*_Spec.lean`.

## S0. Docs slim + harness rename — DONE (2026-09-27)

Replaced phase-history docs with `OVERVIEW / SUBSET / PIPELINE /
VERIFYING / ROADMAP` (+ `PINS.md` kept); archived `PLAN.md`,
`CIR_SUBSET.md`, `OWNERSHIP.md`, `SEMANTICS.md` to `docs/archive/`.
`tools/check.sh` is the single superset entry (old `check-phase*.sh`
kept for compat); CI runs `check.sh 100`.

## S1. Multi-function + `cir.call` — DONE (2026-09-27)

DAG-only calls, `Result`-bind translation. Design deltas from the
sketch: new `CStmt.callRet dst f args` (legacy `call` stays a stub,
never produced by `validate`); `Eval` gains a non-breaking program
layer (`Prog`, `findFunc`, `lookupArgs`, `evalProgStmt`,
`evalProgFunc`, + `seq`/`return` composition helpers) — depth-1
dispatch to call-free callees via the old `evalFuncFuel`, so no
existing lemma changed signature. `matchFrag` admits the two caller
shapes (bodies matched in a nested `match`: list patterns nested
inside `⟨⟩` Func patterns hit a Lean parser quirk). Leaves exclude
non-heap calls, so DAG holds by construction (no cycle expressible).
Rendered callers stay self-contained (`out/` sources lack oleans for
cross-file imports): leaf `Base` bodies inlined, call structure
certified by `addCallerFwd_as_calls` / `sumCallerFwd_is_call`.
Acceptance met: `add_caller` + `sum_caller` corpus (real CIRGen output,
`cir-opt` VERIFY-OK) translates, `evalProgFunc_addCaller` /
`evalProgFunc_sumCaller` proved, golden diffs, `DiffCalls` fuzz vs
native (tamper-checked), `GoldenCalls` 7/7 (recursion, unknown callee,
misshapen caller, call-in-leaf, call-escape), `CHECK-OK`.

## S2. Struct-by-value — DONE (2026-09-27)

Finished staged `Base` (`Point`/`pointTranslate`) through
`Eval`/`Emit`: new `CExpr.fget` (field projection; `cir.get_member` +
`cir.load` fused) + `CExpr.pmk` (`Point` construction; stores + return
fused), `fieldLookup` + per-op lemmas (`evalExpr_fget_*`,
`evalExpr_pmk_*`, `evalExpr_add_fget_var` bridge), `Base`
`pointTranslate_err_y`, canonical `translateFunc` + `translateFwd`
with ok/err bridges, `evalFuncFuel_translate` (all paths, any fuel),
`FragKind.translate`, `matchFrag` struct arm (direct `⟨⟩` pattern —
no S1 list-literal quirk: `fget`/`pmk` take strings/exprs, not
lists), `isTranslateShape` gate before the `get_member` misshapen
branch, rendered `translate_fwd` delegating to `pointTranslate`,
golden `StructByValue.lean`.
Acceptance met: `tests/c/struct_by_value.c` (real CIRGen output)
translates, verifies, fuzzes clean (`DiffStruct`, tamper-checked);
old struct rejection golden replaced by `GoldenStruct.lean` 5/5
(wrong arity, struct + call, passthrough, `get_member` on
non-structs); `GoldenPhase4` struct check is now a pipeline
acceptance; `CHECK-OK`.

## S3. C integer + control-flow hardening

### S3a. Control flow — DONE (2026-09-27)

New `CExpr.umul` (wrapping unsigned `cir.mul`) + `CExpr.ueq`
(unsigned `cir.cmp eq`) with per-op lemmas; new `CStmt.break_` /
`CStmt.continue_` with loop-scoped `Outcome.broke` / `.continued`
(`seq` propagates, `while_` catches `broke`→exit /
`continued`→next-iteration, top-level escape is `AssertFail`) plus
fuel-level composition lemmas. Four canonical funcs with
`emit_correct`: `nested_sum` (nested fuel induction, cost
`(n-k)*(m+1)`), `skip_sum` (`break` caps iterations at 9, so
default-fuel correctness is unconditional), `find_eq` (early return;
hit/miss loop theorems, over-long lengths `OOB` unless an early hit
fires), `cls` (`cir.switch` lowered to an if-chain, loop-free).
`matchFrag` arms use `body`-level matching throughout (deep `.seq`
patterns inside `⟨⟩` hit the S1 equation-compiler quirk).
Validator: `isNestedShape` / `isSkipShape` / `isFindEqShape` /
`isClsShape` (exact const pins) + `noBreakContinueSwitch` exclusions
in all older shapes + line-aware `cir.br` check (it is a substring of
`cir.break`) + shape-aware `cir.switch` exemption.
Acceptance met: four corpus entries (real CIRGen output, `cir-opt`
VERIFY-OK) translate, verify, fuzz clean (`DiffFlow`,
tamper-checked); `GoldenFlow.lean` 10/10; `CHECK-OK`.

### S3b. Width generalization — DONE (2026-09-27, scoped: 64-bit loop-free)

`i64`/`u64` end to end on the loop-free add shapes; everything wider
than the slice rejects loudly. New `Value.i64`/`u64` +
`CLit.i64`/`u64`; `add`/`uadd`/`umul`/`ult`/`ueq` dispatch on the value
tags (mixed widths are `AssertFail`) with per-op 64-bit lemmas;
`Base` gains `checkedAddI64` (+ range/ok/err/value/comm lemmas
mirroring 32-bit) and `cir_simp` includes it. Canonical `add64Func` /
`addu64Func` with `emit_correct` (+ ok/err corollaries for `add64`),
`FragKind.add64`/`addu64`, `matchFrag` arms, rendered `add64_fwd` /
`addu64_fwd`. Validator: `isAdd64Shape` / `isAddu64Shape` (exact
`!s64i`/`!u64i` pins), `nsw`-less signed-64 arithmetic folded into the
per-line wrapping check, dedicated 8/16-bit promotion rejection
(CIRGen lowers small widths through `i32` casts — probed — so there is
no native small-width arithmetic to model).
Acceptance met: two corpus entries (real CIRGen output, `cir-opt`
VERIFY-OK) translate, verify, fuzz clean (`DiffWidth` with
`INT64_MIN`/`MAX`/`UINT64_MAX` boundaries, tamper-checked);
`GoldenWidth.lean` 5/5 (width-mix, missing-`nsw`, promotion);
`CHECK-OK`.
Remaining widths work (deferred): small-width casts, 64-bit
loops/arrays/heap/structs, `checkedNeg`/`Div` at 64 bits, unifying the
32/64 checked-op lemmas behind one width parameter.

## S4. Tactics stage 1 + spec skeletons (parallelizable after S1)

Grow `cir_simp` (call-unfold, struct-field, wider-width, vec rules;
`Result`-bind automation) and land `out/*_Spec.lean` stubs:
signature + body reference + edge list + prop-test entry.
Acceptance: each golden has a `_Spec.lean` stub that typechecks;
`VERIFYING.md` example uses a generated stub; at least one existing
spec (`sum` or `vec`) refactored onto the new `cir_simp` set with a
shorter proof.

## S5. Tactics stage 2: loop + fuel + forward/backward helpers

Loop-invariant helper (reuses fuel-induction pattern from
`emit_correct_sum`/`_vec`), fuel automation (`n ≤ EVAL_FUEL`
discharge), forward/backward `choose` reasoning. No new subset.
Acceptance: `sum`/`vec` emit-correctness proofs shorten or gain a
shared induction helper; documented in `VERIFYING.md` with before /
after.

## Mid-term (after short-term solid)

- **M1 — Heap generics**: `Vec<T,w>`, multiple live allocations,
  `realloc`, looser `free` discipline. Each needs shape +
  `emit_correct` + golden before admission.
- **M2 — STL-free C++-lite**: value constructors/destructors,
  methods on POD, `new`/`delete` as ownership ops. Still no
  inheritance/templates/EH/vtables. Structs (S2) are the prerequisite.
- **M3 — Shrinking oracle trust**: Stacked-Borrows-style
  justification (`oracle_noalias f → memEval f = Eval f` on the
  admitted fragment), trust base down to CIRGen text + Lean/Mathlib.
  Until then: verdicts checked in, differential testing P0, validator
  conservative.
