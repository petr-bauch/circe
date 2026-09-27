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

Generalize `i32`-only / `u32`-only proofs to the `i8–i64`/`u8–u64`
family (checked-op table + width-parameterized lemmas; `Vec<T,w>`
design sketched but not required), and harden `break`/`continue`,
early return, nested loops, `switch`-as-if-chain lowering check.
Acceptance: width-parameterized corpus entries + loop-nesting
goldens, no `sorry`, fuzz covers boundary values per width.

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
