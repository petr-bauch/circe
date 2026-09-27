# Circe — Roadmap: short-term plan + mid-term notes

Mid-term goal: non-aliasing C/C++ code, more syntax, tactics that
simplify working with the Lean versions, scaffolding for simple
verification of the input programs on the Lean side.

Short-term scope (locked 2026-09-27): C + struct-by-value only,
calls first, `cir_simp` now + DSL next, spec skeletons in
`out/*_Spec.lean`.

## S0. Docs slim + harness rename (this change)

Replace phase-history docs with `OVERVIEW / SUBSET / PIPELINE /
VERIFYING / ROADMAP` (+ `PINS.md` kept). Archive `PLAN.md`,
`CIR_SUBSET.md`, `OWNERSHIP.md`, `SEMANTICS.md` to `docs/archive/`.
Rename `tools/check-phase7.sh` to `tools/check.sh` as the single
superset entry (thin wrappers kept for compat if needed).
Acceptance: `lake build` green, `tools/check.sh 100` green,
no references to removed docs from Lean comments required for build
(follow-up cleans comments).

## S1. Multi-function + `cir.call` (first syntax priority)

DAG-only calls, `Result`-bind translation. Callee `fwd` becomes a
Lean call; caller threads `←` binds; `emit_correct` composes per
callee lemmas. Recursion / mutual recursion / function pointers
rejected with dedicated messages.
CoreIR: `CStmt.call` gains real semantics (today a stub);
`Eval` threads env + fuel across the call; `matchFrag` admits
call-graph shapes with pinned callee names; `validate` checks
acyclicity + callee admitted + signature match.
Acceptance: two-function corpus (e.g. `add` caller + `sum` caller)
translates, `emit_correct_call` proved, golden pair diffs,
`Diff` fuzz vs native covers cross-function values, rejection
goldens for recursion + unknown callee.

## S2. Struct-by-value

Finish staged `Base` (`Point`/`pointTranslate`) through
`Eval`/`Emit`: `cir.get_member` semantics, field-wise updates as
values, `matchFrag` struct arm, golden `StructByValue.lean`.
Acceptance: `tests/c/struct_by_value.c` translates instead of
rejecting, verifies, fuzzes clean; struct rejection golden removed
/ replaced by misshapen-struct rejection.

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
