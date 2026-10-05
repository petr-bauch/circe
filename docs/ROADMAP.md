# Circe — Roadmap: where we are + where next

Long-term goal: a viable verification platform for modern C++ —
the subset of C++ amenable to Aeneas-style translation to Lean,
with tactic and spec support for proving properties of the emitted code.

State (2026-10-05): C pipeline complete with proved memory transfer
(M3a–M3c); STL-free C++-lite admission complete (M2a–M2c) with proved
memory transfer (M3d); N2 (viability past noalias) complete; N3
(spec + tactic support) complete; N4a–N4d complete — overloads,
moves, templates, `array`/`optional`/`span` reads, `vector` reads,
`vector` growth leaves (N4d-iv-b1) and the full 53-def growth
composition (N4d-iv-b2: `_M_realloc_insert`, `emplace_back`,
`push_back`, `vec_push_sum` entry, 355 jobs TEST-OK, CHECK-OK).
Delivered milestones moved to `DELIVERED.md`. The active frontier is
`string_view` range-for (same iterator reason as the span range-for
pin); the lifetime-evidence track (L) is in progress.

Guiding principle (locked): admit exactly the C++ that is amenable to
Aeneas-style translation — value semantics + affine tokens, lifetime
discipline visible in CIR text (`restrict`/`noalias` attrs, the C++
single-ref triple, `malloc`/`new` freshness, call multisets,
`cxx_ctor`/`cxx_dtor` markers). Everything else rejects loudly with a
dedicated message. Each slice follows the standing convention:
corpus (real CIRGen, `cir-opt` VERIFY-OK) → shape gate → proof →
golden diff → tamper-checked `Diff*` fuzz → rejection suite →
`check.sh` stage → `CHECK-OK`.

### N4 remainder: `std::string_view` range-for

`string_view` range-for is `cir.scope` + `cir.for` with `begin`/`end`
as `get_member` projections; needs a probed lowering + a token/value
model before admission. Probes so far: `optional::value` lowers to
`cir.trap` (throw path, still deferred).
Deferral pins live in `tests/lean/GoldenArray.lean` (`optional`
graduated to `tests/lean/GoldenOptional.lean`, `span` index-sum
graduated to `tests/lean/GoldenSpan.lean`, `vector` reads
graduated to `tests/lean/GoldenVecRead.lean`, `vector`
growth leaves graduated to `tests/lean/GoldenVecGrow.lean`).

Non-goals (platform-level): inheritance/vtables, exceptions, RTTI,
concurrency, allocators, iterator invalidation reasoning beyond
length-paired discipline.

### Suggested order

N5 (proof ergonomics) → N6 (switch + arithmetic gaps) → N7
(`string_view` range-for; `reserve`/`insert`/`erase` follow-ups).
N2c opportunistically wherever a
missing-attr rejection blocks an otherwise-amenable corpus entry.
Iris spike runs alongside N5 (report, not migration).

## N5. Proof ergonomics — DONE (2026-10-05)

N4d-iv-b2 was the most proof-heavy slice so far: composer fuel
side-goals (`len + 2 ≤ F` emplace, `len + 3 ≤ F` push_back,
`6 ≤ F` closed entry, additive `.callProg` at depth `fuel - 1`),
bespoke Fwd-cascade `simp only [...]` sets per composer (plus
`Except.map` leftovers per the `Span.lean` precedent). Ergonomics
compounds across every later slice; S4/S5 precedent applies
(before/after shortening, `check.sh` adoption asserts, no new
trusted code, no validator/emit behavior change). Each slice below:
helper → re-shorten a b2 proof onto it → adoption assert →
`CHECK-OK`.

- N5a: composer fuel automation — generalize `cir_fuel` (S5) to
  composer fuel shapes: additive calls at `fuel - 1`,
  closed-entry constant bounds, `remaining ≤ F` side conditions.
  Target: the b2 fuel side-goals discharge with no manual
  `omega`/`have` lines.
- N5b: composer cascade registry — each proved composer registers
  its Fwd-cascade simp set once (`Except.map` normalization
  included); new entries close with the registry + N5a instead of
  bespoke simp lists.
- N5c: spec-stub obligations — per-slice proof obligations
  generated from the spec stub mirror (hole-shaped, discharged by
  hand), keeping the N3 gallery pattern as new forwards land.

Result: `fuel_step_down` lemma (one-`obtain` composer split, six
b2 sites adopted, negative driver gate `n5-no-manual-fuel-split`
forbids the manual pair); `cir_step` cascade macro (eight
span/read/entry steps adopted, `Except.map` by construction);
composer stubs name their owed gallery equations (`TODO (user)`,
pinned per stub in the driver). Suite green.

Non-goals: proof search, SMT backends, `validate`/`emit`
semantics changes.

## Later directions — sketches (not planned)

- N6: language gaps — N6a-i probes done (2026-10-05):
  negation is `cir.minus nsw`, (un)signed div/rem are `cir.div` /
  `cir.rem` with signedness from the type, sub/mul carry `nsw`,
  all single-op lowerings (64-bit div included, no libcall),
  VERIFY-OK. N6a-ii wires `neg` + `sdiv` (i32) with the
  pre-proved `checkedNegI32` / `checkedDivI32`. Probe fallout:
  multi-op functions validated to single-op bodies (P0 hole) —
  fixed family-wide with `arithOpCount == 1` in all six
  arithmetic leaf gates. N6a-iii done (2026-10-05): the unwired
  remainder (multi-op bodies, unsigned div/rem, signed
  sub/mul, shifts, bitwise, `nsw`-less minus) rejects through
  one catalog branch with per-cause messages (13/13
  `GoldenRejectCatalog`, `intClass` uniformity guard preserves
  the `wmix` routing); N6b probes done (2026-10-05): dense switches
  stay `cir.switch` at CIR level (no jump-table spelling — the if-chain
  covers all densities), fallthrough is an empty `cir.case` region,
  `break`-switches carry trailing code, case bodies can carry
  arithmetic. N6b-i done (2026-10-05): `cls_fall` (empty `case 0`
  into `case 1`) + `cls_dense` (`0`..`7` + `default`) as exact shapes
  with per-region const pins + `arithOpCount == 0` (closes the
  unsigned-arith-in-case-body hole and the permuted-const hole in the
  old whole-text `cls` pins; 15/15 `GoldenFlow`); N6b-ii (break-switch
  without default) and N6b-iii (compute bodies) remain.
- N7: STD growth — `string_view` range-for (shares the span
  iterator blocker: `begin`/`end` + pointer-chasing; needs a
  probed lowering + a token/value model), then
  `reserve`/`insert`/`erase` composers (`erase` needs
  memmove-down leaves; reuse the no-inlining `vecGrowProg`
  pattern).
- Iris spike (time-boxed, alongside N5): evaluate `iris-lean`
  (Lean 4 Iris port: MoSeL proof interface today, full-logic
  port deferred upstream — see
  `https://github.com/markusdemedeiros/iris-lean`; verify it
  builds at our toolchain pin) for heap reasoning. Questions:
  what would it replace (Mem tags? the oracle?) and where is
  the migration seam? Deliverable is a spike report, not a
  migration — no commitment until a concrete slice needs
  framing beyond equational specs.

## L. Lifetime-relevant evidence (extract-only) — PLAN (2026-10-03)

True lifetime intrinsics do not exist at this pin (raw CIRGen rejects
`-flifetime-markers`; no checked-in `.cir` mentions `lifetime`), and the
existing region/loan plumbing is vestigial (every `mutBorrow` region is
`0`; `LoanState` is never threaded). What raw CIRGen *does* carry is
lexical lifetime evidence — `cir.scope` nesting plus named `cir.alloca`
birth points — which the parser currently drops. This track extracts
that evidence with golden pins but wires no consumers until a slice
needs them (first expected: real region numbers for N4b moves). Each
slice follows the standing convention (corpus evidence → extraction →
proof → golden pins → `check.sh` stage → `CHECK-OK`), minus admission
(extract-only slices change no `validate` behavior by construction).

### L1. Scope/alloca tree — DONE (2026-10-04, extract-only)

New `Circe.Scope`: per-function `extractScopes` over `RawFunc.text`
(the `derivedNoalias` precedent — computed predicates, no `RawFunc`
churn): brace-depth fold with string-literal stripping (attribute
dicts cannot disturb the count), each `cir.alloca "NAME"` recorded at
its normalized depth (function top level = 0), scanning stops at the
first return-to-zero (the function extent), and `balanced = false`
makes miscounts loud (never entered, went negative, never closed).
Proved: `extractScopes_empty` + the depth-bound invariant
(`extractScopes_bound` via a fold-preservation lemma). `ScopeReport`
(29/29) pins every corpus definition's locals and max depth — loop
indices sit one `cir.for` region deep, the nested-loop inner index
four opens deep (verified against `nested_sum.cir`; the reason the
inner index is re-initialized per outer iteration) — plus
truncated/malformed-input loudness. `validate`/`Emit`/transfer
untouched.
