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

`string_view` range-for. N2c opportunistically wherever a
missing-attr rejection blocks an otherwise-amenable corpus entry.

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
