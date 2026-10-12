# Circe — Roadmap: where we are + where next

Long-term goal: a viable verification platform for modern C++ —
the subset of C++ amenable to Aeneas-style translation to Lean,
with tactic and spec support for proving properties of the emitted code.

State (2026-10-08): everything through N9 is delivered — C
pipeline with proved memory transfer (M3a–M3c); STL-free C++-lite
admission (M2a–M2c) with proved transfer (M3d); N2 (viability past
noalias); N3 (spec + tactic support); N4a–N4d (C++ syntax coverage
through the full 53-def `vector` growth composition); N5 (proof
ergonomics); N6 (arithmetic + switch gaps); N7 (`string_view`
range-for — the one range-for shape admitted so far — plus
`reserve`/`insert`/`erase` composers over the admitted N4d
`vector<int>` core); N8 (proof scale-down: closed-entry evals
collapsed behind `cir_eval_closed`); N9 (insertion-sort case study
over `std::array<uint32_t,4>` + the N=8 second monomorph:
corpus → gate → forward-as-fold →
transfer → Sorted/Permutation spec → `DiffSort` fuzz; 444 jobs
TEST-OK, CHECK-OK). Delivered milestones moved to `DELIVERED.md`.
The active remainder is the lifetime-evidence track (L1
extract-only delivered; no consumers wired yet).

Guiding principle (locked): admit exactly the C++ that is amenable to
Aeneas-style translation — value semantics + affine tokens, lifetime
discipline visible in CIR text (`restrict`/`noalias` attrs, the C++
single-ref triple, `malloc`/`new` freshness, call multisets,
`cxx_ctor`/`cxx_dtor` markers). Everything else rejects loudly with a
dedicated message. Each slice follows the standing convention:
corpus (real CIRGen, `cir-opt` VERIFY-OK) → shape gate → proof →
golden diff → tamper-checked `Diff*` fuzz → rejection suite →
`check.sh` stage → `CHECK-OK`.

## Next (all N slices through N9 delivered — see `DELIVERED.md`)

- Iris spike — DONE (2026-10-12, report only, no migration; see
  `Iris spike report` below).
- L-track consumers: first consumer landed report-only (L2 scoped
  above — admission wiring needs last-use analysis; N4b
  real-region-number wiring stays the other candidate).
- Deferred probe still open: `optional::value` lowers to `cir.trap`
  (throw path); deferral pins live in the `Golden*` suites.
- Standing non-goals (platform-level): inheritance/vtables,
  exceptions, RTTI, concurrency, allocators, iterator invalidation
  reasoning beyond length-paired discipline. Proof-search, SMT
  backends, and `validate`/`emit` semantics changes stay out.

## Later directions — sketches (not planned)

### Iris spike report — DONE (2026-10-12, report only, no migration)

Time-boxed evaluation of `iris-lean`
(`https://github.com/markusdemedeiros/iris-lean`) for heap
reasoning. No `validate`/`Emit`/transfer churn; no dependency
vendored.

- Build pin: `iris-lean` pins `leanprover/lean4:v4.21.0`
  (fetched 2026-10-12) against our `v4.34.0`, and tracks `Qq`
  on `git#stable`. It is not a direct lake dependency at our
  pin — adopting it means a separate v4.21 checkout or a port,
  plus pinning a moving `Qq`. No build attempted in this time
  box (vendoring would churn `lakefile.toml` + manifest for a
  report-only spike).
- Scope: MoSeL proof interface only; the full Iris logic port
  is deferred upstream with open problems. Even vendored, we
  would get BI/separation-logic tactics, not Iris program
  logic (invariants, ghost state, lifetimes).
- What would it replace: neither the oracle (M3b keeps
  verdicts as a checked cache) nor the `Mem` tags wholesale
  (disjoint-by-construction + single-`&mut` containment
  transfers stand). The seam is narrow: a framing layer over
  `Mem` blocks for exactly one residue class —
  conditionally-live writers (`alias_cond`), where the branch
  makes footprints caller-dependent and equational specs
  cannot frame. Everything else stays equational: single-`&mut`
  containment (K2/K4/K5), two-`malloc` disjointness (M1a),
  recovered readers (N2c), and the cheap-rule candidates
  (reader pairs, closed two-alloca shapes, free single-`&mut`
  writers — shape admissions, per the alias-oracle routing
  below).
- Recommendation: no migration. Revisit when a slice admits
  `alias_cond`-class framing; that slice must also solve
  lifetime evidence (raw CIRGen carries no lifetime markers —
  see the L-track), since framing without live-range facts has
  nothing to attach to.
- Alias-oracle boundary evidence (A-track probe,
  `tests/lean/GoldenAliasProbe.lean`, `GOLDENALIASPROBE-OK` 12:
  2 admit controls + 10 reject rows over real CIRGen corpus in
  `tests/cpp/alias_*.cpp`). Decision procedure pinned:
  rule-1 param check → verdict gate → pair check → shape arms.
  Findings: a `noalias` verdict confirms `__restrict__` attr
  claims but never substitutes for missing attr text (plain
  pair rejects identically under `unknown` and `noalias`);
  two `noalias` readers still reject at the pair check (no
  multi-reader `Func` admitted); triple-param cases
  (`reborrow`, `cond`, `readonly_pair`, free `incr_ref`) pass
  the oracle vacuously and reject at the shape gate — lexical
  death and conditional liveness are invisible without
  lifetime markers. Zero false-accepts. Residue routing: (i)
  conditionally-live writers (`alias_cond`) are the one case
  needing framing beyond equational specs — first concrete
  Iris-spike input; (ii) sequential reborrows (`alias_reborrow`)
  want an L-track consumer (scope-death evidence over L1);
  (iii) `noalias` reader pairs, closed two-alloca shapes, and
  free single-`&mut` writers are shape admissions (cheap-rule
  candidates), not oracle or Iris problems.

## K. Verified crypto programs — DONE (see `DELIVERED.md` K1–K5)

North star met: ChaCha20 block over `std::array<uint32_t,16>`
(emitted-forward agreement + RFC 8439 KATs) plus a second
primitive (SHA-256 compress vs FIPS 180-4 §8.1.1 "abc" KAT),
both under single-`&mut` containment with no oracle change.
Standing non-goals: streaming/Poly1305, pointer
idioms, heap, Iris, speculative STD. C++-lite only (`std::array`).

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

### L2. Live-range consumer — SCOPED (admission wiring needs last-use analysis)

First consumer landed report-only (2026-10-12): `ScopeReport`
pins `alias_reborrow` (`x`/`r`/`s`, all depth 0) and `alias_cond`
(`p`/`q`/`c`, all depth 0) identically — L1 birth-depth evidence
cannot separate sequential reborrows from conditionally-live
writers (no `cir.scope` around `r`/`s`; use-site scan required).
So no admission consumer is possible yet: reborrow admission
needs last-use/death facts L1 does not extract, and `alias_cond`
framing needs Iris (see the spike report above). N4b
real-region-number wiring stays the other candidate consumer.
