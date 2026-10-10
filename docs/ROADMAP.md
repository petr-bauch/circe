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
The active remainder is the Iris spike (report, not migration) and
the lifetime-evidence track (L1 extract-only delivered; no
consumers wired yet).

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

- Iris spike (time-boxed): the spike report below is still owed —
  evaluate `iris-lean` for heap reasoning, deliverable a report,
  not a migration.
- L-track consumers: L1 evidence is extracted and pinned, but no
  consumer is wired yet (first expected: real region numbers for
  N4b moves). Next slice wires one consumer or records why none
  is needed.
- Deferred probe still open: `optional::value` lowers to `cir.trap`
  (throw path); deferral pins live in the `Golden*` suites.
- Standing non-goals (platform-level): inheritance/vtables,
  exceptions, RTTI, concurrency, allocators, iterator invalidation
  reasoning beyond length-paired discipline. Proof-search, SMT
  backends, and `validate`/`emit` semantics changes stay out.

## Later directions — sketches (not planned)

- Iris spike (time-boxed): evaluate `iris-lean`
  (Lean 4 Iris port: MoSeL proof interface today, full-logic
  port deferred upstream — see
  `https://github.com/markusdemedeiros/iris-lean`; verify it
  builds at our toolchain pin) for heap reasoning. Questions:
  what would it replace (Mem tags? the oracle?) and where is
  the migration seam? Deliverable is a spike report, not a
  migration — no commitment until a concrete slice needs
  framing beyond equational specs.
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

## K. Verified crypto programs — PLAN (2026-10-10)

North star: the ChaCha20 block function over
`std::array<uint32_t,16>`, proved as emitted-forward-vs-executable-spec
agreement plus RFC 8439 known-answer vectors. Staged: K1 `u32`
bitwise leaves — DONE (`DELIVERED.md`); K2 buffer entries
(`mutBorrow` out-param + `sharedBorrow` in-params, tag-erased
buffer-result rendering, directed + fuzz KAT oracle leg) —
DONE (`DELIVERED.md`); K3 quarter-round-as-fold + QR KAT —
DONE (`DELIVERED.md`); K4 full block vs §2.3.2 KAT
(single-`&mut` state containment, no oracle change — the quarter
round is inlined because a 4-writer QR leaf could never pass the
pair check) — DONE (`DELIVERED.md`); K5 second primitive (SHA-256)
or written stop-decision. Non-goals: streaming/Poly1305, pointer
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
