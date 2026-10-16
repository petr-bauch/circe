# Circe — Roadmap: where we are + where next

Long-term goal: a viable verification platform for modern C++ —
the subset of C++ amenable to Aeneas-style translation to Lean,
with tactic and spec support for proving properties of the emitted code.

State (2026-10-16): all delivered milestones live in `DELIVERED.md`.
Work going forward is organized under three pillars; each slice
still follows the standing convention below.

## Pillar 1 — Completeness of C support

Delivered: the C pipeline with proved memory transfer (M3a–M3c),
C control-flow hardening (S3a), 64-bit widths (S3b), arithmetic +
switch gaps (N6), and the lifetime-evidence extractions (L1–L3,
extract-only — scope/alloca tree, live ranges, content roots;
`validate`/`Emit`/transfer untouched). The C core is complete
within the standing non-goals.

Next:
- L-track consumers: N4b real region numbers, and writer admission
  (needs a writer `Func` + Iris framing — the F1 follow-up residue).
- Deferred probe still open: `optional::value` lowers to `cir.trap`
  (throw path); deferral pins live in the `Golden*` suites.

## Pillar 2 — STD for C++ (leet-code sized algorithms)

Delivered: STL-free C++-lite admission (M2a–M2c) with proved
transfer (M3d); `string_view` range-for + `reserve`/`insert`/`erase`
composers (N7); insertion sort over `std::array` (N9, with
Sorted/Permutation spec); the `std::vector<int>` algorithm run —
binary search (V1), two-sum (V2), checked `at()` store (W),
out-of-place merge kernel (M), bottom-up merge sort with
calls-in-loop-bodies (C); crypto programs over `std::array`
(K1–K5: u32 bitwise leaves, buffer-xor, quarter-round, ChaCha20,
SHA-256 vs KATs). Discipline throughout: pre-sized caller-owned
buffers, loud misses (native exit 4), caller-debt side conditions
(sortedness), tamper-checked diff fuzz.

Next: further `std::vector` algorithm shapes and broader STD
coverage, one admission-shaped slice at a time — speculative STD
stays out (see non-goals). Multi-output support (G2/G2b/G3:
`wr_pair`, `cond_pair`, `alias_cond`) unblocks accumulate-style
and multi-writer algorithms.

## Pillar 3 — Human-readable/writable proofs

Delivered: proof ergonomics (N5: `cir_fuel`, fuel-bound lemmas,
per-step cascades), proof scale-down (N8: `cir_eval_closed`),
Hoare rule library + galleries (H1–H3, A, B — 8 closed-instance
`hoare-gallery` jobs), micro-tactics with adoption gates (N5a/N5b),
strategy capture (`notes/proof-patterns.md`, `VERIFYING.md`
galleries), and generator tooling (`tools/GenOut.lean`,
`tools/GenMatch.lean`).

Next: a gallery per new admitted shape; tactic harvesting by the
rule of three (prose note on first use, Lean tactic on third —
`fuel_step_down` earned it); Hoare-loop/frame rules as new
constructs arrive (calls-in-loops is the current frontier).

## Guiding principle (locked)

Admit exactly the C++ that is amenable to Aeneas-style
translation — value semantics + affine tokens, lifetime
discipline visible in CIR text (`restrict`/`noalias` attrs, the
C++ single-ref triple, `malloc`/`new` freshness, call multisets,
`cxx_ctor`/`cxx_dtor` markers). Everything else rejects loudly
with a dedicated message. Each slice follows the standing
convention: corpus (real CIRGen, `cir-opt` VERIFY-OK) → shape
gate → proof → golden diff → tamper-checked `Diff*` fuzz →
rejection suite → `check.sh` stage → `CHECK-OK`.

## Standing non-goals (platform-level)

Inheritance/vtables, exceptions, RTTI, concurrency, allocators,
iterator invalidation reasoning beyond length-paired discipline.
Proof-search, SMT backends, and `validate`/`emit` semantics
changes stay out.

## Delivered reports (moved to `DELIVERED.md`)

- Iris spike (MoSeL evaluation, no migration) — `DELIVERED.md`
  "Iris spike report".
- L-track L1/L2/L3 extractions — `DELIVERED.md` "L.".
- F2 native conditional framing + S0–S4/G1 dispositions —
  `DELIVERED.md` "F2." / "S0–S4 + G1 dispositions".
- K1–K5 crypto programs — `DELIVERED.md` "K." (summary; details
  under each K header).
- All N/H/A/B/M/V/W/C/G slices — `DELIVERED.md` under their
  headers.
