# Circe — Roadmap: where we are + where next

Long-term goal: a viable verification platform for modern C++ —
the subset of C++ amenable to Aeneas-style translation to Lean,
with tactic and spec support for proving properties of the emitted code.

State (2026-10-16): all delivered milestones live in `DELIVERED.md`.
Work going forward is organized under four pillars; each slice
still follows the standing convention below.

## Pillar 1 — Completeness of C support

Delivered: the C pipeline with proved memory transfer (M3a–M3c),
C control-flow hardening (S3a), 64-bit widths (S3b), arithmetic +
switch gaps (N6), and the lifetime-evidence work (L1–L3
extract-only — scope/alloca tree, live ranges, content roots;
L4 second sequential-writer admission; L5 verdicts — regions
vestigial-by-design, L3 roots extract-only). The C core is
complete within the standing non-goals.

Next:
- L-track is closed (L4/L5); the Iris revisit trigger fired on
  both legs 2026-10-16 and the revisit is DEFERRED with a
  limitations note — see `DELIVERED.md` "Iris spike report".
- `optional::value` throw path closed (O1/O2, 2026-10-16):
  guarded `.value()` admitted (checked leaf + throw helper +
  guarded entry), unguarded rejects loudly; general `cir.try`
  semantics stay out per standing non-goals.

## Pillar 2 — STD for C++ (leet-code sized algorithms)

Delivered: STL-free C++-lite admission (M2a–M2c) with proved
transfer (M3d); `string_view` range-for + `reserve`/`insert`/`erase`
composers (N7); insertion sort over `std::array` (N9, with
Sorted/Permutation spec); the `std::vector<int>` algorithm run —
binary search (V1), two-sum (V2), checked `at()` store (W),
out-of-place merge kernel (M), bottom-up merge sort with
calls-in-loop-bodies (C), in-place countdown reverse with
stores-in-loop (R); crypto programs over `std::array`
(K1–K5: u32 bitwise leaves, buffer-xor, quarter-round, ChaCha20,
SHA-256 vs KATs). Discipline throughout: pre-sized caller-owned
buffers, loud misses (native exit 4), caller-debt side conditions
(sortedness), tamper-checked diff fuzz.

Next: further `std::vector` algorithm shapes and broader STD
coverage, one admission-shaped slice at a time — speculative STD
stays out (see non-goals). Multi-output support (G2/G2b/G3:
`wr_pair`, `cond_pair`, `alias_cond`) unblocks accumulate-style
and multi-writer algorithms.
- Next Pillar 2 target: range-bounded in-place algorithms —
  segment reverse over `(lo, hi)` DONE (2026-10-17, S slice:
  window invariant `SegInv`, reused R loop body, `vecSet`
  lockstep), then rotate-by-three-reversals DONE (2026-10-18,
  T slice: loopless triple entry-over-entry composition over
  the admitted seg entry — one new admission pin, one
  admission-shaped slice at a time).

## Pillar 3 — Human-readable/writable proofs

Delivered: proof ergonomics (N5: `cir_fuel`, fuel-bound lemmas,
per-step cascades), proof scale-down (N8: `cir_eval_closed`),
Hoare rule library + galleries (H1–H3, A, B, R swap-step — 9
closed-instance `hoare-gallery` jobs), micro-tactics with adoption
gates (N5a/N5b), strategy capture (`notes/proof-patterns.md`,
`VERIFYING.md` galleries), and generator tooling
(`tools/GenOut.lean`, `tools/GenMatch.lean`).

Next: a gallery per new admitted shape; tactic harvesting by the
rule of three (prose note on first use, Lean tactic on third —
`fuel_step_down` earned it); Hoare-loop/frame rules as new
constructs arrive (countdown loops with calls + stores are now
admitted by C/R — the while/frame rules are the frontier).
- R loop-proof tactics (first use, prose-note stage): one-sided
  reference unfolding (`conv => lhs; unfold <ref>`, then `show`
  past the `let`-bound scrutinee so `rw` sees the `get?`
  patterns); plain-`if` reduction
  (`simp only [.., h, ite_true/ite_false]`); length-dite
  discharge (`dite_eq_left`); closed bool-guard discharge
  (`ite_eq_right (by decide ...)`); prefer the non-deprecated
  `ite_eq_left/right` over `if_pos/if_neg` in new code.
- R memory-threading pattern (first use, prose-note stage):
  `vecSet` lockstep via closed-form `memStore` on the reified
  snapshot (`revMemStore_ok`), shadowing blocks tracked by-find
  (`memFind_cons_hit`), length-word skip via
  `List.set_cons_succ`; calls communicate by value, so the caller
  `(m, π)` threads through `callRet` unchanged and only `vecSet`
  steps extend the block list.
- Program-level while-rule (scoped 2026-10-16, implementation
  pending): `htripleProg_while_at` mirrors `htriple_while_at`
  over `memEvalProgStmt` (same four premises — guard-false at
  zero, exit, guard-decidable, triple-step). Every premise maps
  to a named R lemma; the R invariant needs a fuel-indexed
  wrapper (`revIters i j = k ∧ RevInv …`) since the rule counts
  fuel down. Needs `HTripleProg(At)` promoted to `Circe/Hoare`
  from the gallery before implementation.

## Pillar 4 — Iris separation logic for low-level aspects and concurrency

To be scoped.


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
  "Iris spike report" (trigger fired 2026-10-16, revisit
  deferred with limitations note).
- L-track extractions + consumers (L–L5) — `DELIVERED.md` "L." / "L4." / "L5.".
- F2 native conditional framing + S0–S4/G1 dispositions —
  `DELIVERED.md` "F2." / "S0–S4 + G1 dispositions".
- K1–K5 crypto programs — `DELIVERED.md` "K." (summary; details
  under each K header).
- All N/H/A/B/M/V/W/C/G slices — `DELIVERED.md` under their
  headers.
