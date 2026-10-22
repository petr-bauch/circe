# Circe — Roadmap: where we are + where next

Long-term goal: a viable verification platform for modern C++ —
the subset of C++ amenable to Aeneas-style translation to Lean,
with tactic and spec support for proving properties of the emitted code.

State (2026-10-21): all delivered milestones live in `DELIVERED.md`.
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

Next: nothing open — the C core is complete within the
standing non-goals (L-track closed, Iris revisit deferred with
a limitations note; `optional::value` throw path closed,
general `cir.try` stays out). See `DELIVERED.md` §§ M3/N1, S3,
N6, L–L5, O1/O2, Iris.

## Pillar 2 — STD for C++ (leet-code sized algorithms)

Delivered: STL-free C++-lite admission (M2a–M2c) with proved
transfer (M3d); `string_view` range-for + `reserve`/`insert`/`erase`
composers (N7); insertion sort over `std::array` (N9, with
Sorted/Permutation spec); the `std::vector<int>` algorithm run —
binary search (V1), two-sum (V2), checked `at()` store (W),
out-of-place merge kernel (M), bottom-up merge sort with
calls-in-loop-bodies (C), in-place countdown reverse with
stores-in-loop (R), range-bounded segment reverse reusing the
R loop (S), loopless rotate-by-three-reversals over the
admitted seg entry (T); crypto programs over `std::array`
(K1–K5: u32 bitwise leaves, buffer-xor, quarter-round, ChaCha20,
SHA-256 vs KATs). Discipline throughout: pre-sized caller-owned
buffers, loud misses (native exit 4), caller-debt side conditions
(sortedness), tamper-checked diff fuzz.

Next: further `std::vector` algorithm shapes and broader STD
coverage, one admission-shaped slice at a time — speculative STD
stays out (see non-goals). Multi-output support (G2/G2b/G3,
`DELIVERED.md` §§ N12–N14) unblocks accumulate-style and
multi-writer algorithms.

Proposed (toward the platform goal — for approval, in order):
- P2-M1: merge-drain specs — the missing `mergeRuns` callee
  contracts named as U3 material. M1a DONE 2026-10-21 (14 U2
  contracts in `Specs.lean`: ok + per-site err legs for main /
  both drains by fuel induction, threading trio for the entry).
  M1b DONE 2026-10-22 (mem-level entry transfer: bind lemma,
  body mirrors, loop inductions, general-caller-memory entry).
  M1c DONE 2026-10-22 (closed sort-segment spine: sharing-call
  frame, seg/outer mirrors with pin threading, whole-function
  entry). No new admission; pure verification debt.
- P2-M2: out-of-place transform kernel (read-only input,
  checked-op written output) — first multi-block framed proof
  (`cellsAt` + framed `cellsAt`, an H-kit customer) and the
  accumulate-adjacent shape G2 unblocked. One admission pin.
  DONE (`d555844`, gate 433/433).
- P2-M3: in-place partition (forward scan with stores) — a new
  loop shape beyond countdown/rotate, and the third data point
  for the fuel-arithmetic (audit #5) and loop-tactic triggers.
  One admission pin.
  DONE (`5c941c7`, gate 438/438).
- P2-M4: iterative selection sort (`min_index` leaf + outer
  scan-and-swap entry, calls in the loop body via the M1c kit) —
  the second vector sort (quicksort stays out: the gate rejects
  recursion) and the fourth loop-shape data point. One admission
  pin. WIP (M4a admission).
- P3-T2: rule-of-three harvest — fuel-arithmetic (audit #5) and
  loop-unfold tactics plus the transfer-leg audit (#4), converting
  the R/S/T/M3/M4 sites. Proof-only, no admission.
- P2-M5: vector sortedness/permutation specs (N9-tier, ported
  from array insertion sort to the partition/merge/selection
  kernels). Proof-only, no admission.

## Pillar 3 — Human-readable/writable proofs

Delivered (all re-verified against the repo 2026-10-21;
details in `DELIVERED.md` §§ N5, H1–H3, A, P3a/b/c/d/e,
Frontend, U1–U3, T1, H1): proof ergonomics (N5: `cir_fuel`, fuel-bound
lemmas, per-step cascades; N5a/N5b micro-tactics
`fuel_step_down` / `cir_step` with adoption gates), proof
scale-down (N8: `cir_eval_closed`), Hoare rule library +
galleries (H1–H3 incl. cond-pair, A, R/S/T swap-step — 12
closed-instance `hoare-gallery` jobs: 10 counted passes plus
the two `alias_cond` selector iterations), program-level while
rule (P3a: `HTripleProg` + `htripleProg_while_at`, R countdown
as a rule application), frontend MVP (`circe-emit` CLI +
`examples/hello/` lib + README For-users + `frontend-hello`
pin), user tactics (U1: five-tactic audit, `TacticsDemo` demos
as regression test, VERIFYING.md For-users; deliberate
negative: no `cir_simp` comm lemmas), modular-proof harness
(U2: contract template + three operators, ten annotated
instances, fan-out boundary), lemma packs (U3: P0 audit,
P1 `CheckedIx` extracted and consumed by R+S, P2 negative
recorded, P3 closed with no pack), fold-end tactic (T1:
`cir_fold_end`, six sites converted + `hello_fold_end`
demo), program-level composition (P3c/d/e: `seq_at`,
`callProg_at`, call frame rules, closed rotate prefix,
framed leaf), cell-kit promotion (H1: kit out of the
report-only spike into `Circe.Mem.Agree`), and generator
tooling (`tools/GenOut.lean`,
`tools/GenMatch.lean`). Strategy capture lives in
`docs/VERIFYING.md` (galleries, For-users, Contracts, Lemma
packs) — correction: the `notes/proof-patterns.md` path named
in an earlier revision never landed in the repo (no such file,
no git history); that material is session memory, not a repo
deliverable.

Next: open triggers only. Rule-of-three harvesting: third
checked-add arity (audit #3), third user-goal transfer-leg use
for a `cir_transfer_leg`-shaped tactic (audit #4), third
countdown-loop shape for fuel arithmetic (audit #5) and for
the unfold-loop-`show` tactic (R/S are two uses);
R memory-threading stays prose at first use; third lockstep
use earns a tactic; first triple-level store customer earns a
rule; a fully framed spine waits for an actual multi-cell
caller (P2-M2 would be one). The trailing `return_` still
needs the prog-level seq-return equation. A gallery per new
admitted shape, as always.
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
- S loop-proof deltas (second use of the R tactics, prose stage —
  still no Lean tactic per the rule of three): `++` walks
  outer-append first (left-nested appends); a `Nat` window bound
  named `hi` is shadowed by the `hi` lookup hypothesis from
  `obtain` — rename the bound to `hiW` at the statement; length
  rewrites go through `List.length_reverse` before window
  lengths; the swap-step triple ports premise-for-premise
  (`hoare_segSwap` mirrors `hoare_reverseSwap` — only the
  invariant, the length-word snapshot, and the `hfind` fact
  change). Third use (next admitted loop shape) earns the Lean
  tactics.

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
- All N/H/A/B/M/V/W/C/G/S/T slices — `DELIVERED.md` under
  their headers (vector run V1/V2/W/M/C under N7; R/S/T own
  sections; G2/G2b/G3 under N12–N14).
- P3a/b program-level rules + Frontend + U1–U3 + T1 + P3c/d/e
  + H1 — `DELIVERED.md` under their headers.
