# Circe — Roadmap: where we are + where next

Long-term goal: a viable verification platform for modern C++ —
the subset of C++ amenable to Aeneas-style translation to Lean,
with tactic and spec support for proving properties of the emitted code.

State (2026-10-28): all delivered milestones live in `DELIVERED.md`.
Work going forward is organized under four pillars; each slice
still follows the standing convention below.

## Pillar 1 — Completeness of C support

Delivered: the C pipeline with proved memory transfer (M3a–M3c),
C control-flow hardening (S3a), 64-bit widths (S3b), arithmetic +
switch gaps (N6), and the lifetime-evidence work (L1–L3
extract-only — scope/alloca tree, live ranges, content roots;
L4 second sequential-writer admission; L5 verdicts — regions
vestigial-by-design, L3 roots extract-only), and the
ChaCha20-stream guiding program (K6: `chacha20_encrypt`
admission + full proof + input-OOB proof twins for short
key/nonce/message; `LoopOob` short-read-loop bricks shared
by the xor regimes). The C core is
complete within the standing non-goals.

Next: nothing open — the C core is complete within the
standing non-goals (L-track closed; `optional::value` throw
path closed, general `cir.try` stays out). Iris policy moved
to pillar 4 (native first, Iris on fallback). See
`DELIVERED.md` §§ M3/N1, S3, N6, L–L5, O1/O2, Iris, P4, K6.

## Pillar 2 — STD for C++ (leet-code sized algorithms)

Delivered slices (full reports in `DELIVERED.md`): merge-drain
specs (P2-M1); the `std::vector` algorithm run — out-of-place
checked transform (P2-M2), in-place Lomuto partition (P2-M3),
iterative selection sort (P2-M4) with its
sortedness/permutation contract (P2-M5); earlier: STL-free
C++-lite admission (M2a–M2c), proved transfer (M3d),
`string_view`-ended loop + `ElementRef` family composers (N7),
insertion sort over `std::array` (N9), binary search (V1),
two-sum (V2), checked `at()` store (W), out-of-place merge
kernel (M), bottom-up merge sort (C), reverse (R), segment
reverse (S), rotate (T), crypto over `std::array`
(K1–K5), maximum-subarray scan (Kadane), and the G-track vector
idioms — visited-mark fold (G1, incl. char-width G1b), flat-2D
index read (G2), cursor-stack push kernel (G3), reserve-upfront
iterative DFS (G5a), caller-grown-stack DFS (G4, incl. the
slot-reuse discipline and the push-lemma proof refactor). The
rule-of-three tactic harvest (P3-T2) lives with the pillar-3
entries. Discipline throughout: caller-owned buffers (pre-sized,
or caller-grown past the high-water mark as in G4), loud misses
(native exit 4), caller-debt side conditions, tamper-checked
diff fuzz.

Next:
(none — the selection-sort, partition, merge-sort, and quicksort
stacks are closed, as are the Kadane scan and the G-track
(G1/G1b/G2/G3/G5a/G4); see `DELIVERED.md` §§ P2-M5–P2-M8,
Kadane, G1, G1b, G2, G3, G5a, G4)

Proposed (toward the platform goal — for approval, in order):
(none approved yet; next P2 slice TBD — candidates under
discussion, none committed)

## Pillar 3 — Human-readable/writable proofs

Delivered (all re-verified against the repo 2026-10-25;
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

Next: open triggers only. `LoopOob` bricks
(`whileErr_of_bodyErr`, `whileStep_of_bodyOk`, `iterGuardT`)
at two uses (message-first/keystream-first xor regimes); a
third short-read-loop use earns graduation (documented
pattern vs tactic audit). Rule-of-three harvesting: third
checked-add arity (audit #3), third user-goal transfer-leg use
for a `cir_transfer_leg`-shaped tactic (audit #4), third
countdown-loop shape for fuel arithmetic (audit #5) and for
the unfold-loop-`show` tactic (R/S are two uses);
R memory-threading stays prose at first use; third lockstep
use earns a tactic; first triple-level store customer earns a
rule; a fully framed spine waits for an actual multi-cell
caller (P2-M2 was one — delivered). The trailing `return_` still
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

Standing policy (locked 2026-10-23): native first, Iris
on fallback. Every problem gets the simple no-Iris solution
attempt first; Iris is attempted only when that solution does
not work. History: the 2026-10-12 spike evaluated `iris-lean`
(MoSeL proof interface only) and recommended no migration —
pin mismatch (`v4.21.0` vs our `v4.34.0`), moving `Qq`
(`DELIVERED.md` "Iris spike report"); the revisit trigger
FIRED on 2026-10-16 (N14/G3 + L1/L3 — "L5") but the decision
was DEFER (F2: two helpers + two theorems). Deferral ended
2026-10-23 by decision: Phase 0 re-checked the blockers in a
fresh time-boxed spike (all gone — `v4.34.0` release tag,
identical `Qq`/`Batteries` pins; "P4 Phase 0") and Phase 1
vendored iris (MoSeL only) with a working frame rule
("P4 Phase 1"). It still replaces neither the oracle nor the
`Mem` tags.

Use cases encountered so far, with dispositions:

- Conditional framing (`alias_cond`): the one case needing
  framing beyond equational specs. Delivered natively —
  per-arm frame via `memFind_memStore_other`,
  `condPost_disjoint` / `condPost_aliased` (F2),
  verdict-independent admission with `pinnedCell` +
  `mstore`/`mload` + 4-leg transfer (N14/G3). Native cost:
  each new conditional shape re-pays a bespoke `condPost`
  proof. A *second* conditional shape is the first fallback
  candidate: attempt the bespoke `condPost` natively, escalate
  to the Iris frame rule only if that fails.
- Sequential reborrows (two loans, one address): licensed
  gate-side (L2 ranges + F0 same-address), functionalized
  value-in/value-out — no framing logic needed (N11/F1, L4).
  Overlapping loans stay a non-goal.
- Disjoint writer pairs (`__restrict__` + `noalias` verdict):
  disjointness-by-construction, empty footprints, aliased
  caller = caller-UB — no framing logic needed (N12/G2).
- Statement-level frame kit: `cellAt`/`cellsAt` + store and
  read-back lemmas (promoted to `Mem/Agree`),
  `memFind_memStore_other`, framed `cellsAt` (first
  multi-block customer: P2-M2); sharing-frame call kit
  (P2-M1c). No customer yet for triple-level store rules:
  loops with stores contain calls, so they live at prog
  level (H1 cell-kit audit).
- Hoare triples as thin sugar: skip/seq/consequence/if/while/
  let + program-level seq/call/call-frame rules, exercised by
  per-shape galleries (H0–H3, P3a–e). No new semantics;
  helpers stay first-order with explicit premises, no grand
  whole-while abstraction. Program-level call frame is
  definitional (callee binds into `emptyMem`) — P3e.
- `Mem`-level writes: delivered via `mstore`/`mload` + open
  contracts (S0–S4, N14); store equations stay hypotheses
  under the S0 open contract instead of discharged writes
  (discharging them through the Iris points-to is the
  standing fallback candidate).

What Iris (MoSeL) now provides: a reusable frame rule
carrying untouched locations through for free
(`frame_memStore` over reified `Mem`, Phase 1 MVP) +
BI/separation-logic tactics over our instance. First
consumers under the fallback policy: a second conditional
shape that resists the bespoke-`condPost` treatment, or a
`Mem`-level write need the native path cannot meet (the S0
store-equation hypotheses are the standing candidate).

Out of scope until the platform says otherwise: concurrency
(standing non-goal) — the one use case with no native answer.
If concurrency ever enters scope, the Iris revisit becomes
mandatory rather than optional: invariants and ghost state
have no equational counterpart.


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
  deferred with limitations note; deferral ended 2026-10-23 —
  "P4 Phase 0" / "P4 Phase 1", policy in pillar 4).
- L-track extractions + consumers (L–L5) — `DELIVERED.md` "L." / "L4." / "L5.".
- F2 native conditional framing + S0–S4/G1 dispositions —
  `DELIVERED.md` "F2." / "S0–S4 + G1 dispositions".
- K1–K6 crypto programs — `DELIVERED.md` "K." (summary; details
  under each K header).
- All N/H/A/B/M/V/W/C/G/S/T slices — `DELIVERED.md` under
  their headers (vector run V1/V2/W/M/C under N7; R/S/T own
  sections; G2/G2b/G3 under N12–N14).
- P3a/b program-level rules + Frontend + U1–U3 + T1 + P3c/d/e
  + H1 — `DELIVERED.md` under their headers.
- Kadane max-subarray scan, G-track vector idioms
  (G1/G1b/G2/G3/G5a/G4), G4 push-lemma refactor —
  `DELIVERED.md` §§ Kadane, G1, G1b, G2, G3, G5a, G4, G4
  refactor (the G-track slice labels are distinct from the
  Gate rule G-labels cited under N12–N14).
