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
  real-region-number wiring stays the other candidate). Follow-up
  DONE (2026-10-12): the admission predicate
  (`isSequentialReborrowShape`: structural pins + L2-ordered disjoint
  writer ranges, proved sound) wires into `validate` as deferred
  recognition — `alias_reborrow` rejects with the "sequential writers"
  message instead of the generic fragment fallthrough (still a
  rejection: writer admission needs a writer `Func` + Iris framing).
  Pinned by `ReborrowGate` (7/7).
- Next STD/C slice: two-reader pure admission — DONE (2026-10-12,
  N2d; see `DELIVERED.md`). Next candidate: `vector::at()`
  checked read — DONE (2026-10-12, N4d-iv-c; see `DELIVERED.md`).
  Follow-up: `vector::at()` checked sum — DONE (2026-10-12,
  N4d-iv-d; see `DELIVERED.md`). First writer admission — DONE
  (2026-10-12, F1/N11: sequential reborrows functionalized
  value in / updated value out, fused `x + 1 + 2` licensed by L2 +
  F0; overlapping writers stay Iris-track). Conditional framing
  spike — DONE (2026-10-12, F2 report-only: disjunctive post
  proved natively, MoSeL deferred, admission blocked on
  triple-output/scalar-store model gaps).
- G-track (multi-output `Func`): G1 pair carrier — DONE
  (model-only: `CExpr.pair` building `structVal "IPair"`
  with `Eval`/`Mem` arms + per-op lemmas mirroring `pmk`;
  fixed 2×i32 by the monomorphization precedent, no
  `validate`/`Emit`/golden churn). G2 restrict writer-pair
  admission — DONE (2026-10-13, N12: `wr_pair`, first consumer;
  `alias_cond` is NOT one — no pure `(p,q,c)→(p′,q′)` is sound
  for ordered writers under unknown aliasing; it needs the G3
  framing track — see `DELIVERED.md`). G2b branch-writer
  admission — DONE (2026-10-13, N13: `cond_pair`, the noalias
  twin of `alias_cond`; full unknown-verdict framing stays
  deferred pending a caller-side contract kind). G3-full
  framing S0 spike — DONE (2026-10-13, report only, /tmp
  scratch `wrprobe/s0open.lean`, no repo churn): verdict GO
  on a Mem-space open contract — a `Mem` program mirroring
  the cond body (`condExec`) with `cellAt` hypotheses
  inverts cleanly to per-cell posts under both verdicts
  (`condExec_invert_disjoint` needs gate `b ≠ a`;
  `condExec_invert_aliased` re-reads `p`'s write, second
  addition runs on the stored value, second store wins);
  artifact decision: Mem-space open contract, NOT OpenFunc
  (reuses `cellAt`/`memStore_cell`/`memFind_memStore_other`,
  executable via `memAllocData`, no new `Func`/render);
  binds collapse via `simp only [Bind.bind, Except.bind]`
  (`pure_bind`/`Except.bind` alone make no progress on
  `Except.ok`-scrutinee `let ←`).
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
(45/45) pins every corpus definition's locals, max depth, and live ranges — loop
indices sit one `cir.for` region deep, the nested-loop inner index
four opens deep (verified against `nested_sum.cir`; the reason the
inner index is re-initialized per outer iteration) — plus
truncated/malformed-input loudness. `validate`/`Emit`/transfer
untouched.

### L2. Live-range consumer — DONE (2026-10-12, extract-only; admission wiring follow-up)

Second consumer landed report-only: `ScopeReport` pins per-local
`(first-use, last-use)` line facts — `alias_reborrow` separates
(`r` last-use line 12 precedes `s` first-use line 14; the
`cir.load` copy-chain closure carries `r` through its final
store at file line 17) while `alias_cond` overlaps (`q` spans
lines 6–22 across `p`/`c` — framing stays Iris, see the spike
report above). Matching is region-aware (per-region SSA numbers
resolve inward-outward: the `cond`-region `%13` `n`-copy never
leaks into `a`/`n` ranges — found live mid-slice when flat
matching pinned `sum_two` `a`/`n` last-use 44 via the
after-region integer `%13`; unresolvable mentions count
conservatively for every root tracking the id). Only `cir.load`
copies are chased (stores create no aliases; `ptr_stride`
results are fresh values). Proved: first-use ≤ last-use and
last-use within the function extent. `validate`/`Emit`/transfer
untouched. The admission predicate (sequential writers with
`r.lastUse < s.firstUse`) was the follow-up slice — DONE
(2026-10-12): `hasSequentialWriterRanges` (exactly three scope
locals `[root, a, b]` with the first writer's range observed and
ending before the second begins) plus structural pins (`void`, one
single-reference root, three allocas, no calls/comparisons/loops/
cleanup/traps/globals/strides) form `isSequentialReborrowShape`,
proved sound (`hasSequentialWriterRanges_disjoint`,
`isSequentialReborrowShape_disjoint`: `true` yields recorded ranges
disjoint in order). `validate` routes recognized shapes to a deferred
"sequential writers" message (after every admission, so nothing
admitted is shadowed; the corpus sweep shows `alias_reborrow` is the
only match — `alias_cond` keeps the generic message). Full admission
still needs writer `Func` semantics + Iris framing; N4b
real-region-number wiring stays the other candidate consumer.

### L3. Content-root (loan/address) bridge spike — DONE (2026-10-12, extract-only, report-only)

F0 go/no-go input for the Iris framing track: can we resolve, from
`RawFunc.text`, which address each writer local holds at each point
(L2 gives WHEN, this gives WHERE)? Verdict: GO for F1, with the
framing gap for F2 made textual. New `Circe.Scope` extraction
(computed predicates, no `RawFunc` churn, `validate`/`Emit`/
transfer untouched): slot classes from the alloca ctype (`Ref` iff
the pointee is itself `!cir.ptr<...>` — the C++ reference lowering;
unparseable admits less as `Val`), `cir.store` operand parsing
(`%argN` vs `%M`, `align` skipped, destination must be an alloca id
so stores to computed addresses stay writes, never initializers),
exact copy-owner resolution through the L2 load-copy sets (no
conservative arm: ambiguous copies claim nothing), first-store init
pattern, fuel-bounded transitive ultimates. A `Slot` answer is an
address-identity claim and requires both ends `Ref` (value copies
through `Val` slots report `Unknown`, never an address link).
Proved: fuel-zero/param/unknown stability of `ultimateRoot`
(direct answers are fuel-independent). `ScopeReport` pins
(`SCOPEREPORT-OK` 45 → 60): `alias_reborrow` shares one address
(`r`/`s` → `slot:x` → `param0` — the F1 sequencing license in
waiting); `alias_cond` names DIFFERENT addresses (`p` → `param0`,
`q` → `param1` — caller-dependent footprints confirmed textually,
framing stays Iris); `sum_two` control resolves readers to different
params with value slots claiming nothing (`?`); copy-sets are
ambiguity-free (`uniqueCopies`) on all three. Known limits (sound
direction, all admit less): reassigned slots keep the first init;
value-operand inits (`const`/`add` results) and copy ambiguity
report `Unknown`; multi-region same-id collisions resolve
inward-outward per L2 (unresolvable counts conservatively in
use-facts but claims nothing here).

### F2. Native conditional-framing spike — DONE (2026-10-12, report-only, no admission)

The plan's MoSeL question, answered with evidence instead of
speculation: `Circe/CondFrame.lean` (87 lines, 4 theorems, no
`validate`/`Emit` churn — build-covered via a `Test/Driver`
import, no suite row) proves the `alias_cond` disjunctive post
natively over `Mem`. Per-arm frame reuses
`memFind_memStore_other` with the F0 addresses as hypotheses
(`p` → `param0`'s address, `q` → `param1`'s); one reusable helper
(`memStore_cell`: storing to a known live 1-word cell succeeds)
plus read-back (`memFind_cell_store`) discharge both write legs.
The aliasing split is explicit and BOTH sides are proved:
disjoint (`b ≠ a` — each arm frames the other block) and aliased
(single cell, branch-exclusive update, no framing needed — the
case the `unknown` verdict must also cover and a
star-conjunction would conflate). Burden: two helpers + two
posts, all first-try clean — manual `m`/`m₁`/`m₂` threading
throughout. Verdict: MoSeL vendoring DEFERRED — the native cost
for one conditional is small, and Iris would not unblock
admission anyway. Revisit trigger: a second conditional shape
(when frame threading recurs) or a B2-style shape needing
`Mem`-level writes. Full admission is blocked on two model gaps,
neither logical: (B1) triple outputs `(r, p', q')` are
inexpressible — `pmk` builds exactly a two-field `Point`
`structVal` (anything else is `AssertFail`), nesting fails, no
other struct-building expression exists; (B2) scalar writes
cannot land in `Mem` — no `CStmt` stores scalar blocks, so a
single-output `Func` with a `Mem`-writing transfer is equally
inexpressible (the read projection alone is NOT admitted — it
would silently drop the writes). Deeper consequence, now
evidence-backed: the functionalized pipeline (scalar mutation as
value-in/value-out + gate-side L2/F0 licenses, F1-style)
sidesteps Iris-style framing for scalars entirely — the frame
rule is proven but currently has no pipeline consumer. Next
track candidate: multi-output `Func` support (generalized struct
construction), which unblocks `cond` and all multi-writers and
subsumes B2's need.
