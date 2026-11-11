<p><div style="text-align: center">
<img src="static/circe.jpg" alt="circe" width="240">
<figcaption>
Circe Invidiosa, John William Waterhouse, 1892
</figcaption>
</div>
</p>

CIR → Lean 4 verification pipeline for C and STL-free C++-lite, Aeneas-style:
source → ClangIR (CIR, raw `CIRGen` output) → pure, memory-free Lean 4
via a verified emitter, with functional-correctness proofs as pure
equations. No memory model, no separation logic in the common case; a
proved memory transfer (`Circe.Mem` / `Circe.Transfer`, ROADMAP M3)
backs the value semantics on the admitted fragment, so trust is
CIRGen text + Lean/Mathlib, not oracle verdicts or differential fuzz.
See `docs/OVERVIEW.md` for the current state and
`docs/ROADMAP.md` for the four-pillar plan.

## Where it stands

The project is organized into four pillars; 95 delivered slices are
recorded in `docs/DELIVERED.md` (the gate is green at 607/607 jobs).

- **Pillar 1 — C completeness + raw pointers.** Complete within the
  standing non-goals, including one-pointer linked-list shapes
  (length chase, append, push-front/erase/find/copy/clear,
  sorted insert, sorted merge, remove-if `list_filter`,
  adjacent-duplicate squeeze `list_unique`) over a bump-region
  memory with loud faults, plus `list_reverse` / `list_rotate_left`
  as the current proposed next slices.
- **Pillar 2 — STD for C++ (vector algorithms).** The `std::vector`
  algorithm run is closed through P2-M16: checked `at()` reads/writes,
  transform, partition, selection sort, merge runs / merge sort /
  quicksort / heapsort, erase-compress, prefix-sum scan, sorted-range
  intersect/union/difference, out-of-place filter (`vec_copy_if`),
  in-place squeeze (`vec_unique`), and the caller-record squeeze
  (`vec_unique_copy`, `std::unique_copy`), each with equality- and
  memory-transfer contracts against independent oracles.
- **Pillar 3 — human-readable/writable proofs.** Thin Hoare sugar
  over first-order helpers (no grand abstractions), `cir_fuel` /
  `cir_eval_closed` / fold-end tactics, contract facades
  (`Circe.Contracts.*`), lemma packs (`Circe.Lemmas.*`), proof
  galleries (19+ counted instances), and the `examples/hello/`
  external-user loop below.
- **Pillar 4 — Iris (MoSeL) separation logic, fallback only.**
  Standing policy: **native first, Iris on fallback.** Every problem
  gets the simple no-Iris solution attempted first; Iris is attempted
  only when that fails. Iris-lean (MoSeL only — not the oracle, not
  the `Mem` tags) is vendored on the pinned `v4.34.0` tag and
  provides a reusable frame rule (`frame_memStore_cells` /
  `frame_memStore_cellAtI`, `store_frame_cellAtI`) over reified
  `Mem`, with the first hypothesis-free CondDemo discharges landed
  (P4/P4-2). The escalation trigger stays armed — a second
  conditional shape that resists the bespoke `condPost` treatment
  escalates to the Iris frame rule instead of paying a third bespoke
  proof. Concurrency is a standing non-goal; it is the one use case
  with no native answer, and the Iris revisit becomes mandatory if
  it enters scope. See ROADMAP pillar 4 for the full history
  (2026-10-12 spike → defer → 2026-10-23 vendoring).

## Requirements

- [elan](https://github.com/leanprover/elan) 4.2.4 (provides `lean`, `lake`)
- Lean 4.34.0 (`lean-toolchain`: `leanprover/lean4:v4.34.0`)
- Mathlib `v4.34.0` (pinned in `lake-manifest.json`; prebuilt oleans are
  downloaded automatically, no local Mathlib build needed)
- System `clang` for the native C corpus driver (any recent clang)
- CIR-enabled `clang` + `cir-opt` **only** to re-capture CIR goldens:
  `~/code/llvm-project-cir/build/bin/{clang,cir-opt}` at the pinned SHA
  (see `docs/PINS.md`). Not needed for `lake build`.

## How to run

```sh
# one-time: install elan, then fetch Mathlib oleans
lake update        # refresh deps (optional; manifest is pinned)
lake build         # typecheck everything, including Phase 2 lemmas

# run the C corpus natively (no CIR build needed)
for f in tests/c/*.c; do clang -O0 "$f" -o "/tmp/$(basename $f .c)"; done

# re-capture CIR goldens (requires the CIR-enabled clang, see docs/PINS.md)
tools/emit-cir.sh  # writes tests/cir/*.cir

# End-to-end (single entry point): regenerates `out/`, then the full
# gate — golden byte-diffs, typechecks, golden suites, differential
# fuzz vs native (default 1000 trials), rejection suites, spec
# stubs (174, each `#eval`'d `true`), and tactic-adoption checks.
# Current head: 607/607 TEST-OK.
lake exe circe-test [trials]
```

## For users (prove things about your own C++)

The loop, end to end — every command below runs verbatim against
`examples/hello/` (a workspace lib with its own directory that
imports only `Circe.*`, i.e. the external-user shape):

```sh
# 0. Build once (same Requirements as above). This also checks the
#    example proofs — `Hello.Spec` must compile.
lake build circe-emit Hello

# 1. Write C++. The example is pure checked addition:
cat examples/hello/hello.cpp

# 2. Emit Lean. CIR capture needs the CIR-enabled clang
#    (docs/PINS.md); the repo ships captures, and the gate reuses
#    the `add` capture for the example:
lake exe circe-emit -- --in tests/cir/add.cir --out /tmp/my_add.lean
diff /tmp/my_add.lean examples/hello/Hello/Emitted.lean && echo SAME
# Multi-def modules: add `--func <mangled>` to pick one.
# Functions with reference params: add `--fact <name>=noalias`
# (pure functions default to `unknown`). Anything outside the
# admitted subset (docs/SUBSET.md) rejects loudly — never silently
# modeled. Try it: point `--in` at any other `tests/cir/*.cir`
# whose shape is not admitted and read the `out-of-subset` message.

# 3. Read the emission. It is a pure forward over `BitVec`/`Result`:
cat examples/hello/Hello/Emitted.lean

# 4. Write your spec + proof next to it (see
#    examples/hello/Hello/Spec.lean: `hello_add_small` proves small
#    inputs add exactly via `checkedAddI32_ok`; `hello_add_comm`
#    rides the library lemma; `hello_spec_check` is the executable
#    check). This step is ordinary Lean — `docs/VERIFYING.md`
#    documents the spec style. Rebuild to check your proofs:
lake build Hello

# 5. Evaluate the executable check (`true` required):
printf 'import Hello.Spec\n#eval hello_spec_check\n' > /tmp/hello_check.lean
lake env lean /tmp/hello_check.lean
# true
```

What you get: the emitted forward is covered by the emitter's
own correctness proofs (`Circe/Emit`, `emit_correct_*`), and the
memory transfer (`Circe.Mem`/`Circe.Transfer`) backs the value
semantics on the admitted fragment — your spec + proof is the
only new trusted-by-you artifact, checked by `lake build`.
Proving: `import Circe.Tactics` gives the tactic pack
(`cir_simp`, `cir_eval_closed`, `cir_fuel`, `cir_choose`,
`cir_step`) — see `docs/VERIFYING.md` ("For users") and the live
demos in `examples/hello/Hello/TacticsDemo.lean`. Multi-function
programs: write one contract (ok + err legs) per function and
compose callers from callee contracts — see `docs/VERIFYING.md`
("Contracts and composition").
Coming later: modular-proof harnesses and reusable lemma packs
(ROADMAP frontend follow-ups).

## Layout

- `Circe/Base.lean` — value model + checked ops + evaluator vocabulary
- `Circe/CoreIR.lean` — verified IR
- `Circe/Eval/` — loan-based value semantics (+ `cir_fuel`, `cir_eval_closed`)
- `Circe/Mem/` — addressful block-map model (`Agree`, `Model`)
  + lockstep bridges
- `Circe/Emit/` — emitter: per-shape program translations + proofs,
  matcher (`Match.lean`), renderers (`Render`, `SpecStubs`)
- `Circe/Transfer/` — memory transfer, per-shape lockstep twins
- `Circe/Validator/` — verified gate + derived no-alias footprints
- `Circe/Specs.lean` — user specs and per-shape forward contracts
- `Circe/Tactics.lean`, `Circe/LeafTactics.lean` — tactic pack
- `Circe/Hoare/` — Hoare triple rules (thin sugar, first-order helpers)
- `Circe/Contracts/` — stable contract facades
- `Circe/Lemmas/` — reusable lemma packs (`TwoCursor`, `CheckedIx`, …)
- `Circe/Iris/` — MoSeL points-to + frame rules (fallback-only, P4)
- `Circe/CondFrame.lean`, `Circe/ReadOnly.lean`, `Circe/Scope.lean`
  — framing, sharing discipline, lifetime evidence
- `Circe/Parser.lean`, `Circe/Oracle.lean` — trusted front ends

Docs: `docs/OVERVIEW.md`, `docs/SUBSET.md`, `docs/PIPELINE.md`,
`docs/VERIFYING.md`, `docs/ROADMAP.md`, `docs/DELIVERED.md`,
`docs/PINS.md` (`docs/archive/` holds the superseded
phase-history docs).
