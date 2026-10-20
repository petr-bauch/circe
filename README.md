<p><div style="text-align: center">
<img src="static/circe.jpg" alt="circe" width="240">
<figcaption>
Circe Invidiosa, John William Waterhouse, 1892
</figcaption>
</div>
</p>

CIR → Lean 4 verification pipeline for C and STL-free C++-lite, Aeneas-style:
source → ClangIR (CIR, raw `CIRGen` output) → pure, memory-free Lean 4
via a verified emitter, with functional-correctness proofs as pure equations.
No memory model, no separation logic in the common case; a proved memory
transfer (`Circe.Mem` / `Circe.Transfer`, ROADMAP.md M3) backs the value
semantics on the admitted C fragment, so trust is CIRGen text +
Lean/Mathlib, not oracle verdicts or differential fuzz.
See `docs/OVERVIEW.md` for the current state.

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

# End-to-end (single entry point): the full pipeline — C/C++ corpora through
# N9 (incl. N8 closed-eval adoption and the N9 insertion-sort golden + diff
# stages) — plus golden diffs, native drivers, differential fuzz vs native
# (default 1000 trials), rejection suites, spec stubs, and tactic-adoption
# checks
tools/check.sh [trials]
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

Layout: `Circe/Base.lean` (value model + checked ops + evaluator vocabulary),
`Circe/Emit/{Vec,Flow,M2,Sum,Grow}Fwd.lean` (per-family program translations),
`Circe/CoreIR.lean`
(verified IR), `Circe/Eval.lean` (loan-based value semantics + `cir_fuel` + `cir_eval_closed`),
`Circe/Mem.lean` (addressful block-map model + lockstep bridges),
`Circe/Validator.lean` (verified gate + `derivedNoalias`),
`Circe/Emit*.lean` (emitter + per-shape proofs), `Circe/Derived.lean`
(per-shape noalias footprints), `Circe/Transfer.lean` (memory transfer),
`Circe/Tactics.lean` (`cir_simp`), `Circe/Specs.lean` (user specs),
`Circe/Hoare/` (Hoare triple rules), `Circe/CondFrame.lean`
(framing assertions), `Circe/ReadOnly.lean` (read-only sharing discipline),
`Circe/Scope.lean` (scope/alloca lifetime evidence),
`Circe/Parser/` + `Circe/Oracle/` (trusted front ends).
Docs: `docs/OVERVIEW.md`, `docs/SUBSET.md`, `docs/PIPELINE.md`,
`docs/VERIFYING.md`, `docs/ROADMAP.md`, `docs/PINS.md`
(`docs/archive/` holds the superseded phase-history docs).
