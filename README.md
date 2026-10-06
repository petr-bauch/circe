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

# End-to-end (single entry point): the full pipeline — C corpus, C++ corpus
# (M2), and the M3 memory-transfer stages — plus golden diffs, native
# drivers, differential fuzz vs native (default 1000 trials), rejection
# suites, spec stubs, and tactic-adoption checks
tools/check.sh [trials]
```

Layout: `Circe/Base.lean` (value model + checked ops), `Circe/CoreIR.lean`
(verified IR), `Circe/Eval.lean` (loan-based value semantics + `cir_fuel`),
`Circe/Mem.lean` (addressful block-map model + lockstep bridges),
`Circe/Validator.lean` (verified gate + `derivedNoalias`),
`Circe/Emit*.lean` (emitter + per-shape proofs), `Circe/Derived.lean`
(per-shape noalias footprints), `Circe/Transfer.lean` (memory transfer),
`Circe/Tactics.lean` (`cir_simp`), `Circe/Specs.lean` (user specs),
`Circe/Parser/` + `Circe/Oracle/` (trusted front ends).
Docs: `docs/OVERVIEW.md`, `docs/SUBSET.md`, `docs/PIPELINE.md`,
`docs/VERIFYING.md`, `docs/ROADMAP.md`, `docs/PINS.md`
(`docs/archive/` holds the superseded phase-history docs).
