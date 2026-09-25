# circe

CIR → Lean 4 verification pipeline for C (MVP subset), Aeneas-style:
C source → ClangIR (CIR, raw `CIRGen` output) → pure, memory-free Lean 4
via a verified emitter, with functional-correctness proofs as pure equations.
No memory model, no separation logic in the common case.
See `docs/PLAN.md` for the full plan.

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

# Phase 3 end-to-end: build, regenerate out/, golden diff, typecheck emitted
# files, build native drivers, differential fuzz vs native (default 1000 trials)
tools/check-phase3.sh [trials]

# Phase 4 end-to-end (superset): above plus choose/sum outputs, both fuzzers,
# and the golden pipeline + rejection suite (18 checks)
tools/check-phase4.sh [trials]
```

Layout: `Circe/Base.lean` (value model + checked ops), `Circe/CoreIR.lean`
(verified IR), `Circe/Eval.lean` (loan-based value semantics),
`Circe/Validator.lean` (verified gate), `Circe/Emit.lean` (emitter),
`Circe/Parser/` + `Circe/Oracle/` (trusted front ends).
Docs: `docs/PLAN.md`, `docs/PINS.md`, `docs/CIR_SUBSET.md`,
`docs/OWNERSHIP.md`, `docs/SEMANTICS.md`, `docs/VERIFYING.md`.
