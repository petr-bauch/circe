#!/usr/bin/env bash
# Phase 5 end-to-end check: Phase 4 pipeline + functional-spec verification.
# Usage: tools/check-phase5.sh [trials]
# 1. Delegates to tools/check-phase4.sh (build, regenerate, goldens,
#    typecheck, both fuzzers, golden/rejection suite).
# 2. Asserts the emitted bodies the Phase 5 specs reason about are exactly
#    the golden-pinned text (so `Circe.Specs` transfers verbatim to `out/`).
# 3. Typechecks the specs + tactics modules explicitly (also via lake build).
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${1:-1000}"

tools/check-phase4.sh "$TRIALS"

echo "== emitted-body correspondence (Specs transfer argument) =="
grep -qF "checkedAddI32 a b" out/Add.lean
grep -qF "checkedIncrI32 p" out/Incr.lean
grep -qF ".ok (if b then x else y)" out/Choose.lean
grep -qF ".ok (if b then (ret, y) else (x, ret))" out/Choose.lean
grep -qF "prefixSumU32 a.val a.val.length" out/SumArray.lean
echo "emitted bodies match Specs assumptions"

echo "== specs + tactics typecheck =="
grep -q "theorem incr_correct" Circe/Specs.lean
grep -q "theorem choose_lens_laws" Circe/Specs.lean
grep -q "theorem sum_correct" Circe/Specs.lean
grep -q 'macro "cir_simp"' Circe/Tactics.lean
lake env lean Circe/Tactics.lean
lake env lean Circe/Specs.lean
echo "specs typecheck"

echo "PHASE5-OK"
