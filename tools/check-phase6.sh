#!/usr/bin/env bash
# Phase 6 end-to-end check: Phase 5 pipeline + extended reject suite.
# Usage: tools/check-phase6.sh [trials]
# 1. Delegates to tools/check-phase5.sh (build, regenerate, goldens,
#    typecheck, both fuzzers, golden/rejection suite, specs transfer).
# 2. Runs the Phase 6 extended rejection suite (tests/lean/GoldenPhase6.lean):
#    every remaining `forbiddenOp` branch (volatile/atomics/inline-asm,
#    double, int_to_ptr, landingpad, void* returns) plus the Phase 6
#    additions (heap, setjmp/longjmp, globals, function pointers, VLAs,
#    variadics, switch, goto, bitfields, signed wrapping arithmetic).
#    Mismatch policy: any in-subset C -> Lean divergence is P0; everything
#    out of subset must reject loudly (never silently model memory).
# 3. Asserts the roadmap + docs linkage (heap/C++/oracle-trust follow-ups).
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${1:-1000}"

tools/check-phase5.sh "$TRIALS"

echo "== extended reject suite (Phase 6) =="
lake env lean --run tests/lean/GoldenPhase6.lean

echo "== roadmap + docs linkage =="
grep -q "uniquely-owned heap" docs/ROADMAP.md
grep -q "Stacked Borrows" docs/ROADMAP.md
grep -q "C++-lite" docs/ROADMAP.md
grep -q "cir.br" docs/CIR_SUBSET.md
grep -q "GOLDEN6-OK" tools/check-phase6.sh
echo "roadmap + docs in sync"

echo "PHASE6-OK"
