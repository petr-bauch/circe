#!/usr/bin/env bash
# End-to-end gate (thin entry): delegates to the parallel Lean driver.
#
# Contract: mismatch policy — any in-subset divergence is P0;
# out of subset must reject loudly (never silently model memory).
# Success ends with CHECK-OK.
#
# Coverage lives in Test/Driver.lean (its roster IS the wiring):
# regenerate out/ (tools/GenOut.lean, single source of truth) →
# native drivers → golden diffs → typechecks → Diff* fuzz vs native →
# golden suites → emitted-body correspondence → specs (55/55 typecheck,
# 55/55 _check entries true) → TEST-OK. lake does not track
# include_str deps, so diff enforces drift.
# `check-phase*.sh` kept for compat (early-phase slices standalone).
set -euo pipefail
cd "$(dirname "$0")/.."

TRIALS="${1:-1000}"
lake exe circe-test -- "$TRIALS"

echo "CHECK-OK"
