# Phase 0 Pins (reproducibility record)

Date: 2026-09-20. Update this file on every toolchain bump.

## LLVM / Clang / CIR

- `llvm-project` SHA (original pin): `51b123078e64d73f7d8db78645d6f56fbed3215d`
  (2025-01-30). Local checkout at `~/code/llvm-project` — **left untouched**.
  Its CIRGen is declaration-only (see Blocker below); superseded for CIR
  purposes by the worktree pin.
- `llvm-project-cir` worktree pin: `32080ffd98b12a7f4733181790b21ff62f9f31ba`
  (`origin/main` as of 2026-09-20), at `~/code/llvm-project-cir`
  (detached HEAD worktree; main checkout undisturbed).
  Build dir `~/code/llvm-project-cir/build`, same CMake flags as above.
  At this SHA: full CIR (`clang/test/CIR/CodeGen` with function bodies,
  `clang/tools/cir-opt`, `cir-translate`, `cir-lsp-server`).
- System clang: `clang version 19.0.0git (a2af375556486d8027d229f3fae956af8371aa86)`,
  installed at `/usr/local/bin/clang`.
  **Status: CIR NOT enabled** (`CIR support not built into clang`,
  `clang -cc1 -emit-cir` hits `UNREACHABLE` in `ExecuteCompilerInvocation.cpp:57`).
- Existing build dir `~/code/llvm-project/build`: configured WITHOUT
  `CLANG_ENABLE_CIR` (see `build.sh`: `clang;clang-tools-extra;mlir`,
  no `-DCLANG_ENABLE_CIR=ON`). Do not reuse for CIR.
- CIR build dir (new): `~/code/llvm-project/build-cir`, configured with:
  ```
  cmake -G Ninja ../llvm \
    -DLLVM_ENABLE_PROJECTS="clang;mlir" \
    -DLLVM_TARGETS_TO_BUILD="X86" \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_ENABLE_ASSERTIONS=ON \
    -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
    -DLLVM_ENABLE_LLD=ON -DLLVM_CCACHE_BUILD=ON \
    -DCLANG_ENABLE_CIR=ON
  ```
  Expected artifacts: `build-cir/bin/clang` (CIR-enabled).
  Smoke test (no `cir-opt` tool at this SHA — it appeared later upstream):
  `build-cir/bin/clang -cc1 -emit-cir <f>.c -o <f>.cir`.
- CIR capture flags (once built):
  ```
  build-cir/bin/clang -fclangir -Xclang -emit-cir \
    tests/c/<f>.c -S -o tests/cir/<f>.cir
  ```
  (`-fclangir-disable-passes` does not exist at the pinned SHA; re-add if
  supported after the upgrade below.)
  Plus oracle verdicts: `-Rpass-missed=...` / `-fsave-optimization-record`
  for `basicaa` noalias evidence (exact flags TBD during Phase 4).

## Lean

- `lean-toolchain`: `leanprover/lean4:v4.34.0`.
- `lean --version`: `4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b)`.
- `lake`: `5.0.0-src+293d5d0`. `elan`: `4.2.4`.
- Mathlib revision: `v4.34.0` → `5ed2965256430c3649e86755f9576b54eca72435`
  (pinned 2026-09-21 via `lake init circe math`; see `lake-manifest.json`).
  `lake build` downloads the prebuilt olean cache, so our skeleton builds
  without compiling Mathlib locally.

## Status (Phase 0 COMPLETE 2026-09-20)

- [x] C corpus checked in (`tests/c/*.c`, 5 files); native `clang -O0`
      driver passes (`corpus-native-OK`).
- [x] CIR-enabled `clang` + `cir-opt` built at worktree pin
      (`~/code/llvm-project-cir/build/bin/{clang,clang-24,cir-opt}`,
      `ninja clang cir-opt` green).
- [x] `tests/cir/*.cir` goldens captured via `tools/emit-cir.sh`
      (raw CIRGen: `-fclangir -Xclang -emit-cir
      -Xclang -clangir-disable-passes`), all 5 `cir-opt` VERIFY-OK.
- [x] Oracle evidence: `__restrict__` params surface as
      `{llvm.noalias, llvm.noundef}` attrs in goldens (e.g. `incr`,
      `choose`, `sum_array`). Deeper `-fsave-optimization-record` dumps
      deferred to Phase 4 (`tests/oracle/` placeholder remains).
- [x] Mathlib revision pinned at Phase 1 `lake init` time
      (`v4.34.0` → `5ed2965`, see Lean section above).

## Status (Phase 1 COMPLETE 2026-09-21)

- [x] Lean skeleton per PLAN.md §7 Phase 1 (`Circe/{Base,CoreIR,Eval,
      Validator,Emit,Parser,Oracle}.lean`, `Circe.lean` re-export).
- [x] `lake build` green (10 jobs, no errors/warnings).
- [x] `docs/SEMANTICS.md` (fragment table + golden idioms) and
      `docs/VERIFYING.md` (Phase 5 pattern stub) drafted.
- [x] `tests/{lean,golden}/` + `out/` dirs created (`.gitkeep`).
- [x] CI: `mathlib`-template `lean_action_ci` workflow (`lake build`).

Observed CIRGen idioms the validator/emitter must handle (from goldens):
`__retval` alloca + store/load/return pattern; `bool→int→bool` cast chains
around `cir.ternary` conditions and `cir.for` `cir.condition`;
`cir.for` cond/body/step regions + `cir.inc`; `cir.ptr_stride`;
`!rec_Point` record types + `cir.get_member %p[N]`; `cir.add nsw` (signed)
vs plain `cir.add` (unsigned); `cir.scope` nesting; module attrs
(`cir.triple`, `dlti.dl_spec`) to ignore.
