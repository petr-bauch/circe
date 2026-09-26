# Verifying Functional Correctness

Workflow (Phase 5, landed): pure equational specs over emitted code, à la
Aeneas — no memory model, no separation logic, no framing lemmas.
`Circe.Specs` proves the three required specs (§8 DoD item 2); each is
stated against `Circe.Base` operations that are literally the bodies of
the emitted definitions in `out/*.lean`, so they transfer verbatim:

| Spec (`Circe.Specs`) | Statement | Emitted body (`tests/golden/`-pinned) |
|---|---|---|
| `incr_correct` | ok → `r = p + 1` + `nsw` range certificate; overflow → genuinely out of range | `out/Incr.lean`: `incr_fwd p := checkedIncrI32 p` |
| `choose_lens_laws` | get-put + put-get over plain `BitVec` (`chooseBackBV`/`chooseFwdBV` mirrors, tag-free) | `out/Choose.lean`: `.ok (if b then x else y)` / `.ok (if b then (ret, y) else (x, ret))` |
| `sum_correct` | in-range `sumFwd l n = .ok (.u32 ((l.take n.toNat).sum))` via `prefixSumU32_take_sum`; `sum_correct_full` is the emitted `BoundedList` body | `out/SumArray.lean`: `.ok (prefixSumU32 a.val a.val.length)` |

Supporting lemmas: `incr_spec_ok/err`, `chooseFwdBV_agrees`/`chooseBackBV_agrees`
(Value-level bridge to `chooseFwd`/`chooseBack` and their Emit lens laws),
`sum_correct_oob`, `sum_empty`. The bridge `prefixSumU32_take_sum`
(a prefix sum is the `List.sum` of the taken prefix) lives in `Circe.Base`
next to `prefixSumU32`.

Body identity is enforced two ways: `native_decide` golden linkage in
`Circe.Emit` (+ `diff` in the check scripts, since `lake` does not track
`include_str` deps) and the emitted-body `grep` assertions in
`tools/check-phase5.sh`.

## Tactics

`Circe.Tactics` provides `cir_simp`: one `simp` call bundling checked-op
unfoldings (`checkedAddI32`, `checkedIncrI32`, `checkedAddU32`, strict
variant, `checkedNegI32`, `checkedDivI32`), `prefixSumU32` computation +
its `List.sum` bridge, `bget`/`pointTranslate` shapes, and the `Result`
bind/map computation rules (`result_bind_ok/err`, `result_map_ok/err`
— caller-side `←` chains compute by `rfl`). Compose with plain `simp`
for goal-specific lemmas (`cir_simp` takes no extra args by design:
`simp`-argument splicing does not accept raw `term` lists):

```lean
theorem sum_correct_full {n : Nat} (a : BoundedList (BitVec 32) n) :
    prefixSumU32 a.val a.val.length = a.val.sum := by
  cir_simp
```

Plain `simp`/`omega`/`bv_decide` suffice in the common case; `cir_simp`
just saves re-listing the set. Used throughout `Circe.Specs`.

## Current status (Phase 5)

Three pure functional-correctness theorems proved (`Circe.Specs`:
`incr_correct`, `choose_lens_laws`, `sum_correct`, all `lake build`
green). `tools/check-phase5.sh` runs the whole E2E: everything in
`check-phase4.sh` (both differential fuzzers, 18-case golden/rejection
suite) plus emitted-body correspondence and specs typecheck.
Next: Phase 6 hardening (reject-suite CI, in-subset fuzzing, heap/C++
roadmap).
