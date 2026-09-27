# Verifying Functional Correctness

Workflow: pure equational specs over emitted code, à la Aeneas — no
memory model, no separation logic, no framing lemmas. `Circe.Specs`
proves specs against `Circe.Base` operations that are literally the
bodies of the emitted definitions in `out/*.lean`, so they transfer
verbatim.

| Spec | Statement | Emitted body (golden-pinned) |
|---|---|---|
| `incr_correct` | ok → `r = p + 1` + `nsw` certificate; overflow genuinely out of range | `incr_fwd p := checkedIncrI32 p` |
| `choose_lens_laws` | get-put + put-get over tag-free `BitVec` mirrors | `choose_fwd` / `choose_back` |
| `sum_correct` | in-range = `List.sum` of taken prefix (`prefixSumU32_take_sum`); `sum_correct_full` is the `BoundedList` body | `.ok (prefixSumU32 a.val a.val.length)` |
| `vec_correct` | heap program = `List.sum` of `[0,n)` (`vecFillSumU32_correct` + take bridge); `vec_empty` is `n = 0` | `vecFillSumU32 n.toNat` |

Body identity enforced two ways: `native_decide` golden linkage in
`Circe.Emit` (+ `diff` in check scripts) and emitted-body `grep`
assertions in the check script.

## Tactics

`Circe.Tactics` provides `cir_simp`: one `simp` set bundling
checked-op unfoldings, `prefixSumU32` + sum bridge, `bget` /
`pointTranslate`, vector ops, and `Result` bind/map computation rules
(caller-side `←` chains compute by `rfl`). Compose with plain `simp`
for goal-specific lemmas (`cir_simp` takes no extra args by design).

```lean
theorem sum_correct_full {n : Nat} (a : BoundedList (BitVec 32) n) :
    prefixSumU32 a.val a.val.length = a.val.sum := by
  cir_simp
```

Plain `simp`/`omega`/`bv_decide` suffice in the common case.
Stage 2 (ROADMAP.md S5) adds: loop-invariant helper, fuel
automation, forward/backward reasoning — staged after `cir_simp`
growth (S4).

## Spec scaffolding (ROADMAP.md S4)

Emitter writes `out/<name>_Spec.lean` next to each forward file:
unverified stub with the function signature, the `Base`-op body
reference, an edge-case list (empty / singleton / max-fuel), and a
`Diff*`-style prop-test entry. The user copies the stub into
`Circe.Specs` (or a per-project spec file) and fills the equation.
The check script asserts the stub exists and typechecks; the filled
spec transfers by the same body-identity argument above.
See ROADMAP.md S4 for acceptance.
