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
checked-op unfoldings (+ ok/err + range bridges, 32- and 64-bit),
`prefixSumU32` + sum bridges, `bget` / `pointTranslate` shapes (+
struct-field ok/err bridges), call-unfold
(`addCallerFwd_as_calls`, `sumCallerFwd_is_call`), vector ops (+ the
whole-program bridge `vecFillSumU32_correct`), S3a flow folds, and
`Result` bind/map computation rules (caller-side `←` chains compute
by `rfl`, with assoc/pure for nested binds). Compose with plain
`simp` for goal-specific lemmas (`cir_simp` takes no extra args by
design).

```lean
theorem sum_correct_full {n : Nat} (a : BoundedList (BitVec 32) n) :
    prefixSumU32 a.val a.val.length = a.val.sum := by
  cir_simp
```

S4 shortened an existing spec onto the grown set (`vec_correct`,
before → after):

```lean
-- before: manual bridge listing (11-line proof)
  rw [vecFillSumU32_correct, prefixSumU32_take_sum, htake]
-- after: bridges fire in `cir_simp`; only the take-length fact is manual
  cir_simp
  rw [htake]
```

Plain `simp`/`omega`/`bv_decide` suffice in the common case.
Stage 2 (ROADMAP.md S5 — done) adds two tactics beside `cir_simp`
plus one bound lemma. Placement follows dependencies (`Tactics`
imports `Emit`, so the helpers live where their names resolve, all in
scope via `import Circe.Tactics`):

- `cir_fuel` (`Circe.Eval`, next to `EVAL_FUEL`): fuel automation —
  normalizes `EVAL_FUEL` and discharges fuel arithmetic
  (`≤ EVAL_FUEL` bounds, `remaining ≤ F` side conditions of
  fuel-generalized loop facts). Replaces the scattered `(by omega)`
  arguments and the `hle4096` conversion lines.
- `word32_lt_two32_of_fuel` (`Circe.Eval`): fuel fits in a word
  (`n.toNat ≤ EVAL_FUEL → n.toNat < 2 ^ 32`). One `have` per
  `emit_correct_*` wrapper.
- `cir_choose b` (`Circe.Emit`, next to `chooseFwd`/`chooseBack`):
  split on the selector, simplify with the verified forward/backward
  equations. Closes get-put / put-get goals.

S5 shortened the `sum`/`vec` wrappers onto the helpers (before →
after):

```lean
-- before: 5-line fuel-to-word block in every emit_correct_* wrapper
  have h32eq : (2 : Nat) ^ 32 = 4294967296 := rfl
  have h32 : nv.toNat < 2 ^ 32 := by
    rw [h32eq]
    have hle4096 : nv.toNat ≤ 4096 := by simpa [EVAL_FUEL] using hfuel
    omega
-- after: one have where a word is at hand, cir_fuel where none is
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  have hlen32 : l.length < 2 ^ 32 := by cir_fuel
```

Loop-fact side conditions discharge uniformly (`sumWhile_correct ...
(by cir_fuel)`), and both `choose` lens laws are one line each
(`by cir_choose b`). No new subset: nested/skip/find keep their
hand-rolled fuel steps and can migrate as needed.

## Spec scaffolding (ROADMAP.md S4 — done)

The emitter writes `out/<name>_Spec.lean` next to each forward file
(14 stubs, one per golden; `tools/GenOut.lean` via `Circe.Emit.emitSpec`,
dispatched on `matchFrag` exactly like `emitFunc`): unverified stub
with the function signature, the `Base`-op body reference, an
edge-case list (empty / singleton / max-fuel), and a `Diff*`-style
prop-test entry. The user copies the stub into `Circe.Specs` (or a
per-project spec file) and fills the equation. The check script
asserts every stub exists and typechecks and every `_check` evaluates
to `true`; the filled spec transfers by the same body-identity
argument above. Example (generated `out/SumArray_Spec.lean`, abridged):

```lean
import Circe.Base

/-- C signature: `uint32_t sum_array(uint32_t *a, uint32_t n)` ... .
    Base body reference: `prefixSumU32` (cf. emitted `sum_array_fwd`,
    `emit_correct_sum`). -/
def sum_array_spec_fwd {n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=
  .ok (prefixSumU32 a.val a.val.length)

/-- Edge cases: empty / singleton / max-fuel (length = bound). -/
def sum_array_spec_edges : List (List (BitVec 32)) :=
  [[], [0], [1], [1, 2, 3], [0xFFFFFFFF, 1]]

/-- Prop-test entry: the `List.sum` equation holds on every edge ... -/
def sum_array_spec_check : Bool :=
  sum_array_spec_edges.all fun l =>
    (repr (prefixSumU32 l l.length)).pretty == (repr ((l.take l.length).sum)).pretty
```

(`repr`-pretty-`==` is the same comparison the `Diff*` fuzzers use:
`Except` has no `DecidableEq` instance to feed `decide`, so both
sides render before comparing.) Acceptance met: 14/14 stubs
typecheck, 14/14 `_check` entries evaluate to `true`; `vec_correct`
refactored shorter onto the grown set (see Tactics above).
