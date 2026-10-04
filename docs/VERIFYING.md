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
| `vec64_correct` (M1b) | `u64` heap program = `List.sum` of `[0,n)` (`vecFillSumU64_correct` + take bridge); `vec64_empty` is `n = 0` | `vecFillSumU64 n.toNat` |
| `vecRealloc_correct` (M1c) | grown heap program = `List.sum` of `[0,n+n)` (`vecReallocFillSumU32_correct` + take bridge); `vecRealloc_empty` is `n = 0` | `vecReallocFillSumU32 n.toNat` |
| `add3_correct_ok/err` (N4a) | threaded two-add: ok needs both `checkedAddI32` certs, first-add error propagates | `add3Fwd x y z` (two sequenced binds) |
| `useAdd_correct` / `useNsAdd_correct` (N4a) | entry forward = `addFwd` (overload resolution is identity at spec level) | `useAddFwd` / `useNsAddFwd` |
| `accMoveCtor_correct` (N4b) | dst takes src word (zeroing is entry-level) | `accMoveCtorFwd d s` |
| `moveAcc_correct_ok/err_a/err_b` (N4b) | threaded adds with zeroing `assign`; move invisible at spec level | `moveAccFwd a b` |
| `scopeEarly_correct_eq/ne/err_a/err_b` (N4b) | early `get` on `a == b`, else second add + `get` | `scopeEarlyFwd a b` |
| `useTadd32_correct` / `useTadd64_correct` (N4c) | entry forward = `addFwd` / `add64Fwd` (monomorph resolution is identity at spec level) | `useTadd32Fwd` / `useTadd64Fwd` |

Body identity enforced two ways: `native_decide` golden linkage in
`Circe.Emit` (+ `diff` in `tools/check.sh`) and emitted-body `grep`
assertions in the check script.

## Tactics

`Circe.Tactics` provides `cir_simp`: one `simp` set bundling
checked-op unfoldings (+ ok/err + range bridges, 32- and 64-bit),
`prefixSumU32`/`prefixSumU64` + sum bridges, `bget` / `pointTranslate`
shapes (+ struct-field ok/err bridges), call-unfold
(`addCallerFwd_as_calls`, `sumCallerFwd_is_call`) + the N4a overload
folds (`add3Fwd`/`add3Fwd_ok/err`, `useAddFwd_is_call`,
`useNsAddFwd_is_call`) + the N4c instantiation folds
(`useTadd32Fwd_is_call`, `useTadd64Fwd_is_call`) + the N4b move folds (`accMoveCtorFwd_is_ok`,
`moveAccFwd_is_moveAcc` + `moveAcc_ok/err_a/err_b`,
`scopeEarlyFwd_is_scopeEarly` + `scopeEarly_ok_eq/ok_ne/err_a/err_b`;
program-level `if_` + `seq_returned` lemmas back the early return),
vector ops (+ the
whole-program bridges `vecFillSumU32_correct` / `vecFillSumU64_correct`),
S3a flow folds, and
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

## N3c gallery: worked properties (ROADMAP.md N3 — done)

Three end-to-end proofs over the existing corpus, checked into
`Circe.Specs` (driver typecheck-gated, so they double as regression
tests for N3a/N3b). Each shows where `cir_simp` ends and domain
reasoning begins.

Sortedness of a fill loop — `vec` writes `k` at slot `k`, so the
filled values ascend (`ofNat` monotone below `2 ^ 32`):

```lean
theorem fillSorted_u32 (m : Nat) (hm : m ≤ 2 ^ 32) :
    List.Pairwise (· ≤ ·) ((List.range m).map (BitVec.ofNat 32)) := by
  rw [List.pairwise_map]
  revert hm
  induction m with
  | zero => intro _; simp
  | succ k ih =>
    intro hm
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih (by omega), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    have hbk : b = k := List.mem_singleton.mp hb
    rw [hbk]
    have hak : a < k := List.mem_range.mp ha
    rw [BitVec.ofNat_le_ofNat,
      Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega)]
    omega
```

`find_eq` first-match minimality — every index below the hit holds a
different value (core's `List.find?_range_eq_some` is the minimality
fact; the `decide` bridge turns `(!·) = true` into `≠`):

```lean
theorem findEq_first_match (l : List (BitVec 32)) (n : Nat) (k : BitVec 32)
    (j : Nat) (h : findIdxU32 l n k = some j) (i : Nat) (hij : i < j) :
    l[i]? ≠ some k := by
  rw [findIdxU32, List.find?_range_eq_some] at h
  have hneg : decide (l[i]? = some k) = false := by
    simpa using h.2.2 i hij
  exact of_decide_eq_false hneg
```

`vec_realloc` prefix preservation at spec level — the grown program
sums `range (n + n)`, whose length-`n` prefix is exactly the ungrown
program's domain (the extension fills `[n, n + n)` without touching
it; cf. `vecReallocFillSumU32_correct`):

```lean
theorem reallocPrefix_spec (n : Nat) :
    ((List.range (n + n)).take n) = List.range n := by
  simp
```

N3b audit result (all in `Circe.Specs`): every proof is `cir_simp`-first
with at most two further steps, except two sanctioned exceptions —
`translate_correct` conjoins conditional bridges that provably do not
fire under `simp` (so `exact`, as in the `incr` precedent), and
`cls_correct` case-splits the exhaustive dispatch (`by_cases` × 2)
before `cir_simp` + `simp_all` closes the if-lifting. The set grew by
`accCtorFwd`/`accCtor`/`accGetFwd`/`accDtorFwd` (each enables at least
one proof); `vecRealloc_empty`/`vec64_empty` shortened to bare
`cir_simp` and `sumCaller_correct` now opens with `cir_simp`.

## Spec scaffolding (ROADMAP.md S4 — done)

The emitter writes `out/<name>_Spec.lean` next to each forward file
(39 stubs, one per golden; `tools/GenOut.lean` via `Circe.Emit.emitSpec`,
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
sides render before comparing.) Acceptance met: 25/25 stubs
typecheck, 25/25 `_check` entries evaluate to `true` (asserted in
`tools/check.sh`); `vec_correct`
refactored shorter onto the grown set (see Tactics above).
