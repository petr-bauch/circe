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
| `clsFall_correct` (N6b-i) | `0` falls through to the `1` arm: both answer `10`, else `30` | `clsFallFwd x` (if-chain) |
| `clsDense_correct` (N6b-i) | exhaustive dispatch over all eight cases + default | `clsDenseFwd x` (8-deep if-chain) |
| `clsBreak_correct` (N6b-ii) | both cases store their const, else the `99` initializer | `clsBreakFwd x` (guarded assigns) |
| `clsAdd_correct` (N6b-iii) | compute cases answer `y + 1` / `y + 2` (wrapping), else `y` | `clsAddFwd x y` (`uadd` if-chain) |
| `neg_correct_ok/err` (N6a) | ok delivers `-x`, err is exactly `INT_MIN` overflow | `negFwd x` (`checkedNegI32`) |
| `sdiv_correct_ok/zero/overflow` (N6a) | truncating quotient; zero divisor is `DivZero`; `INT_MIN / -1` is `Overflow` | `sdivFwd a b` (`checkedDivI32`) |
| `accMoveCtor_correct` (N4b) | dst takes src word (zeroing is entry-level) | `accMoveCtorFwd d s` |
| `moveAcc_correct_ok/err_a/err_b` (N4b) | threaded adds with zeroing `assign`; move invisible at spec level | `moveAccFwd a b` |
| `scopeEarly_correct_eq/ne/err_a/err_b` (N4b) | early `get` on `a == b`, else second add + `get` | `scopeEarlyFwd a b` |
| `useTadd32_correct` / `useTadd64_correct` (N4c) | entry forward = `addFwd` / `add64Fwd` (monomorph resolution is identity at spec level) | `useTadd32Fwd` / `useTadd64Fwd` |
| `arrayRef_correct_hit/oob` (N4d-i) | leaf reads the word at a live index, `OOB` off the end | `arrayRefFwd l n` (index read) |
| `arrayAt_correct` (N4d-i) | entry forward = `_S_ref` body (call edge fused, resolution is identity at spec level) | `arrayAtFwd` / `arrayRefFwd` |
| `arraySum_correct_ok/err_a/err_b/err_c` (N4d-i) | threaded three-add: ok needs all three `checkedAddI32` certs, each-site error propagates | `arraySumFwd a b c d` (three sequenced binds) |
| `optHas_correct` (N4d-ii) | leaf reports the engaged bit | `optHasFwd v` (bit read) |
| `optHasValue_correct` / `optDerefOp_correct` (N4d-ii) | entry forwards = leaf bodies (call edges fused, resolution is identity at spec level) | `optHasValueFwd` / `optDerefOpFwd` |
| `optGet_correct_some/none` (N4d-ii) | word on engaged, `AssertFail` on disengaged (unreachable made loud) | `optGetFwd v` (payload match) |
| `optDeref_correct_some/none` (N4d-ii) | word on engaged, `-1` sentinel on disengaged | `optDerefFwd v` (guarded match) |
| `spanExtent_correct` / `spanSize_correct` (N4d-iii) | leaves report the reified length | `spanExtentFwd l` / `spanSizeFwd l` (length read) |
| `spanIndex_correct_some/oob` (N4d-iii) | leaf reads the word at a live `u64` index, `OOB` off the end | `spanIndexFwd l n` (index read) |
| `spanSum_correct_nil/cons/cons_err` (N4d-iii) | checked-add fold: nil is zero, cons threads `checkedAddI32`, error propagates | `spanSumFwd l` (fold from `0`) |
| `stdVecSize_correct` (N4d-iv-a) | leaf reports the reified length | `stdVecSizeFwd l` (length read) |
| `stdVecIndex_correct_some/oob` (N4d-iv-a) | leaf reads the word at a live `u64` index, `OOB` off the end | `stdVecIndexFwd l n` (index read) |
| `stdVecReadSum_correct_nil/cons/cons_err` (N4d-iv-a) | checked-add fold: nil is zero, cons threads `checkedAddI32`, error propagates | `stdVecReadSumFwd l` (fold from `0`) |
| `stdVecEmptyCtor_correct` / `stdVecUnit_correct` (N4d-iv-b1) | empty owned triple; erased no-ops answer zero | `stdVecEmptyCtorFwd` / `stdVecUnitFwd` (const) |
| `stdVecDtor_correct_empty/free` (N4d-iv-b1) | null passthrough; live frees storage | `stdVecDtorFwd b len cap` (cap guard + `vecFree`) |
| `stdVecDestroyNoop_correct` / `stdVecDestroyPtr_correct` / `stdVecGetTp_correct` (N4d-iv-b1) | trivial destroys + stateless allocator answer zero | const `0` forwards |
| `stdVecDiffMax_correct` (N4d-iv-b1) | the `S64_MAX / 4` difference bound | `stdVecDiffMaxFwd` (const) |
| `stdVecMax_correct_right/left` / `stdVecMin_correct_right/left` (N4d-iv-b1) | arg selection on the `ult` guard | `stdVecMaxFwd a b` / `stdVecMinFwd a b` (conditional) |
| `stdVecCheckLen_correct_fail/saturate/exact` (N4d-iv-b1) | loud past `max_size - size`; saturate on wrap; else grown length | `stdVecCheckLenFwd len n` (3-deep guard chain) |
| `stdVecBegin_correct` / `stdVecEnd_correct` / `stdVecBack_correct` (N4d-iv-b1) | 0 / length / length − 1 | const / reified forwards |
| `stdVecIterId_correct` / `stdVecMinusEl_correct` / `stdVecMinus_correct` (N4d-iv-b1) | identity; wrapping `usub`; bit-exact `s64diff` | `stdVecIterIdFwd` / `stdVecMinusElFwd` / `stdVecMinusFwd` |
| `stdVecAlloc_correct_zero/ok/overmax` (N4d-iv-b1) | null shape at zero; zeroed storage; loud past `max_size` | `stdVecAllocFwd n` (count guard + `max_size` bound) |
| `stdVecDealloc_correct_ok/err` / `stdVecDeallocGuard_correct_zero/free` (N4d-iv-b1) | consume; free failure propagates; zero-count passthrough | `stdVecDeallocFwd` / `stdVecDeallocGuardFwd` (`vecFree`) |
| `stdVecConstruct_correct_ok/oob` (N4d-iv-b1) | placement store; loud past storage | `stdVecConstructFwd b len cap p x` (`vecSet`) |
| `stdVecReloc_correct_nil` (N4d-iv-b1) | zero-word relocation is the identity | `stdVecRelocFwd …` (`stdVecBlitFold` nil) |
| `viewBegin_correct` / `viewEnd_correct` (N7a) | erased `0` offset / reified length | const / `viewEndFwd l` (length read) |
| `viewSum_correct_nil/cons/cons_err` (N7a) | checked-add fold over sign-extended bytes: nil is zero, cons threads `checkedAddI32` over `sext8`, error propagates | `viewSumFwd l` (fold from `0`) |
| `stdVecGrowCapacity_correct` (N7b) | `capacity` reads header word 1 | `stdVecGrowCapacityFwd cap` (reified cap) |
| `stdVecReserve_correct_passthrough/realloc/throw` (N7b) | passthrough when `n ≤ cap`; allocate → relocate → deallocate + length re-pin when `cap < n`; loud past `max_size` | `stdVecReserveFwd b len cap n` (composer over frozen leaves) |
| `vecReserveSumEntry_correct` (N7b) | closed script: ctor + `reserve(10)` + two pushes + two reads + add + dtor returns `3` | `vecReserveSumEntryFwd` (const `3`) |

Host assumption (N7a): x86 `char` is signed, so the `s8i`
element load sign-extends (`viewAt` delivers
`x.signExtend 32`). The model bakes this in; the high-bit diff
edges (`0xFF` sums as `-1`, `0x80` as `-128`) check it against
native on every run. On an unsigned-`char` platform the native
binary would disagree — the `DiffView` mismatch would fire as P0,
which is the honest signal (not silent soundness).

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
Stage 2 (DELIVERED.md S5 — done) adds two tactics beside `cir_simp`
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

Stage 3 (N5) covers the composer patterns S5 left manual. `fuel_step_down`
packs the `F = F' + 1` split with its stepped-down bound (before → after):

```lean
-- before: two lines + two manual omegas at all six b2 composer sites
  obtain ⟨F', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : F ≠ 0)
  have hF' : 5 ≤ F' := by omega
-- after: arithmetic lives in the lemma; the site names only F', hF', k
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
```

`cir_step` registers the program-step cascade (evaluator unfolding +
`Except.map` normalization) with per-step hypotheses as arguments —
the eight span/read/entry `simp only [evalExpr, <hyps>, Except.map>`
lines are now `cir_step evalExpr [<hyps>]`. New composers close steps
with these two instead of bespoke lists. Obligation rule: every composer
spec stub names its owed gallery equations (`TODO (user)` — e.g. the
entry stub names `vecPushSumEntry_correct`); the equations themselves
stay hand-proved in `Circe.Specs`, pinned per-slice in the driver.

### For users (U1)

One door: `import Circe.Tactics`. Three tiers, by how often user
proofs meet them — every tactic demonstrated live in
`examples/hello/Hello/TacticsDemo.lean` (built by `lake build
Hello`, so the demo IS the regression test):

- Everyday: `cir_eval_closed` (closed checks evaluate in the
  kernel — `hello_check_true`), `cir_simp` (discharges the
  library layer in one call — `hello_add_ok_set`: unfold your
  forward, `cir_simp` applies the ok-rule with your certificate
  and splits the range test, leaving integer arithmetic for
  `omega`/an explicit step).
- Advanced (fuel-induction proofs): `cir_fuel` (fuel side-goals —
  `hello_fuel_side`), `cir_step` (one symbolic evaluator step —
  `hello_step_uadd`).
- Specialized: `cir_choose b` (boolean-selector case split with
  the forward/backward equations — `hello_choose_get_put`),
  `cir_fold_end (dropEq, hget)` (suffix-fold end script: unfold
  one step on the left via your fold's drop equation, discharge
  the lookup — `hello_fold_end`; the six in-repo fold sites run
  this exact script).

Three standing limits (all hit during the U1 audit, all documented
so users don't rediscover them):

- Unfold your own forward first (`unfold add_fwd`): emitted
  functions are not in the simp set, and the set never guesses
  them.
- Algebraic facts stay explicit: `hello_add_comm_simp` is
  `exact checkedAddI32_comm`, not a simp call — `simp` rejects
  permutative rewrites it cannot orient, so the set deliberately
  carries no commutation lemmas (an audit-proposed addition was
  reverted for exactly this reason).
- `cir_choose` needs a variable selector (a literal leaves the
  impossible branch behind); `cir_step` needs every lookup fact
  the step touches (the cascade only rewrites what the
  hypotheses cover — a single uncovered `envLookup` stalls it);
  `cir_fold_end` needs the drop-equation name for your fold
  (it is per-fold by definition — `spanFold_drop`,
  `viewFold_drop`, `stdVecFold_drop` — plus the lookup fact;
  implementation re-parses surface strings at the use site
  because `rw`/`simp` arg kinds reject spliced idents —
  `cir_step` precedent).

## N3c gallery: worked properties (DELIVERED.md N3 — done)

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

## Spec scaffolding (DELIVERED.md S4 — done)

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

## Contracts and composition (U2)

A per-function contract is an ok leg plus an err leg over the
emitted forward, proved from callee contracts taken as
hypotheses — never by re-verifying the callee. Shape:

```lean
theorem myCaller_contract_ok (args ...)
    -- CONTRACT (assumes, callee ok legs): one equation per call site.
    (h1 : calleeFwd ... = .ok ...) (h2 : ...) :
    -- CONTRACT (guarantee, ok leg).
    myCallerFwd ... = .ok ... := by
  simp only [myCallerFwd, h1, h2, ...bridges...] <;> cir_simp
-- CONTRACT (guarantee, err leg): same skeleton with the failing
-- callee equation; first-failure-wins matches the forward's binds.
theorem myCaller_contract_err ... : ... := by
  simp only [myCallerFwd, h, ...] <;> cir_simp
```

Three operators, all already the in-repo idiom (the harness names
the shape; it invents nothing):

- Sequential threading: callee equations rewrite into the
  unfolded composer, bridges discharge the between-call value
  shapes. Instances: `add3_correct_ok/err`, `addCaller_correct_ok/err`,
  `stdVecGrowRealloc_correct_ok` (eight callee equations),
  `stdVecReserve_correct_realloc` (allocate → relocate →
  deallocate-guard), `VecMergeRuns.mergeRunsFwd_ok` (main →
  drain-`i` → drain-`j`), each marked `Template instance` at
  its doc. Recursive callees carry fuel-indexed ok legs plus
  per-failure-site err legs (`mergeRunsMainFwd`,
  `mergeRunsDrainIFwd/JFwd`), proved by fuel induction.
- Delegation: the composer forward is the callee (plus a
  projection) — rewrite with the delegation equation, apply the
  callee's spec. Instances: `sumCaller_correct` (→ `sum_correct`),
  `stdVecEmplaceBack_correct_slow/fast` (→ realloc/construct).
- Conjunction: independent legs conjoined when conditional
  bridges provably do not fire under `simp` (so `exact`, as in
  the `incr` precedent). Instance: `translate_correct`.

Fan-out boundary (read before forcing rotate into this shape):
`vecRotateFwd` is stated directly (`drop`/`take`), so no callee
subterm exists for assumes to rewrite — a forward-level
contract trio over it would be vacuous. Its composition proof
lives one level down (`evalProgFunc_vecRotate`: three
`callProg` steps over the seg entry, R2). Program-level
`seq`/`callRet` contract rules are the Pillar-3 prerequisite;
until they exist, fan-out with a direct-stated composer stays
at the eval level, and fan-out with a callee-stated composer
uses sequential threading (one equation per call site, cf. the
realloc eight). Missing callee specs are new verification, not
harness work: the mergeRuns/drain forwards have no specs yet
(U3 material).

### OOB twins (K6c)

A loop-level err leg for short reads follows the `LoopOob`
recipe (`Circe/Crypto/LoopOob.lean`): induction on
iterations-remaining with the mutated state generalized
(message, counter, fuel); zero case proves the failing read
and closes body and loop with `whileErr_of_bodyErr`;
successor case proves both reads hit, falls the body through,
and steps with `whileStep_of_bodyOk`; fuel `n + 1 ≤ F`
discharged by `cases F`, the zero-fuel subcase by the fuel
hypothesis. Guards read via `iterGuardT`. Instances:
`xorLoopMsgFirst_oob` (message-read-first),
`xorLoopSFirst_oob` (keystream-read-first, needs `i ≤ 16`
since the keystream block is 16 words).
Divergence fencing: where eval returns but the model rejects,
fence with a side condition on the twin (`nwords ≠ 0` for the
short key/nonce twins — the empty-message early return; the
message twin needs none since `msg.length < nwords.toNat`
already excludes `nwords = 0`). Early-exit loops use the
loop-err/exit-ok sum (`outerWhile_msg_oob`): the exit case
returns its state as payload for the tail instead of an
equation, because the tail runs at outer fuel on one side
and predecessor fuel on the other.

## Lemma packs (U3)

Rule: prose note on first reuse, pack on the third use. Each pack
is a `Circe/Lemmas/*` file proved once over abstract hypotheses;
consumers replace their inline copies with one application, and
the gate (byte-identical goldens + CHECK-OK) confirms the
refactor changed no statement.

- CheckedIx (`Circe/Lemmas/CheckedIx.lean`, P1 DONE): pointwise
  read of two sequential positional writes, `doubleSet_read`
  (the touching case rides on an explicit `i = j → a = b`
  hypothesis proved from the two checked reads) plus
  `doubleSet_length` (the `length_set` chain). Consumers:
  `RevInv_step` and `SegInv_step` `hset` proofs (were verbatim
  copies). Bounds side-goals stay `by omega` with the invariant
  in context — that one-liner is already the automation.

- Two-pointer invariant (P2 NEGATIVE, deliberate non-result):
  after P1 the only commonality left between `RevInv_step` and
  `SegInv_step` is mirror arithmetic that differs per invariant
  plus per-leg case skeletons, which are proof-script rather
  than lemma material (a tactic would be the vehicle, and that
  needs three user-goal uses first). With only two
  forward-level uses the standing rule keeps this at prose
  level; a third countdown-swap loop reopens the question.

## Hoare triples (H1)

`Circe.Hoare` wraps the `Mem` equation lemmas as Hoare triples —
total correctness over `.ok` outcomes, fuel-generic, no new
semantics. `HTriple P s Q`: from any pre-state satisfying `P`,
statement `s` evaluates (at any fuel) to an ok outcome
satisfying `Q`; errors stay caller-side hypotheses, matching
transfer style. Rules (`Circe/Hoare/Rules.lean`):
`htriple_skip`, `htriple_seq` (mid-outcome pinned to
`fellThrough`; early return is `htriple_seq_return` via
`memEvalStmtFuel_seq_return`), `htriple_consequence`,
`htriple_mstore_frame` (stored-cell fact plus one framed cell;
index pinned to `0`, complete rather than limiting because
`cellAt` is a singleton assertion, so any successful store into
a `cellAt` cell is at index 0), `hexpr_mload`
(expression-level only — `mload` has no value mirror, so loads
cannot form statement triples), `htriple_if_true/false` (plain
`.b` guards), `htriple_return` (first non-`fellThrough` post).
Gallery (`tests/lean/HoareGallery.lean`, compile-gated) proves
`pa[0] += 1; pb[0] += 1` end-to-end with framing;
overflow-freedom (`checkedAddI32 v 1 = .ok (v + 1)`) is explicit
hypothesis debt. Tactic trap recorded: `obtain` with `rfl`
patterns substitutes witnesses out of scope — the final `exact`
must use post-substitution values.

### Loops (H2)

`memEvalStmtFuel_while_false` (any fuel) and `while_true`
(one-unfolding) promote the handler arms to equation lemmas.
`HTripleAt` is the fixed-fuel triple; `HTriple` is `∀ F,
HTripleAt F` (existing proofs elaborate unchanged).
`htriple_while_at` takes a fuel-indexed invariant `I :
Nat → state → Prop` — load-bearing, not decorative: at fuel 0
a true-guard loop errors via the zero handler, so `I 0` admits
only guard-false states and each true-guard step delivers an
`I k` state from `I (k+1)` (fuel bounds, so no separate
termination measure is needed); plus `htriple_assign`.
Body iterations must end `fellThrough`/`continued`
(`broke`/`returned` bodies deferred with the handler arms
named). Galleries (`tests/lean/HoareGallery.lean`):
`alias_cond` under both guards over the real emitted body
(first `if`-rule exercise, both cases proved), and a `u32`
countdown (`n ≤ F` at fuel `F`, exact decrement via
`BitVec.toNat_sub`); runtime closed instances ride the
existing `hoare-gallery` driver job — 18 counted passes over
16 check sites (H1–H3 cells/alias/cond-pair/countdown/sum/incr,
R reverse-swap/loop, S seg-window, T rotate, J rewire/chase,
H sift/entry/dup-entry, L-ptr linkedrev; both cond arms
iterate). Tactic note: nested `obtain`
with `rfl` keeps the inner-binder side — the outer names are
gone after substitution, so inner applications must use the
fresh names.

Program level (P3a/F1): `HTripleProg` mirrors `HTriple` over
`memEvalProgStmt` (covers the `callRet`/`callProg` leaves the
call-free evaluator cannot see). `htripleProg_while_at` is the
while rule one level up (same four premises; the R countdown
re-proved as `hoare_reverseWhileProg`); `htripleProg_seq`
(+ fixed-fuel `htripleProg_seq_at`) composes
`fellThrough`-prefix spines from leaf triples
(`hoare_rotateSpine_seq`: size call + `z` let + three admitted
segment calls, four nested applications); `htripleProg_callProg_at`
discharges a `.callProg` leaf from the callee run at one less
fuel (the zero-fuel arm errors, so `At (F+1)`) — the U2
contract + transfer plug in as the run equation, never
re-verified. `hoare_rotateSpine_closed` is the closed rotate
prefix: all five leaves discharged, four `seq_at`
compositions at fuel `G+1` (`htripleProg_seq_at_return` +
`htripleProg_seq_return` now cover the trailing-`return_`
case via the pre-existing `memEvalProgStmt_seq_returned`).

Program-level frame (F3): `htripleProg_callProg_frame_at` /
`htripleProg_callRet_frame_at` ride a caller-memory frame `R`
across the call untouched. Definitional, not deep: the callee
body runs on fresh entry blocks (`memEvalProgFunc` binds into
`emptyMem`, so caller memory is unreachable) and both call
equations keep `(m, π)` identical — no address-inequality side
conditions like `cellAt` framing. `hoare_segCall1_framed`
exercises the `callProg` rule on the first seg call. A fully
framed spine waits for an actual multi-cell caller (third-use
rule); the real frame work — overlapping footprints,
multi-word assertions — lives at statement level (H-track).

### Lets and micro-tactics (H3)

`htriple_let` wraps `memEvalStmtFuel_let_pure` (allocating
arms excluded by constructor-discrimination hypotheses);
`memEvalExpr_add_agree` / `pair_agree` fill the two missing
agreement slots beside `usub_agree`. The `cond_pair` triples
run over the real emitted body (pure-env entry): under `c`
both overflow debts are owed, under `¬c` the `tif`
passthrough masks the first add — no `p` debt. Tactic
verdict (measured, not assumed): the gallery carried ~20%
mechanical lines, but a general `cir_hoare` is rejected — the
15-argument frame applications cannot be inferred. Shipped
instead: `hoare_lit_eval` (one quantified literal-evaluation
lemma replacing seven blocks) and `hoare_guard_of` (one-line
guard-premise closures). A `hoare_eq` substitution macro was
tried and abandoned with reason: quotations cannot splice
into `at` on this toolchain, and the obtain-only fallback
substitutes the wrong side (it drops the inner binders where
the two-step keeps them) — negative result kept on record.
Net rewrite savings ≈ 50 lines at unchanged coverage.

### Array loops (A)

`cellsAt m a t l` (`Circe/CondFrame.lean`) generalizes the
singleton `cellAt` to whole-list contents, with
`memStore_cellsAt` / `memFind_cellsAt_store` /
`memLoad_cellsAt` frame and load lemmas. The first array
gallery is a read-only sum loop (`hoare_sumLoop`): `while (i
< len) { acc = acc + arr[i]; i = i + 1 }` over a `Mem` block
with the total in a framed singleton cell. Overflow-freedom
is per-prefix caller debt (`hdebt`: every `take`-prefix sum
plus the next word adds cleanly); lengths fit `u64` (`hn`).
Design finding: memory floats existentially in the invariant
and post (`mc`, `πc = π`) — the accumulator store evolves
memory each iteration, so entry memory cannot be pinned, and
the exit lemma carries its own layout pin. Tactic notes: a
`subst` drops eliminated binders from scope, so later code
must use post-substitution names (traced, not assumed); a
`rw` that closes its goal leaves no goals for continuations;
accumulator witnesses go in explicitly rather than by
unification assignment. The second gallery is an in-place
increment (`hoare_incrLoop`, single array block, no side
cell): the invariant carries the evolving prefix
(`(take iv).map (· + 1) ++ drop iv`), and the store step
bridges the operational `set`-form to the next prefix form
(`set_append_right` + take/drop algebra, drop-head by
extensionality) — a measured reminder that take/map/drop is
the spec shape while `set` is the operational residue.
Maintenance factor (M2): the duplicated guard stack is now
shared helpers in `Circe/Hoare/Rules.lean` — `ofNat64_toNat`,
`ult_ofNat64_true/false`, `memEvalExpr_ult_ilen`,
`envLookup_ilen`, `hoare_uadd_incr_facts`, `u64_succ_toNat`
— and the prefix algebra lives beside `cellsAt` in
`Circe/CondFrame.lean` (`take_map_drop_getElem`,
`drop_set_zero_cons`, `take_map_drop_set_succ`). Helpers stay
first-order with explicit premises (the H3 inference lesson);
the whole-while-protocol abstraction stays rejected.
