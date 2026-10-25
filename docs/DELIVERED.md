# Circe — Delivered milestones

Long-term goal: a viable verification platform for modern C++ —
the subset of C++ amenable to Aeneas-style translation to Lean,
with tactic and spec support for proving properties of the emitted code.

Delivered slices, moved from `ROADMAP.md` (2026-10-05) to keep the roadmap
focused on active work. Active frontier, ordering, and the lifetime
track stay in `ROADMAP.md`.

## S0. Docs slim + harness rename — DONE (2026-09-27)

Replaced phase-history docs with `OVERVIEW / SUBSET / PIPELINE /
VERIFYING / ROADMAP` (+ `PINS.md` kept); archived `PLAN.md`,
`CIR_SUBSET.md`, `OWNERSHIP.md`, `SEMANTICS.md` to `docs/archive/`.
`tools/check.sh` is the single superset entry (old `check-phase*.sh`
kept for compat); CI runs `check.sh 100`.

## S1. Multi-function + `cir.call` — DONE (2026-09-27)

DAG-only calls, `Result`-bind translation. Design deltas from the
sketch: new `CStmt.callRet dst f args` (legacy `call` stays a stub,
never produced by `validate`); `Eval` gains a non-breaking program
layer (`Prog`, `findFunc`, `lookupArgs`, `evalProgStmt`,
`evalProgFunc`, + `seq`/`return` composition helpers) — depth-1
dispatch to call-free callees via the old `evalFuncFuel`, so no
existing lemma changed signature. `matchFrag` admits the two caller
shapes (bodies matched in a nested `match`: list patterns nested
inside `⟨⟩` Func patterns hit a Lean parser quirk). Leaves exclude
non-heap calls, so DAG holds by construction (no cycle expressible).
Rendered callers stay self-contained (`out/` sources lack oleans for
cross-file imports): leaf `Base` bodies inlined, call structure
certified by `addCallerFwd_as_calls` / `sumCallerFwd_is_call`.
Acceptance met: `add_caller` + `sum_caller` corpus (real CIRGen output,
`cir-opt` VERIFY-OK) translates, `evalProgFunc_addCaller` /
`evalProgFunc_sumCaller` proved, golden diffs, `DiffCalls` fuzz vs
native (tamper-checked), `GoldenCalls` 7/7 (recursion, unknown callee,
misshapen caller, call-in-leaf, call-escape), `CHECK-OK`.

## S2. Struct-by-value — DONE (2026-09-27)

Finished staged `Base` (`Point`/`pointTranslate`) through
`Eval`/`Emit`: new `CExpr.fget` (field projection; `cir.get_member` +
`cir.load` fused) + `CExpr.pmk` (`Point` construction; stores + return
fused), `fieldLookup` + per-op lemmas (`evalExpr_fget_*`,
`evalExpr_pmk_*`, `evalExpr_add_fget_var` bridge), `Base`
`pointTranslate_err_y`, canonical `translateFunc` + `translateFwd`
with ok/err bridges, `evalFuncFuel_translate` (all paths, any fuel),
`FragKind.translate`, `matchFrag` struct arm (direct `⟨⟩` pattern —
no S1 list-literal quirk: `fget`/`pmk` take strings/exprs, not
lists), `isTranslateShape` gate before the `get_member` misshapen
branch, rendered `translate_fwd` delegating to `pointTranslate`,
golden `StructByValue.lean`.
Acceptance met: `tests/c/struct_by_value.c` (real CIRGen output)
translates, verifies, fuzzes clean (`DiffStruct`, tamper-checked);
old struct rejection golden replaced by `GoldenStruct.lean` 5/5
(wrong arity, struct + call, passthrough, `get_member` on
non-structs); `GoldenPhase4` struct check is now a pipeline
acceptance; `CHECK-OK`.

## S3. C integer + control-flow hardening

### S3a. Control flow — DONE (2026-09-27)

New `CExpr.umul` (wrapping unsigned `cir.mul`) + `CExpr.ueq`
(unsigned `cir.cmp eq`) with per-op lemmas; new `CStmt.break_` /
`CStmt.continue_` with loop-scoped `Outcome.broke` / `.continued`
(`seq` propagates, `while_` catches `broke`→exit /
`continued`→next-iteration, top-level escape is `AssertFail`) plus
fuel-level composition lemmas. Four canonical funcs with
`emit_correct`: `nested_sum` (nested fuel induction, cost
`(n-k)*(m+1)`), `skip_sum` (`break` caps iterations at 9, so
default-fuel correctness is unconditional), `find_eq` (early return;
hit/miss loop theorems, over-long lengths `OOB` unless an early hit
fires), `cls` (`cir.switch` lowered to an if-chain, loop-free).
`matchFrag` arms use `body`-level matching throughout (deep `.seq`
patterns inside `⟨⟩` hit the S1 equation-compiler quirk).
Validator: `isNestedShape` / `isSkipShape` / `isFindEqShape` /
`isClsShape` (exact const pins) + `noBreakContinueSwitch` exclusions
in all older shapes + line-aware `cir.br` check (it is a substring of
`cir.break`) + shape-aware `cir.switch` exemption.
Acceptance met: four corpus entries (real CIRGen output, `cir-opt`
VERIFY-OK) translate, verify, fuzz clean (`DiffFlow`,
tamper-checked); `GoldenFlow.lean` 10/10; `CHECK-OK`.

### S3b. Width generalization — DONE (2026-09-27, scoped: 64-bit loop-free)

`i64`/`u64` end to end on the loop-free add shapes; everything wider
than the slice rejects loudly. New `Value.i64`/`u64` +
`CLit.i64`/`u64`; `add`/`uadd`/`umul`/`ult`/`ueq` dispatch on the value
tags (mixed widths are `AssertFail`) with per-op 64-bit lemmas;
`Base` gains `checkedAddI64` (+ range/ok/err/value/comm lemmas
mirroring 32-bit) and `cir_simp` includes it. Canonical `add64Func` /
`addu64Func` with `emit_correct` (+ ok/err corollaries for `add64`),
`FragKind.add64`/`addu64`, `matchFrag` arms, rendered `add64_fwd` /
`addu64_fwd`. Validator: `isAdd64Shape` / `isAddu64Shape` (exact
`!s64i`/`!u64i` pins), `nsw`-less signed-64 arithmetic folded into the
per-line wrapping check, dedicated 8/16-bit promotion rejection
(CIRGen lowers small widths through `i32` casts — probed — so there is
no native small-width arithmetic to model).
Acceptance met: two corpus entries (real CIRGen output, `cir-opt`
VERIFY-OK) translate, verify, fuzz clean (`DiffWidth` with
`INT64_MIN`/`MAX`/`UINT64_MAX` boundaries, tamper-checked);
`GoldenWidth.lean` 5/5 (width-mix, missing-`nsw`, promotion);
`CHECK-OK`.
Remaining widths work (deferred): small-width casts, 64-bit
loops/arrays/heap/structs, `checkedNeg`/`Div` at 64 bits, unifying the
32/64 checked-op lemmas behind one width parameter.

## S4. Tactics stage 1 + spec skeletons — DONE (2026-09-27)

Grew `cir_simp` (S4): call-unfold (`addCallerFwd_as_calls`,
`sumCallerFwd_is_call`; `Tactics` now imports `Circe.Emit` for the
bridge lemmas), struct-field (`pointTranslate_ok`, `pointTranslate_err_x/y`,
`translateFwd_*` bridges), wider-width (`inInt32Range`/`inInt64Range` +
iffs, `checkedAddI32/I64` ok/err), vec rules (`vecFillSumU32_correct`,
`vecNew`/`vecSet`/`vecGet`/`vecFree`, `prefixSumU32_full` + nil/zero/cons),
S3a flow folds (`nestedSumU32`, `rowU32`, `skipSumU32`, `findEqOut`,
`findIdxU32`), `Result`-bind automation (`result_bind_assoc`,
`result_pure_bind` beside the bind/map computation rules). One
deliberate omission: the bare `vecFillSumU32` unfold is *not* in the
set — it beats the `vecFillSumU32_correct` bridge in `simp` and stalls
`vec_correct`; the bridge alone fires.
Landed `out/*_Spec.lean` stubs (14, via `Circe.Emit.emitSpec` +
`GenOut`, dispatched on `matchFrag` like `emitFunc`): signature +
body reference + edge list + prop-test entry (`_check : Bool`, compared
with the `repr`-pretty-`==` the `Diff*` fuzzers use since `Except`
has no `DecidableEq` for `decide`).
Acceptance met: all 14 stubs typecheck, all 14 `_check` entries evaluate
to `true` (asserted in `check.sh`); `VERIFYING.md` example uses the
generated `SumArray` stub; `vec_correct` refactored onto the new set
(manual bridge listing → `cir_simp` + take fact, 11 lines → 8).

## S5. Tactics stage 2: loop + fuel + forward/backward helpers — DONE (2026-09-29)

Fuel automation + `choose` reasoning, no new subset. `cir_fuel`
(`Circe.Eval`, next to `EVAL_FUEL`: `EVAL_FUEL` normalization + `omega`
via explicit `first`-branching — a bare `try ... ; omega` misparses,
`try` swallowing the whole sequence when `simp` makes no progress)
discharges `≤ EVAL_FUEL` bounds and `remaining ≤ F` loop-fact side
conditions; `word32_lt_two32_of_fuel` collapses each wrapper's 5-line
fuel-to-word block to one `have`; `cir_choose b` (`Circe.Emit`, next to
`chooseFwd`/`chooseBack`: `cases` on an `elimTarget` + simp with the
forward/backward equations) closes get-put / put-get. Placement is
dependency-forced (`Tactics` imports `Emit`, so the macros live where
their names resolve); all three are in scope via
`import Circe.Tactics`.
Acceptance met: `emit_correct_sum` / `emit_correct_sum_oob` /
`emit_correct_vec` shortened onto the helpers, every `sum`/`vec`
loop-fact fuel side goal uses `cir_fuel`, both `choose` lens laws are
`by cir_choose b`; `VERIFYING.md` documents before / after; `check.sh`
asserts presence + adoption; `CHECK-OK`.
## Mid-term (after short-term solid)

## M1. Heap generics — LOCKED (2026-09-29)

Order: M1a → M1b → M1c → M1d. Each slice gated by shape +
`emit_correct` + golden before admission.

| Slice | Core change | Design pin |
|---|---|---|
| M1a two live `u32` blocks — DONE | `vec_copy_sum`: fill `a` / copy `a`→`b` / sum `b`, `vec2Fwd = vecFwd` (copy value-invisible); `isVec2Shape` (2×`malloc`, `freeCallCount = 2`); `DiffVec2` + `GoldenVec2` 6/6 | `Base` gained `vecCopyLoopAux` + contents lemmas (copy needs a spec/witness too); double-free gate refined to `free > malloc` (balanced-but-misshapen → heap-shape message) |
| M1b `u64` blocks — DONE | `vec_alloc_u64`: `Vec64` monomorphized mirror of `Vec32` (fill/sum loops, `vecFillSumU64` + `prefixSumU64` bridges); new `Value.vecVal64`, mixed-width access → `AssertFail` (S3b policy, pinned by `evalExpr_vget_mix/mix64` + golden runtime checks); `FragKind.vec64`, `isVec64Shape` (`u64` ret, disjoint from `isVecShape`), `DiffVec64` + `GoldenVec64` 6/6 | No `Vec α` polymorphism; single-block only (two-block `u64` would be a further slice) |
| M1c `realloc` — DONE | `vec_realloc`: `VecRealloc` grown-block fragment, `vecRealloc` preserves `min(old,new)` prefix, zero-fills growth, never fails (unbounded convention); `realloc(p,0)` / `realloc(NULL,n)` spellings rejected loudly | No OOM error path |
| M1d free discipline — DONE | Validator only: must-free → `freeCallCount ≤ expected` (leak = forgetting a value, sound; `vec_alloc_leak` corpus validates to the `VecAlloc` body); double-free / use-after-free stay loud via token, pinned by `GoldenFreeDiscipline` (13) | Relaxation is validator-side only |

Per-slice acceptance (standing convention): corpus C (real CIRGen,
`cir-opt` VERIFY-OK) → shape gate → proof → golden diff →
tamper-checked `Diff*` fuzz → rejection suite → `check.sh` stage →
`*_Spec` stub → `CHECK-OK`.
Non-goals: pointer arithmetic beyond stride loops, true aliasing (M3),
OOM, polymorphism, threads.

## M2. STL-free C++-lite — LOCKED (2026-09-30)

Value constructors/destructors, methods on POD, `new`/`delete` as
ownership ops. Still no inheritance/templates/EH/vtables. Structs (S2)
are the prerequisite; S1 `callRet` + depth-1 `evalProgFunc` dispatch
carries method/ctor calls (callees are call-free leaves, so DAG holds
by construction).

Probed CIR facts (pinned clang, `cir.lang<cxx>`): methods lower to
`cir.call @mangled(this, …)` with `this: !cir.ptr<!rec>`; ctor/dtor
defs carry `func_info<#cir.cxx_ctor / #cir.cxx_dtor>` markers; a local
with a dtor wraps the body in `cir.cleanup.scope { … } cleanup normal
{ dtor-call }` + trailing `cir.trap`; `new T{…}` is
`cir.call @_Znwm(size)` (nonnull, `allocsize`, `builtin`) + bitcast +
field stores; `delete` is a null-compare (`cir.cmp ne` vs
`#cir.ptr<null>`) + `cir.if` + `cleanup`-scoped sized
`cir.call @_ZdlPvm(ptr, size)`.

Locked decisions: `-fno-exceptions` pinned for all C++ corpus
(without it, dtor defs carry `cir.try` + `personality` and new/delete
carries `cleanup eh` regions; with it only `cleanup.scope` /
`cleanup normal` + `trap` remain — no-EH stays absolute); by-value
struct params deferred (`coerce` alloca + `bitcast` via
`can_pass_in_regs`; M2a corpus uses `const&` / `this` pointers, the
coerce pattern rejects loudly); single-`this` / single-ref uniqueness
via `nonnull + dereferenceable + noundef` attrs (SUBSET rule 1
amendment — `this` cannot carry `restrict` / `noalias`); `_Znwm` never
fails (unbounded convention, like M1 malloc/realloc).

Cross-cutting (once, before M2a): `emit-cir.sh` gains a `.cpp` loop
with `-fno-exceptions` (+ PINS: flags, `cir.lang<cxx>`, mangled-name
pins, `func_info` markers); `Validator.validateModule` validates every
defined func (`parseFuncs`; declarations skipped per S1 precedent);
`forbiddenOp` gains general `cir.trap` + `cir.cleanup` rejection with
shape-aware exemptions (both pass silently today); method/ctor/dtor
defs need no oracle facts (single-`this` + attr triple).

Order: M2a → M2b → M2c. Each slice gated by shape +
`emit_correct` + golden before admission.

| Slice | Core change | Design pin |
|---|---|---|
| M2a POD const-methods — DONE | `point_sum_ref(const Point&)`: method leaf (`this` + `get_member` x/y + `nsw` add — S2 body with pointer param) + ref-param caller via S1 `callRet`; no new CIR constructs | Exact mangled `callsFunc` pin (PINS); `this` binds a struct value (copy semantics); by-value coerce-pattern rejection pins the deferral |
| M2b value ctors + trivial dtors — DONE | `acc_two(a, b)` (ints only: the struct never crosses the boundary): new `CStmt.cleanup` (scope sequenced, `cleanup normal` at exit); ctor call → field-init, trivial-dtor call → no-op at validation | `cxx_ctor` / `cxx_dtor` markers + exact call multiset (1 ctor + 2 `add` + 1 `get` + 1 dtor, 5 sites) + const-`0` init pin + `trap` terminator; `cleanup` / `trap` admitted only here |
| M2c `new` / `delete` as ownership ops — DONE | `box_through(x)`: `Box32` value + affine `freed` token (Vec32 precedent at one word: `boxNew` never fails, `boxGet`, `boxFree`; double-`delete` / use-after-`delete` → `AssertFail`); sized `_ZdlPvm` with matching 4-byte size const; M1d leak relaxation admits the 1-`new`/0-`delete` spelling to the same body | `_Znwm` / `_ZdlPvm` join the heap-shape gate (excluded from `hasNonHeapCall`, dedicated misshapen + double-`delete` branches); null-guarded `cir.if` (ptr-`cmp ne` + `#cir.ptr<null>`) erased, `delete` inside `cleanup normal` erased (new exemption); `cir.trap` stays M2b-only |

Per-slice acceptance (standing convention, C++ adapted): corpus `.cpp`
(real CIRGen with `-fno-exceptions`, `cir-opt` VERIFY-OK) → shape gate
→ proof → golden diff → tamper-checked `Diff*` fuzz (C++ drivers) →
rejection suite → `check.sh` stage → `*_Spec` stub → `CHECK-OK`.
Non-goals: inheritance, templates, vtables, EH (`cir.try` /
`personality` / `cleanup eh` always rejected), non-const / static /
overloaded methods, operators, implicit copy/move ctors (avoided by
corpus construction; exact call-multiset pins make surprises reject
loudly), `std::nothrow` lowering (covered by never-fails),
polymorphism, threads.
## M3. Shrinking oracle trust — APPROVED (2026-10-01)

Goal: replace trust in `tests/oracle/verdicts.txt` + differential
testing with a proved transfer `oracle_noalias f → memEval f = Eval f`
on the admitted fragment. Trust base becomes CIRGen text +
Lean/Mathlib; verdicts stay as a checked cache, not a trust root.

Method (lightweight, not full Stacked Borrows): a small tag model just
strong enough for our three uniqueness sources — `__restrict__` /
`noalias` attrs, the C++ single-ref triple (`nonnull +
dereferenceable + noundef`), and disjoint `malloc` / `new` results.
No retag/protect generality beyond what the admitted shapes express.

State shape (locked): flat block map (`Mem`: next-address counter +
`Addr → Block` list-map; a block is a tag + width + word list).
`memEval` takes its own fuel bound alongside `EVAL_FUEL`.

Order: M3a → M3b → M3c → M3d. Each slice gated by model/lemma +
transfer + `check.sh` stage before admission.

| Slice | Core change | Design pin |
|---|---|---|
| M3a mem model skeleton (C only) — DONE (2026-10-02) | New `Circe.Mem`: flat block map + tags; `memEval` mirroring `Eval` for call-free C leaves + `sum` / `vec_alloc`. Tag creation at `restrict`-param bind + each `malloc`; load/store require a live tag. `Eval` untouched | C leaves + `sum`/`vec_alloc` first; no callers, no structs/flow, no C++. Transfer statement lands as a stub theorem, proved per-leaf only |
| M3b derived noalias (C only) — DONE (2026-10-02) | Per-shape noalias lemmas: each admitted C shape implies disjoint footprints (attr text for `restrict`; two-`malloc` disjointness by construction; length-pairing for stride loops). New `check.sh` stage asserts checked-in verdicts match the derived facts (cache, not trust) | `Oracle.lookupOracle` + `verdictAdmits` unchanged; new `derivedNoalias : RawFunc → Bool` implies `verdictAdmits`. No validator behavior change |
| M3c end-to-end transfer (C only) — DONE (2026-10-03: loop-free slice `choose`/64-bit widths/`cls`/`translate`; flow slice `nested_sum`/`skip_sum`/`find_eq`; caller slice `add_caller`/`sum_caller` via a new memory program layer; heap slices `vec_copy_sum` / `vec_realloc` / `vec_alloc_u64`; each with `oracleNoalias` witnesses + `memTransfer_*`) | Full `oracle_noalias f → memEval f = Eval f` for every admitted C `Func` (leaves, S1 callers, S2 `translate`, S3 flow, M1 heap, S3b widths). `check.sh` fails on verdict/derived mismatch | Transfer per-`FragKind`, reusing `emit_correct` bridges as the `Eval`-side; no new `Func` shapes. `Diff*` fuzz stays P0 but is no longer the soundness argument |
| M3d C++ follow-up — DONE (2026-10-04: N1a `methodSum` leaf + `pointSumRef` entry via the memory program layer; N1b `Acc` leaves + `accTwo` entry with `memEvalProgStmt_cleanup` sequencing; N1b `box_through` with new `boxNew`/`boxGet`/`boxFree` memory arms over single-word blocks + `MemConsistent` box disjunct; `check.sh` M3d stage) | Tags + single-ref (`this`/`const&` bind values — CoreIR has no field-store, so struct values are immutable and need no footprint; the attr triple justifies the copy) + box tokens (`Box32.freed` as affine tag); `cleanup`-scope and null-guard erasure justified in `memEval`. Transfer for M2a/b/c | Call-multisets + `cxx_ctor`/`cxx_dtor` markers become tag-creation points; `trap`/`cleanup` erasure mirrors the exemption gates. No inheritance/templates/EH/vtables |

Per-slice acceptance (M3 adaptation): model/lemma → per-shape
transfer proof → `check.sh` stage (verdict-cache assert from M3b on) →
existing goldens still green (no `.cir`/Emit churn expected) →
`CHECK-OK`. No new corpus unless a tag-creation point needs a pin the
text doesn't already carry.
Non-goals: full Stacked Borrows, OOM paths (never-fails stays),
polymorphism, threads, deleting `verdicts.txt` (stays as cache +
assert), removing `Diff*` fuzzing (stays as P0 signal).

## N. Toward a verification platform for modern C++ — delivered slices

(The N guiding principle and the active remainder live in `ROADMAP.md`.)

### N1. Close M3: C++ transfer (M3d) — DONE (2026-10-04)

Closed the trust story: `memTransfer` for all three M2 shapes, so C++
admission rests on tags + text pins rather than the attr triple taken
on faith.

- N1a: `this`/`const&` values — `memEvalFuncFuel_methodSum` +
  `memEvalProgFunc_pointSumRef`/`memTransferProg_pointSumRef`
  (single-ref params bind values; CoreIR has no field-store, so the
  footprint is empty and the attr triple justifies the copy).
- N1b: ctor/dtor + box tokens — `memEvalFuncFuel_accCtor/Add/Get/Dtor`
  + `memEvalProgFunc_accTwo`/`memTransferProg_accTwo` (`cleanup`
  sequences via `memEvalProgStmt_cleanup`); `boxNew`/`boxGet`/`boxFree`
  memory arms over single-word 32-bit blocks + `memEvalFuncFuel_boxThrough`/`memTransfer_boxThrough`
  (`MemConsistent` box disjunct, `vboxFree_lockstep`).
- N1c: `check.sh` M3d stage + C++ verdict story (`DerivedNoalias`
  pins `derivedNoalias = false` for C++ by design; leaf defs need no
  oracle facts; int-only entries keep the cache-agreement assert).

### N2. Viability past noalias — short-term

Today `validate` admits only proven-disjoint inputs. The next ring out
is code that is *safe but not statically disjoint*: shared immutable
borrows already exist (`sharedBorrow`); what is missing is (a) a
precise statement of what we accept and (b) loud, specific rejections
for what we do not.

- N2a: read-only sharing discipline — DONE (2026-10-04, model-side:
  `Circe.ReadOnly` pins the value-sound `const` shape as two
  `sharedBorrow` readers + owned length (`IsReadOnlyParams`,
  `twoReaderParams`), proves the footprints (`bindMemArgs_twoShared`,
  `twoShared_noalias`, `twoShared_consistent`) and alias soundness
  (`twoShared_alias_sound`: the aliased call `f(a, a, n)` reads
  identically through either pin), excludes any writer
  (`hasWriter_not_readOnly`, `writer_reader_excluded`), and
  `GoldenReadOnly` (5/5) pins that writer + reader still rejects loudly
  while the two-reader shape does not derive. Text-gate admission of
  multi-reader shapes (`derivedNoalias` / `validate`) is N2b/N2c work;
  no new corpus in this slice.
- N2b: interior rejection catalog — DONE (2026-10-04: `validate`
  reports per-cause messages instead of the catch-all: writer+reader
  (two or more live pointer params outside `choose`, `alias-reject`),
  escaping-borrow (pointer return with no pointer inputs,
  `escape-reject`; the ambiguous-inputs case keeps the existing
  borrow-return message), borrow-after-free (`free`/`delete` plus a
  pointer return, `escape-reject`), each pinned by
  `GoldenRejectCatalog` (3/3); the heap `vr` case (malloc + free +
  return-freed-pointer) and the N2a two-pointer case now assert their
  precise causes. No new admission: every cataloged input still
  rejects loudly.)
- N2c: `restrict`-recovery report — DONE (2026-10-04: probed CIRGen
  (pinned clang, raw CIRGen) on the evidence matrix and recovered the
  derivable gap from construction (M1a precedent) instead of demanding
  attr text:
  - `const` reader without `restrict` → no `llvm.noalias` (correctly
    silent: the source guarantees nothing) — still rejects, unless the
    shape is a proven single-reader (next bullet);
  - `const ... __restrict__` reader → `{llvm.noalias, llvm.noundef}`
    (control: attr present, unchanged path);
  - fresh `malloc`/`realloc`/`new` results → no `noalias` on the call
    result (fresh by construction; the heap shapes already consume this
    without demanding attrs — M1a precedent, unchanged);
  - single live array in an admitted reader shape (`sum` /
    `sum_caller` / `find_eq`) → `recoveredNoalias` (new
    `Validator` predicate, attr-blind by construction) carves the
    reader out of both the rule-1 and oracle-verdict gates; writers
    (`incr`, `choose`) and multi-pointer shapes never recover.
  - New corpus `sum_norestrict` (real CIRGen, zero `llvm.noalias`,
    `cir-opt` VERIFY-OK, oracle verdict honestly `unknown`) validates
    to the canonical `sumFunc` body and fuzzes clean (`DiffNorestrict`
    vs native); `GoldenPhase4` pipeline + `DerivedNoalias`
    recovery-agreement (`recovered=true`, `derived=false`, cache
    `unknown`) + `GoldenRejectCatalog` overreach negatives pin both
    sides. `derivedNoalias` stays strictly attr-demanding (M3b trust
    story untouched). No new `Func`: recovery reuses the whole sum
    pipeline, gate-only change.)
- N2d: two-reader admission — DONE (2026-10-12: the text-gate
  admission N2a deferred. New corpus `sum_two`
  (`uint32_t sum_two(const uint32_t *__restrict__ a, const uint32_t
  *__restrict__ b, size_t n)` returning the wrapping pairwise sum,
  real CIRGen, `cir-opt` VERIFY-OK, oracle verdict honestly
  `noalias`): `isSumTwoShape` pins two `noalias` pointers + length,
  one `cir.for`, two `cir.ptr_stride`, exactly two plain `cir.add`
  (no `nsw`), no calls/branches; the pair check exempts the exact
  shape (verdict still required — attrs are claims, the verdict
  confirms) and `derivedNoalias` admits it as the second two-pointer
  case (disjoint by construction under N2a). New `sumTwoFunc`
  (params exactly `twoReaderParams`, so the N2a footprint lemmas
  apply directly) with the `pairSum` fold forward (`OOB` past either
  array), value proofs (`emit_correct_sumTwo` + OOB, fuel EVAL_FUEL),
  footprint witness (`oracleNoalias_sumTwo` via `twoShared_noalias`)
  and memory transfer (`memTransfer_sumTwo` + OOB: reads agree on
  both sides), `FragKind.sumTwo` + structural match arm, tag-erased
  rendering + spec stub (6 edges incl. aliased readers and
  either-side `OOB`), `Specs` gallery equations (`sum_two_correct`
  via `pairSum_distrib`, `sum_two_aliased`, OOB). Pinned by
  `GoldenSumTwo` (8: pipeline + inconclusive/`mayAlias` verdicts +
  missing-`restrict` + `nsw` + single-add + `alias_add_restrict`
  probe + `sum_array`-not-sum-two shape-exactness), `DiffSumTwo`
  (eval-vs-forward on every trial, native in-range on `n`-prefixes
  incl. an aliased-readers leg, Lean-Lean `OOB`, 9 edges + 1000 fuzz
  trials), `DerivedNoalias` cache agreement and the `ScopeReport`
  row. Readers never write, so aliasing (`a == b`) is value-sound —
  the first slice that turns the N2a discipline into an admission.)

Non-goals: true mutable aliasing, raw-pointer arithmetic, lifetime
inference — if the discipline is not visible in CIR text, it rejects.

### N3. Spec + tactic support for real properties — DONE (2026-10-04)

`cir_simp` + `_Spec` stubs bootstrap the workflow, but proving
anything beyond `List.sum` shapes is still manual. Goal: a user
verifying an admitted function writes the statement once and the
tactics discharge the plumbing.

- N3a: one proved property per admitted shape in `Circe.Specs`
  (C remainder: callers, `translate`, flow, widths, `norestrict`; C++
  lifecycle: method leaf + entry, Acc ctor/add/get/dtor/two-sequence,
  box passthrough) — DONE. Delivered as plain-Lean equational specs
  over the `Emit` forwards (no spec DSL was needed: the forward
  functions already are the checked vocabulary).
- N3b: every `Specs` proof `cir_simp`-first (≤2 further steps); set
  grew by `accCtorFwd`/`accCtor`/`accGetFwd`/`accDtorFwd`, each enabling
  ≥1 proof; two proofs shortened to bare `cir_simp` — DONE (two
  sanctioned exceptions: conjoined conditional bridges in
  `translate_correct`, `by_cases` split in `cls_correct`; see
  `VERIFYING.md`).
- N3c: gallery of 3 end-to-end worked proofs (`fillSorted_u32`,
  `findEq_first_match`, `reallocPrefix_spec` in `Circe.Specs`,
  curated in `VERIFYING.md`, driver typecheck-gated) — DONE.
- Non-goals: a general program logic, framing automation beyond the
  admitted shapes — the shapes stay small enough that equational
  specs suffice.

### N4. C++ syntax coverage toward useful programs — all entries delivered (the `string_view` range-for remainder graduated to N7a below)

In admission order (each: probe CIR lowering → shape gate →
`emit_correct` → golden; stop at the first construct whose lowering
is not value-faithful):
- N4a: overloading + namespaces (name-mangling generalization of the
  M2a exact-name pins; no semantic change) — DONE (2026-10-04:
  `_Z3addii`/`_Z3addiii`/`_Z7use_addii` +
  `_ZN2ns3addEii`/`_Z10use_ns_addii`, gate + emit + transfer +
  golden/diff/spec green).
- N4b: move semantics + RAII on owned values (move = rebind + source
  invalidation, the affine-token story we already tell for
  `free`/`delete`; dtor-runs-on-scope-exit generalizes M2b `cleanup`)
  — DONE (2026-10-04: trivial `move_int` erases to `add`; `_ZN3AccC2EOS_`
  move-ctor leaf + nested-`cleanup` `move_acc` entry with the zeroing
  `assign`; `cir.cmp eq` early-return `scope_early` entry; `ueq`
  widened to width-polymorphic bit equality; program-level `if_`;
  gate + emit + transfer + golden/diff/spec green).
- N4c: monomorphized templates on value types (each instantiation is
  its own shape; no generic reasoning, mirroring the `Vec32`/`Vec64`
  monomorphization precedent) — DONE (2026-10-04:
  `_Z4taddIiET_S0_S0_`/`_Z4taddIlET_S0_S0_` leaves validate as
  `add`/`add64` with zero gate change; `_Z10use_tadd32ii`/
  `_Z10use_tadd64ll` entries via `isOverloadCallerShape` +
  `isOverloadCaller64Shape` with a dedicated wrong-shape rejection;
  `evalFuncFuel_add64At`/`memEvalFuncFuel_add64At` renamed-leaf
  lemmas; gate + emit + transfer + golden/diff/spec green).
- N4d: `std::` vocabulary types with value semantics —
  N4d-i `std::array<int, 4>` reads — DONE (2026-10-04:
  `_S_ref` unchecked-index leaf + `operator[]` single-delegation
  entry + 4-call `array_sum` entry with one fused edge;
  `idxi` u64-index read; gate + emit + transfer + golden/diff/spec
  green). N4d-ii `std::optional` guarded deref — DONE (2026-10-04:
  `_M_is_engaged` bit leaf + payload `_M_get` leaf + `has_value` /
  impl `_M_get` delegation entries + fused `operator*` leaf +
  2-call `opt_deref` entry with the `-1` sentinel; `optVal` +
  `optHas`/`optGet` with the disengaged `AssertFail`; the dead
  disabled-`__glibcxx_assert` skeleton dropped and gate-pinned;
  gate + emit + transfer + golden/diff/spec green).
  N4d-iii `std::span` index-sum — DONE (2026-10-04:
  `_M_extent` extent leaf + single-delegation `size` + fused
  `operator[]` with the dead disabled-assert skeleton pinned +
  by-value-span 2-call `span_sum` index-loop entry; `spanVal` +
  `spanLen`/`spanAt` with the `OOB` report; the checked-add
  `spanFold`; containment result — index-based is IN, range-for
  (`begin`/`end` iterator calls + pointer-chasing) is OUT with a
  deferral pin; gate + emit + transfer + golden/diff/spec green).
  N4d-iv-a `std::vector` reads — DONE (2026-10-04:
  `size` projection leaf + call-free fused `operator[]` leaf +
  `const&` 2-call `vec_read_sum` index-loop entry; `stdVecVal` +
  `stdVecLen`/`stdVecAt` with the `OOB` report; the checked-add
  `stdVecFold`; containment result — reads are IN, growth
  (`push_back` → reallocation) is OUT with a deferral pin; gate +
  emit + transfer + golden/diff/spec green).
  N4d-iv-b1 `std::vector` growth leaves — DONE (2026-10-04: the
  21 call-free leaf bodies of the 53-def `vec_push_sum` frontier
  over the owned-mutable triple (`buf`, `len`, `cap`) with the
  `[len, cap] ++ words` block; `_S_relocate` runs the `memmove`
  copy loop in lockstep with `stdVecBlitFold` (source pin framed,
  destination pin threaded); header-reading leaves take an
  `hlive` gate (use-after-free header reads are the one silent
  divergence); containment result — growth leaves are IN,
  multi-call composition is OUT with the dedicated composer pin
  (entry / `push_back` / `emplace_back` / `_M_realloc_insert`,
  deferred to N4d-iv-b2); gate + emit + transfer + golden/diff/
  spec green).
  N4d-iv-b2 `_M_realloc_insert` — DONE (2026-10-05: the 16-site
  growth composition over the frozen b1 leaves via the shared
  `vecGrowProg`, no inlining; `evalProgFunc` + `memEvalProgFunc`
  + `memTransfer` green, `VecGrowComposerRealloc*.lean` goldens
  byte-identical, spec stub mirror-agreement check true;
  containment result — `_M_realloc_insert` is IN,
  `emplace_back` / `push_back` / entry stay OUT with the
  composer pin).
  N4d-iv-b2 `emplace_back` — DONE (2026-10-05: the len/cap-guarded
  dispatch over the frozen b1 leaves via the shared `vecGrowProg`,
  no inlining; fast `construct`-at-`len`, slow realloc-insert at
  `pos = len` via additive `.callProg` (composer-calls-composer at
  fuel-1); `evalProgFunc` + `memEvalProgFunc` + `memTransfer`
  green, `VecGrowComposerEmplace*.lean` goldens byte-identical,
  spec stub mirror-agreement check true; containment result —
  `emplace_back` is IN, `push_back` / entry stay OUT with the
  composer pin).
  N4d-iv-b2 `push_back` — DONE (2026-10-05: the 8-site forwarder
  over the proved `emplace_back` composer via additive `.callProg`
  at depth `fuel - 1` (fuel `len + 3 ≤ F`); `evalProgFunc` +
  `memEvalProgFunc` + `memTransfer` green,
  `VecGrowComposerPushBack*.lean` goldens byte-identical, spec stub
  mirror-agreement check true; containment result — `push_back` is
  IN, entry admitted next).
  N4d-iv-b2 `vec_push_sum` entry — DONE (2026-10-05: the closed
  17-site script over the proved composers via the shared
  `vecGrowProg`, no inlining (fuel `6 ≤ F`, closed);
  `evalProgFunc` + `memEvalProgFunc` + `memTransfer` green,
  `VecGrowComposerEntry*.lean` goldens byte-identical, spec stub
  mirror-agreement check true; containment result — the full
  53-def frontier is IN, N4d-iv-b2 is complete).
  N4d-iv-c `std::vector::at` checked read — DONE (2026-10-12: new
  corpus `vec_at_one` (`return v.at(0)` on `const vector<int>&`,
  real CIRGen, `cir-opt` VERIFY-OK): three call-free fused Funcs
  (the `_M_range_check` guard leaf + the `at()` composer + the
  entry) over the admitted `size`/`operator[]` leaves; the noreturn
  `__throw_out_of_range_fmt` arm fuses to `fail`/`AssertFail`
  (deliberately distinct from `operator[]`'s catchable `OOB` — the
  throw aborts); the throw-message `get_global` +
  `array_to_ptrdecay` sites pin the arm textually via the
  `isVecRangeCheckExemptText` `forbiddenOp` exemption (cf.
  `isVecDtorExemptText`); value proofs + memory transfers +
  footprint witnesses green, tag-erased rendering + spec stubs
  byte-identical, `GoldenVecAt` (11: 5-pipeline + guard-stripped +
  throw-less + `lt`-flavor + direct-throw + unchecked-entry +
  bare-ptr) + `DiffVecAt` (eval-vs-forward every trial, native
  in-range on exact words, Lean-Lean OOB + native-abort leg, 6
  edges + 1000 fuzz trials) green; containment result — checked
  single reads are IN, checked sums (`at()` + `checkedAddI32`)
  stay OUT as the deferred follow-up).
  N4d-iv-d `std::vector::at` checked sum — DONE (2026-10-12: new
  corpus `vec_at_sum` (`s += v.at(i)` over `v.size()` with `nsw`
  adds, real CIRGen, `cir-opt` VERIFY-OK): the entry
  functionalizes to a call-free fused `while_` loop (the
  `vec_read_sum` precedent — `callRet` cannot appear inside loop
  bodies since `while_` delegates to the call-free evaluator, so
  fusion is structural). Per iteration the `_M_range_check`
  guard fuses to an `if_` around the inherited `stdVecBody`,
  the throw arm fusing to `fail`. Error precedence: the loop
  bound subsumes the guard, so `AssertFail` is dead-but-propagated
  (`vecAtSumBody_guard_false`) and the live failure is the `nsw`
  overflow — the forward is the inherited `stdVecFold`
  (`vecAtSumFwd := stdVecReadSumFwd`). Value proofs + memory
  transfers + footprint witness green, tag-erased rendering +
  spec stub byte-identical, `GoldenVecAtSum` (10: 5-pipeline +
  unchecked-entry + read-sum-not-at-sum + direct-range +
  double-at + bare-ptr) + `DiffVecAtSum` (eval-vs-forward every
  trial, native when the fold is `.ok`, Lean-Lean on `nsw`
  overflow, 8 edges + 1000 fuzz trials; no OOB leg — the bound
  makes it unreachable) green; containment result — checked
  `at()` sums are IN).
  V1 `vec_binary_search` (STD `std::vector` binary search) —
  DONE (2026-10-15: new corpus `vec_binary_search`
  (`while (lo < hi)` over `v.size()` with the safe midpoint
  `lo + ((hi - lo) >> 1)`, every element through `at()`, miss
  returns `v.size()`, real CIRGen): V1a extends the trusted
  evaluators with the u64 `bshr` arm + the `slt` ctor for `i32`
  element comparison (both with closed-eval spot checks); V1b
  functionalizes the entry to a call-free fused `while_` loop
  with a `let_`-prelude (`assign` needs bound targets).
  Midpoint Nat-correctness (`vecBinSearchMid_toNat`) + three
  body steps (hit / go-left / go-right) + fuel-generalized
  while induction (hit + miss soundness, `hi - lo` measure) +
  fuel agreement give `emit_correct`
  (`evalFuncFuel_vecBinarySearch`). The corpus initially
  returned `hi` on miss (collapse point, contradicting the plan
  and its own header comment) — fixed to `v.size()` and
  re-captured. Value proofs green, tag-erased rendering + spec
  stub byte-identical, `GoldenVecBinarySearch` (10: 5-pipeline
  + direct-index + at-sum/read-sum-not-binsearch + recursive +
  bare-ptr) + `DiffVecBinarySearch` (eval-vs-forward every
  trial, native on every input — no UB leg, 16 edges + 1000
  fuzz trials incl. `int32`-boundary and unsorted vectors)
  green; containment result — binary search over readonly
  vectors is IN, sortedness caller debt).
  V2 `vec_two_sum` (STD `std::vector` brute-force two-sum) —
  DONE (2026-10-15: new corpus `vec_two_sum` (outer `while (i < n)`,
  inner `j = i + 1`, `while (j < n)`, both elements through `at()`,
  checked `i32` add, hit returns early `IPair`, miss returns
  `(n, n)`, real CIRGen): V2a extends the trusted evaluators with
  the `.i32ofU64` narrowing ctor (the corpus casts `(int)i` /
  `(int)j` / `(int)n` explicitly — `structVal` holds 32-bit words
  only, so a u64 pair is inexpressible; wrapping mod 2^32, the V1a
  `slt` precedent) with closed-eval spot checks; V2b
  functionalizes the entry to nested call-free fused `while_` loops
  with a `let_`-prelude. Six body steps (inner hit / next /
  overflow, outer exit / assign-j-reset / assign-i-incr) + inner
  and outer fuel-generalized inductions (hit + miss + overflow
  soundness) + fuel agreements give `emit_correct`
  (`evalFuncFuel_vecTwoSum`). Value proofs green, tag-erased
  rendering + spec stub byte-identical, `GoldenVecTwoSum` (10:
  5-pipeline + direct-index + at-sum/binsearch-not-twosum +
  recursive + bare-ptr) + `DiffVecTwoSum` (eval-vs-forward every
  trial, native on non-overflowing inputs — the `nsw` loud leg is
  Lean-Lean only, 15 edges + 1000 fuzz trials incl.
  `int32`-boundary words, tamper-checked) green; containment
  result — brute-force two-sum over readonly vectors is IN,
  sortedness irrelevant).
  W `vec_at_set` (first STD `std::vector` mutable write) —
  DONE (2026-10-15: new corpus `vec_at_set` (mutable-borrow vector
  + `u64` index + `i32` value in, `void` out; straight-line: one
  non-const `at()` call, store through its result — the range check
  lives inside the leaf, real CIRGen): Wa probes the non-const
  leaves (structurally identical fusion under `_ZN` names; the
  mutable `operator[]` passes the existing index shape, the
  mutable `at()` needs its own gate over the mutable index name)
  and the borrow-store gap (`vgrowSet` is owned-triple-only, so Wb
  adds the new `CStmt.vecSet`: borrowed `stdVecVal` in-env
  `List.set`, loud `OOB`, mirroring `arrSet`, with eval + mem arms
  and a `beqStmt` arm). Wb functionalizes the entry to the fused
  guard + store (`if i < len then vecSet else fail`, updated words
  returned by `var` — the `xor_n` out-param idiom) with
  `emit_correct` (`evalFuncFuel_vecAtSet`). Value proofs green,
  tag-erased rendering + spec stub byte-identical,
  `GoldenVecAtSet` (10: 5-pipeline — entry + mutable composer +
  shared range_check + mutable index + shared size — plus
  direct-store + at-one/binsearch-not-atset + recursive +
  bare-ptr) + `DiffVecAtSet` (eval-vs-forward every trial, native
  vector-compare on hit, exit-4 pin on miss, 8 edges + 1000 fuzz
  trials, tamper-checked) green; containment result — one checked
  `at()` store through a mutable borrow is IN, the write
  capability captured at the entry, never by the leaf).
  M `vec_merge_into` (first STD three-loop entry, merge-sort
  kernel) — DONE (2026-10-15: new corpus `vec_merge_into` (two
  `const&` vectors + pre-sized mutable `out`, `void` out; main
  two-pointer loop with short-circuit `&&` + two drains; reads via
  const `at()`, writes via non-const `at()`; strict `<`, real
  CIRGen). Mb functionalizes the entry to guarded reads
  (`stdVecAt`) + guarded borrowed stores (`vecSet` + per-write
  `k < len`), the `&&` onto the pure ternary (`tif`), with
  `emit_correct` (`evalFuncFuel_vecMergeInto`) chaining three
  sequential loops at one model fuel (same-fuel `seq` threading,
  measure-exact fuels, fwd-bound side lemmas — no monotonicity).
  Value proofs green (6 while inductions + 3 bound lemmas + entry
  bridge), tag-erased rendering + spec stub byte-identical,
  `GoldenVecMergeInto` (12: 7-pipeline — entry + size + both `at()`
  composers + shared range_check + both index leaves — plus
  twosum/binsearch/atset-not-merge + recursive + bare-ptr) +
  `DiffVecMergeInto` (eval-vs-forward every trial, native
  vector-compare on hit, exit-4 pin on miss, 6 edges + 1000 fuzz
  trials incl. unsorted-input agreement and short-`out` misses,
  tamper-checked) green; containment result — the out-of-place
  two-pointer merge is IN, sortedness caller debt).
  C `vec_merge_sort` (first calls-in-loops customer: bottom-up
  sort through the ranged `merge_runs` callee) — DONE (2026-10-16:
  new corpus `vec_merge_sort` (ranged callee: `const&` vector +
  pre-sized mutable `tmp` + three `u64` bounds, `void` out, 10
  `at()` calls, three `cir.while` loops, one `cir.ternary`
  short-circuit `&&`; entry: two mutable borrows, `void` out, 4
  calls — one `size`, one `merge_runs`, two mut `at()` copy-back —
  three `cir.while` loops, two `cir.if` clamps; real CIRGen). C2
  proves the callee as the kernel proof twin (bounds are `u64`
  variables, not lengths) and the entry over it: lookup-based
  `SortInv` (shadow-tolerant — `callProg` conses a `tmp` binding
  per segment), segment length-preservation lemmas threading
  `n = length` through the pass loop, fuel-budgeted outer fuel
  with the N5a `fuel_step_down` idiom (no manual splits). Value
  proofs green (12 loop inductions — 6 callee + copy/segment/outer
  pairs — + bound/length side lemmas + two `evalProgFunc` entry
  bridges), two `matchFrag` arms (machine-generated literal
  patterns, `rfl`-verified) + shape predicates + tag-erased
  rendering + spec stubs byte-identical, `GoldenVecMergeSort` (22:
  8-pipeline — callee + entry + both `at()` composers + shared
  size/range_check/both index leaves — plus runs/sort cross-accepts
  and cross-rejects + mergeinto/twosum/binsearch/atset-not-shaped
  + recursive + bare-ptr) + `DiffVecMergeSort` (eval-vs-forward
  every trial — also validating model-fuel sufficiency — native
  word-compare on hit, exit-4 pin on miss, 18 edges + 1000 fuzz
  trials over both the ranged callee and the entry incl.
  partial-range merges and short-`tmp` misses, tamper-checked)
  green; containment result — calls inside loop bodies are IN
  (via the admitted callee), sortedness caller debt).

### N5. Proof ergonomics — DONE (2026-10-05)

N4d-iv-b2 was the most proof-heavy slice so far: composer fuel
side-goals, bespoke Fwd-cascade `simp only [...]` sets per composer
(plus `Except.map` leftovers per the `Span.lean` precedent).
Delivered, each adopted onto a b2 proof with an adoption assert:

- N5a: composer fuel automation — `fuel_step_down` lemma (one-`obtain`
  composer split: `k + 1 ≤ F` gives `F = F' + 1 ∧ k ≤ F'`; six b2
  sites adopted; negative driver gate `n5-no-manual-fuel-split`
  forbids the manual pair).
- N5b: composer cascade registry — `cir_step` cascade macro (eight
  span/read/entry steps adopted, `Except.map` by construction).
- N5c: spec-stub obligations — composer stubs name their owed gallery
  equations (`TODO (user)`, pinned per stub in the driver).

Non-goals (kept): proof search, SMT backends, `validate`/`emit`
semantics changes. No new trusted code, no validator/emit behavior
change. Suite green.

### N6. Language gaps (arithmetic + control flow) — DONE (2026-10-06)

Probes first, then wiring; every unwired remainder rejects through
one catalog branch with per-cause messages.

- N6a-i probes (2026-10-05): negation is `cir.minus nsw`,
  (un)signed div/rem are `cir.div` / `cir.rem` with signedness from
  the type, sub/mul carry `nsw`, all single-op lowerings (64-bit div
  included, no libcall), VERIFY-OK.
- N6a-ii: `neg` + `sdiv` (i32) wired with the pre-proved
  `checkedNegI32` / `checkedDivI32`.
- Probe fallout (P0 hole, fixed family-wide): multi-op functions
  validated to single-op bodies — `arithOpCount == 1` in all six
  arithmetic leaf gates.
- N6a-iii (2026-10-05): the unwired remainder (multi-op bodies,
  unsigned div/rem, signed sub/mul, shifts, bitwise, `nsw`-less
  minus) rejects with per-cause messages (13/13
  `GoldenRejectCatalog`; `intClass` uniformity guard preserves the
  `wmix` routing).
- N6b probes (2026-10-05): dense switches stay `cir.switch` at CIR
  level (no jump-table spelling — the if-chain covers all
  densities), fallthrough is an empty `cir.case` region,
  `break`-switches carry trailing code, case bodies can carry
  arithmetic.
- N6b-i (2026-10-05): `cls_fall` (empty `case 0` into `case 1`) +
  `cls_dense` (`0`..`7` + `default`) as exact shapes with
  per-region const pins + `arithOpCount == 0` (closes the
  unsigned-arith-in-case-body hole and the permuted-const hole in
  the old whole-text `cls` pins; 15/15 `GoldenFlow`).
- N6b-ii (2026-10-06): `cls_break` (`0`/`1`, no `default`, store +
  `break` per case, `99` initializer) as guarded assigns over a
  local (19/19 `GoldenFlow`).
- N6b-iii (2026-10-06): `cls_add` (wrapping `y + 1` / `y + 2` / `y`,
  `uadd` if-chain, dedicated compute-body rejection for the rest;
  23/23 `GoldenFlow`).

N6 language gaps complete (suite: 23/23 `GoldenFlow`, 13/13
`GoldenRejectCatalog`, CHECK-OK).

### N7. STD growth — DONE (2026-10-08)

- N7a: `string_view` range-for (2026-10-06: `cir.scope` + `cir.for`
  with `begin`/`end` as `get_member` projections; the admitted shape
  normalizes the pointer chase to an index fold over erased `u64`
  offsets with `sext8` byte reads; `GoldenView` + `DiffView` pin the
  one admitted range-for shape — span range-for stays OUT, same
  iterator lowering but a different monomorph).
- N7b: `reserve` (`capacity` leaf + guarded composer + closed
  `vec_reserve_sum` entry computing `1 + 2 = 3`, 55-def corpus,
  DiffReserve pin).
- N7c: `insert` (descending-blit shift + `_M_insert_aux` /
  `_M_insert_rval` / forwarder composers + closed `vec_insert_sum`
  entry computing `1 + 2 + 3 = 6`, 73-def corpus, `memTransfer` to
  `6`, DiffInsert pin — shift spare-slot, aux result, rval/insert
  router matrix incl. the full arm; 408 jobs TEST-OK, CHECK-OK).
- N7d: `erase` (ascending-blit shiftDown + `_M_erase` / forwarder
  composers + closed `vec_erase_sum` entry computing `1 + 3 = 4`,
  72-def corpus, `memTransfer` to `4`, DiffErase pin — shiftDown
  ascending-walk, core result, erase router matrix incl. the
  erase-last boundary; 409 jobs TEST-OK, CHECK-OK).

### N8. Proof scale-down — DONE (2026-10-08)

Collapsed the ~7k-line hand evaluations of closed entries to
`native_decide` behind the `cir_eval_closed` macro (entries restated
at concrete fuel; collapsed proofs carry argument comments per the
opacity decision), plus splits keeping files near the ~2k guideline.

- N8a: erase entries collapsed (`DecidableEq (Result Value)`
  lawful instance unblocking `native_decide`).
- N8b: insert entries collapsed + `InsertRouter` split out of
  `Insert`.
- N8c: `cir_eval_closed` macro (lives in `Eval/Core` beside its
  `DecidableEq` instance — `Tactics` imports `Emit`, so no
  back-import) + push/reserve entries collapsed +
  `n8-closed-eval-adoption` gate (every collapsed closed-entry
  proof goes through the macro).

### N9. Insertion sort over `std::array<uint32_t,4>` — DONE (2026-10-08)

One-algorithm user-proof case study: prove the emitted forward,
not arbitrary user programs. Unsigned elements keep the comparison
in the `ult` core; indices are `u64` per the N4d-i precedent.
A single `&mut` array is containment (no second ref can collide),
so the oracle needs no Iris.

- N9-i corpus: `tests/cpp/array_sort_sum.cpp` + `.cir` (4 defs,
  VERIFY-OK); the entry sorts `{3, 1, 2, 0}` and returns the sum.
- N9-ii shapes + gate + goldens: `u32` array sort shapes pinned,
  gate, `GOLDENARRAYSORT-OK` 9.
- N9-iii forward-as-fold + transfer: pure fold
  (`insertU32`/`sortL`/`outerListAux`) with CoreIR mirrors
  (`bubbleDown`, inner/outer `while` correctness by fuel
  induction with structural index splits),
  `evalFuncFuel_insertionSort`, mem side (`arrSet_lockstep`,
  `Transfer.SortSlice` re-induction with the block tracking the
  value list), closed sum entry computing `6` at fuel 7.
- N9-iv Sorted/Permutation spec:
  `evalFuncFuel_insertionSort_spec` (sorted ascending +
  `List.Perm` of the input).
- N9-v `DiffSort` fuzz: Lean-Lean eval/forward agreement plus an
  executable sorted+permutation oracle (8 directed edges + 1000
  LCG trials, `DIFFSORT-OK`); no native leg — the C++ entry
  prints only the permutation-invariant sum, so sortedness is
  pinned by the spec oracle here.
- N9b second monomorph (`std::array<uint32_t,8>`): new corpus
  (`tests/cpp/array_sort_sum8.cpp` + `.cir`; the entry sorts
  `{3, 1, 2, 0, 7, 5, 6, 4}` and returns `28`); new shapes
  (`isArrayAtU32_8Shape`, `isInsertionSort8Shape`,
  `isArraySortSum8Shape`) sharing the N=4 op-count cores; the
  closed entry computes `28` at fuel 15
  (`evalProgFunc_arraySortSum8Entry`); no new proofs — the
  N-parametric value + mem theorems already cover N=8.
  `GOLDENARRAYSORT8-OK` 7, the N=8 `DiffSort` leg (8 edges + 1000
  LCG trials), 3 N=8 reject probes.
- Acceptance: 444 jobs TEST-OK, CHECK-OK.

### N10. Per-family translation homes (`*Fwd` split) — DONE (2026-10-10)

`Circe/Base.lean` (1923 lines) mixed evaluator vocabulary with the
program translations the goldens render. The translations moved to
per-family value-level modules under unchanged names, next to their
proofs — `Emit/VecFwd` (M1 fill/sum/copy loops + whole-program
entries), `Emit/FlowFwd` (S3 folds + `findEq`), `Emit/M2Fwd` (C++
`Point`/`Acc`/`Box` bodies), `Emit/SumFwd` (wrapping prefix sums),
`Emit/GrowFwd` (bulk word-copy folds) — while `Base` (754 lines)
keeps evaluator vocabulary only (value/checked-op primitives, the
`Vec32`/`Vec64`/`Box32` types + block ops `Eval`/`Mem` call
directly). No proof touched: consumers resolve the same names
transitively, goldens import the home module (byte re-pinned), and
per-family `*-homes` gates pin the split (defs present in the `Fwd`
module, absent in `Base`).
- Acceptance: 430 jobs TEST-OK, CHECK-OK.

### K1. `u32` bitwise leaves (crypto op mix) — DONE (2026-10-10)

First crypto-track milestone: `xor_u32` / `and_u32` / `or_u32`
(total `cir.xor` / `cir.and` / `cir.or` on `!u32i`) and `shl_u32` /
`shr_u32` (`cir.shift(left/right, …)`, amounts ≥ 32 are `OOB` via
`checkedShiftU32`, the N6 shift-UB discipline). New `CExpr`
constructors (`bxor`/`band`/`bor`/`bshl`/`bshr`) with value + mem
eval arms, `Circe/Emit/Bitwise.lean` forwards with `emit_correct`
proofs, `Specs` gallery equations, `Transfer` theorems, N6-catalog
shapes with single-op exactness. The rotate-left composite is four
ops, so exactness rejects it (`rotl` reject row) — the quarter
round will compose the shifts explicitly. `DiffArith` grows five
native legs (Lean-Lean + C binaries, `OOB` amounts Lean-Lean
only) plus five pipeline-vs-golden VERIFY-OK rows.
- Acceptance: 461 jobs TEST-OK, CHECK-OK.

### K2. Bounded buffer-xor kernel — DONE (2026-10-10)

First crypto buffer entry: `xor_n` (`out[i] = a[i] ^ b[i]`,
`i in [0,n)`) over `__restrict__` buffers with a `u64` (`size_t`)
length. New `Circe/Emit/XorBuf.lean`: the entry `Func` (`mutBorrow`
out + `sharedBorrow` readers), the `xorNList` prefix-fold forward
with `OOB` past any buffer, loop-env + cond/body/correctness/`OOB`
lemmas (fuel induction mirroring the `sum` proofs, `simp only`
with the `toNat` bridge so `simp`'s `BitVec` mod-normalization
cannot strand the `arrSet` facts), and `emit_correct` + `OOB`
corollaries. Gate: `isXorNShape` (exact op-count shape over the
captured CIR) + dispatch + the single-`&mut` containment exemption
in the 2+-pointer pair check (verdict still required). New
`FragKind` (`.xorN`) with a structural match arm (bound literals
pinned, body exact), tag-erased buffer-result rendering, and a
spec stub whose mirror is the emitted body. `DiffXorN` (pipeline
leg, directed edges, past-`u32` length legs, fuzz vs the native
driver) + `GoldenXorN` (pipeline-vs-golden + 5 containment
rejections) ride the driver roster; spec stubs grow 105 → 106.
- Acceptance: 467 jobs TEST-OK, CHECK-OK.

### K3. Quarter-round fold + QR KAT — DONE (2026-10-10)

Pure-Lean ChaCha20 quarter-round spec for K4 to verify against
(no C corpus, no gate admission — by design, see SUBSET 28d).
New `Circe/Crypto/Qr.lean`: `rotlU32` with K1-leaf bridges,
`qrStep` (RFC 8439 §2.1), `qrAt` state applier with
length/untouched lemmas. The §2.1.1 vector
(`11111111/01020304/9b8d6f43/01234567` →
`ea2a92f4/cb1cf8ce/4581472e/5881c4bb`) is pinned by `decide` in
the library and cross-checked two independent ways before
check-in (6+ web sources agree; a from-pseudocode Python
implementation reproduces it — this caught a wrong `d` word from
memory, `...c925` vs `...c4bb`). `DiffQr` (KAT + zero + 1000
fuzz trials vs the test-only native driver) rides the roster
with a `k3-qr` content suite; no gate/validator/golden changes.
- Acceptance: 469 jobs TEST-OK, CHECK-OK.

### K4. ChaCha20 block vs §2.3.2 KAT — DONE (2026-10-10)

Full ChaCha20 block function over a single-`&mut` 16-word state,
verified end to end: real CIRGen corpus (`tests/c/chacha_block.c`
→ `tests/cir/chacha_block.cir`, 1413 lines: one `__restrict__`
u32 state buffer, void return, three `cir.for`, no calls) admitted
by exact op-count gate (`isChachaBlockShape`, no oracle change —
the pair check still demands the explicit `noalias` verdict).
New `Circe/Crypto/Block.lean`: `qrFrag`/`roundFrag`/`roundBody`/
`roundWhile`/`addWhile` fragments with forward-eval agreement
(`qrFrag_eval` via the 12-step bridge to the K3 `qrAt` fold,
`roundBody_eval`, `roundWhile_correct`, `addWhile_correct`) plus
the `OOB` corollary legs (short states error on every fragment
and the `Func`), and `emit_correct_chachaBlock`. Gate/match/render
wiring (`FragKind.chachaBlock`, `matchFrag_chachaBlock`,
`emitChachaBlockText`/`emitChachaBlockSpecText`); pipeline output
is byte-identical to the checked-in `tests/golden/ChachaBlock.lean`
(+ `_Spec.lean`, `spec_check=true`). The RFC 8439 §2.3.2 vector is
pinned three ways (Python reference cross-check at authoring time,
forward-KAT leg, native-vs-forward leg). `DiffChacha` (pipeline +
KAT + zero/short/long edges + 1000 fuzz trials vs the corpus-linked
native driver, eval-vs-forward agreement on every trial) +
`GoldenChacha` (pipeline-vs-golden + rename acceptance + 3
containment rejections) ride the driver roster with a `k4-chacha`
content suite; spec stubs grow 106 → 107.
- Acceptance: 475 jobs TEST-OK, CHECK-OK.

### K5. SHA-256 compress vs FIPS 180-4 §8.1.1 "abc" KAT — DONE (2026-10-12)

Second crypto primitive over a single-`&mut` 24-word state (8 digest
+ 16 block), verified end to end: real CIRGen corpus
(`tests/c/sha256_compress.c` → `tests/cir/sha256_compress.cir`,
678 lines: one `__restrict__` u32 state buffer, void return, five
`cir.for`, no calls) admitted by exact op-count gate
(`isSha256Shape`, no oracle change — the pair check still demands
the explicit `noalias` verdict). New `Circe/Crypto/Sha.lean`: the
value-level fold (`sha256CompressFwd`, tail passthrough) with the
FIPS §8.1.1 "abc" vector proved by `decide`
(`sha256Compress_kat`). New `Circe/Crypto/ShaBlock.lean`:
`initWhile`/`schedWhile`/`vinitWhile`/`compressWhile`/`shaAddWhile`
fragments with forward-eval agreement plus the `OOB` corollary
legs. New `Circe/Crypto/ShaFunc.lean`: whole-function
`evalFuncFuel_sha256` (+ `_oob`) collapsing to `emit_correct_sha256`
at the default fuel. Gate/match/render wiring
(`FragKind.sha256Compress`, `matchFrag_sha256Compress`,
`emitSha256CompressText`/`emitSha256CompressSpecText`); pipeline
output is byte-identical to the checked-in
`tests/golden/Sha256Compress.lean` (+ `_Spec.lean`,
`spec_check=true`). The "abc" vector is pinned three ways
(`decide` KAT, forward-KAT leg, native-vs-forward leg). `DiffSha`
(pipeline + KAT + zero/short/long edges + 1000 fuzz trials vs the
corpus-linked native driver, eval-vs-forward agreement on every
trial) + `GoldenSha` (pipeline-vs-golden + rename acceptance + 3
containment rejections) ride the driver roster with a `k5-sha`
content suite; spec stubs grow 107 → 108.
- Acceptance: 588 jobs TEST-OK, CHECK-OK.

### K6. ChaCha20 stream vs RFC 8439 §2.4.1/§2.4.2 — DONE (2026-10-24)

First multi-block stream cipher and first call-in-loop program,
verified end to end (pillar-1 guiding algorithm for the G1 gap):
real CIRGen corpus (`tests/c/chacha20_encrypt.c` →
`tests/cir/chacha20_encrypt.cir`, 688 lines: one outer `cir.while`
over full 16-word blocks, two `cir.for` xor loops, one `cir.if`
tail guard, two `cir.call @chacha20_block` sites — one in the loop
body, one in the tail branch; no div/mul/rem) admitted by the exact
caller-shape gate (`isChacha20EncryptShape` plus the caller-side
alias exemption, SUBSET rule 9 G1; the callee is the call-free K4
leaf and resolves by name against the program at the same fuel).
New `Circe/Crypto/Stream.lean`: the fuel-threaded forward
(`chacha20EncryptFwd` over `encLoopFwd`) and its fuel-free twin
(`chacha20EncryptList`), proved equal at sufficient fuel; the
chain-prefix environment discipline (`s`/`ntail` bindings shadow
the fixed-shape env, so lookups/updates lift over the stale
prefix); `setupFrag`/`xorBody`/`xorLoop`/`xorFull`/`blockCall`/
`fullIter` fragment agreements; the outer fuel induction
(`outerWhile_post`: one fuel per full block plus 16 for the tail)
with wrap-free guard arithmetic (`nwords + 16 < 2^64`); the tail
phase (`tailNtail_ok`, `tailIf_empty`/`tailIf_nonempty`);
outer-plus-tail with the trailing return (`outerTail_correct`);
whole-function agreement (`evalProgFunc_chacha20Encrypt`)
collapsing to `emit_correct_chacha20Encrypt` at the default fuel.
Bounds are stated, not hidden: `nwords ≤ 4096` (C array plus
fuel), `nwords/16 < 2^32` (`u32` block counter), wrap-free guards.
The §2.4.2 "Sunscreen" vector (28-word prefix: one full block plus
a 12-word tail) is pinned four ways — `native_decide` list KAT
(`kat_chacha20_list`, kernel-checked) plus its end-to-end eval
corollary (`kat_chacha20_eval`), the forward-KAT leg, the
native-vs-forward leg, and eval-vs-forward agreement on every
fuzz trial (this caught a mistranscribed KAT word, `0x6f20756f`
vs `0x6f75756f`). `DiffChacha20Encrypt` (pipeline + KAT +
zero/short/long/OOB edges + fuzz vs the corpus-linked native
driver) + `GoldenChacha20Encrypt` (pipeline-vs-golden
byte-identical + `_Spec.lean`, `spec_check=true`) ride the driver
roster. K6c (2026-10-24): input-OOB proof twins proved —
short key (`evalProgFunc_chacha20Encrypt_key_oob`: `setupRest`
fold induction over the 16 stores, constants peel, first
missing key word fails; two-path whole-function assembly),
short nonce (same induction with long-key/counter prefix,
`setupRest_nonce_oob`), short message
(`xorLoopMsgFirst_oob`/`xorLoopSFirst_oob` xor-loop inductions
for the message-read-first and keystream-read-first regimes,
`tailFrag_msg_oob` shared tail assembly,
`outerWhile_msg_oob` loop-err/exit-ok sum induction,
`outerSkipped_msg_oob` loop-skipped path). The documented
divergence stands and is now fenced: `(short key, nwords = 0)`
returns without touching the key (empty-message early return),
so the key/nonce twins carry `nwords ≠ 0`; the message twin
needs no such side condition (`msg.length < nwords.toNat`
already excludes `nwords = 0`). Bounds: message within the
4096-word buffer, fuel covers the remaining words plus the
block-call depth. The while-plumbing both xor inductions
share (failing-iteration close, successful-iteration step,
`i`-bound guard) is factored into `Circe/Crypto/LoopOob.lean`
(`whileErr_of_bodyErr`, `whileStep_of_bodyOk`, `iterGuardT`)
with the short-read-loop recipe; both inductions are rewired
onto it, read-miss evals staying per-loop.
- Acceptance: 456 jobs TEST-OK, CHECK-OK.

### N11. First writer admission: sequential reborrows (F1) — DONE (2026-10-12)

First mutable writer through a borrowed reference: `alias_reborrow`
(`int&` in, `void`, `r += 1` then `s += 2` through two loans to one
address), functionalized value in / updated value out — the `incr`
precedent with two sequenced checked adds. The fusion is licensed
gate-side, not proved: L2-ordered disjoint writer ranges
(`hasSequentialWriterRanges`) plus one F0-resolved address
(`reborrowSameAddress`: both derived writers ultimate to `param0`)
mean the text computes `x + 1 + 2` through one cell; checked-add
order is unobservable (uniform `.Overflow`), but the gate pins the
corpus order exactly anyway (3 allocas / 6 loads / 5 stores /
2 consts / 2 `nsw` adds, `1`/`2` consts consumed in order, no
calls / comparisons / branches / loops / scopes —
`isReborrowShape`; anything else sequential-writer-shaped keeps the
deferred message). New `Circe/Emit/Reborrow.lean`: `reborrowFunc`
(the mangled entry name, so GenOut and pipeline agree),
`reborrowFwd` with ok/err1/err2 bridges, `evalFuncFuel_reborrow`
(+ `emit_correct` + err/ok corollaries) reusing the `add3`
seq/let skeleton. New `Circe/Eval/Core.lean`
`evalExpr_add_var_lit` + `Circe/Mem/Model.lean`
`memEvalExpr_add_var_lit`: all-variable `add`-of-var-and-lit
forwarding, the BitVec-literal-discipline fix — separately
elaborated `1 : BitVec 32` terms do not match syntactically
(`1` vs `1#32`), so literal hypotheses rewrite with `rw`, never
as `simp` arguments (a deep nested `matchFrag` arm also timed out
the equation compiler; the arm matches two-level via
`isReborrowBody`). New `Circe/Transfer/Slice.lean`
`memEvalFuncFuel_reborrow` (Mem threaded untouched through both
adds) + `memTransfer_reborrow` (both sides equal the forward);
`bindMemArgs_reborrow` / `oracleNoalias_reborrow` mirror `incr`
(borrow functionalized, empty footprint). Gate/match/render
wiring (`isReborrowShape` admission before the deferred branch,
`FragKind.reborrow`, `matchFrag_reborrow`,
`emitReborrowText`/`emitReborrowSpecText` with ground-truth spec
edges); pipeline output is byte-identical to the checked-in
`tests/golden/Reborrow.lean` (+ `_Spec.lean`, `spec_check=true`).
`DiffReborrow` (eval-vs-forward on every trial, 7 edges + 1000
fuzz trials vs the corpus-linked native driver observing `*x`,
Lean-Lean only on `nsw` overflow) + `GoldenReborrow`
(pipeline-vs-golden with no oracle facts + 4 corpus-transformed
rejections + `incr` shape-exactness) + reworked `ReborrowGate`
(predicate pins + admission check + `cond` message) ride the
driver roster with an `f1-reborrow` content suite; spec stubs grow
113 → 114; `GoldenAliasProbe` gains its third admit control.
- Acceptance: 630 jobs TEST-OK, CHECK-OK.

### N12. Disjoint writer-pair admission (G2, first multi-output) — DONE (2026-10-13)

Two disjoint mutable writers through `__restrict__` pointers:
`wr_pair` (`*p += 1`, `*q += 2`), functionalized to the updated
pair — the `incr` precedent doubled with the G1 `pair` carrier
(`structVal "IPair"`, tag-erased to `BitVec 32 × BitVec 32` in the
rendering). Disjoint writes commute, so no L2 sequencing license is
needed (unlike N11); the license is gate-side and twofold: the
in-order dataflow pin (`wrPairDataflow` — each add feeds its
in-order store into its in-order param cell from that same cell,
chased through the reload loads with the fuel-bounded
`chaseLoadAlloca`; rejects the same-cell, swapped, and cross-read
near-misses with identical op counts) plus the explicit `noalias`
verdict (attrs are claims, the verdict confirms —
inconclusive/`mayAlias` verdicts keep dedicated `alias-reject`
codes). Exact shape: `void`, two non-single-ref `i32` pointer
params, 2 allocas / 6 loads / 4 stores / 2 consts / 2 `nsw` adds,
no calls / comparisons / loops / branches / scopes
(`isWrPairShape`; the pair-check exemption and the third
`derivedNoalias` two-pointer arm). New `Circe/Emit/WrPair.lean`:
`wrPairFunc`, `wrPairFwd` with ok/err1/err2 bridges (pair matches
reduce definitionally after both discriminants rewrite — no
`dsimp`), `evalFuncFuel_wrPair` (+ `emit_correct` + err/ok
corollaries) on the two-let/return skeleton, `isWrPairBody`
(two-level `matchFrag` arm from the start). New
`memEvalExpr_pair_ok` (mirror of `evalExpr_pair_ok`); new
`Circe/Transfer/Slice.lean` `memEvalFuncFuel_wrPair` (Mem threaded
untouched; Mem-side `let_pure` concludes with `::`-cons envs, so
post-let facts use the literal cons form) + `memTransfer_wrPair`;
`bindMemArgs_wrPair` / `oracleNoalias_wrPair` mirror `incr`
(empty footprint — the aliased-caller case is caller-UB under
`noalias`, so no N2a-style alias-soundness leg exists).
Gate/match/render wiring (`isWrPairShape` admission after
`sum_two`, `FragKind.wrPair`, `matchFrag_wrPair`,
`emitWrPairText`/`emitWrPairSpecText` with verified ground-truth
spec edges); pipeline output is byte-identical to the checked-in
`tests/golden/WrPair.lean` (+ `_Spec.lean`, `spec_check=true`).
`DiffWrPair` (eval-vs-forward on every trial, 7 edges + 1000 fuzz
trials vs the corpus-linked native driver observing both cells,
Lean-Lean only on `nsw` overflow, tamper-checked: `+5` perturbation
fails exactly one job) + `GoldenWrPair` (pipeline-vs-golden under
`noalias` + 5 corpus-transformed rejections + `incr`
shape-exactness) + `WrPairGate` (6 corpus predicate rows + 3
adversarial dataflow rows + admission + message routing) +
`ScopeReport` rows (flat locals, overlapping L2 ranges, different
F0 roots) + `DerivedNoalias` agreement ride the driver roster with
a `g2-wrpair` content suite; spec stubs grow 114 → 115.
- Acceptance: 639 jobs TEST-OK, CHECK-OK.

### N13. Branch-writer admission (G2b, noalias cond) — DONE (2026-10-13)

One conditional writer plus one unconditional writer through
`__restrict__` pointers: `cond_pair` (`*p += 1` under `c`,
`*q += 2` always) — the C-pointer twin of the deferred
`alias_cond`, made sound by the `noalias` verdict (the G3
investigation showed B2 scalar stores are neither sufficient nor
necessary for the unknown-verdict twin: transfer discards `Mem`,
and `bind` cannot express caller aliasing, so full framing needs
a new caller-side contract kind — deferred). Functionalized with
the lazy `tif` (`a = c ? p + 1 : p`, masking the first add and
its overflow when `c = false`) plus the G1 `pair` carrier; the
forward matches on `c` (not `if` — an `if`'s `Decidable` instance
gets stuck under `rw`'s closer) in body evaluation order
(branch first, so short-circuits agree on both sides with no
uniformity argument). Exact shape: `void`, two non-single-ref
`i32` pointers plus `bool`, one scope-wrapped `cir.if`, 3
allocas / 7 loads / 5 stores / 2 consts / 2 `nsw` adds, plus
branch placement (first run strictly inside the `if` region
— region-path proper prefix — second run outside, condition
chased to the `bool` slot). New `Circe/Emit/CondPair.lean`:
`condPairFunc`, `condPairFwd` with ok-true/ok-false/err-q×2/err-p
bridges, `evalFuncFuel_condPair` (branch × outcome cases)
(+ `emit_correct`); `isCondPairBody` (two-level `matchFrag`
arm). `memEvalFuncFuel_condPair` reuses the `tif` agreement
lemmas on both sides (no new model — the step-0 probe found
everything present) + `memTransfer_condPair`;
`bindMemArgs_condPair` / `oracleNoalias_condPair` (empty
footprint). Pair-check exemption + fourth `derivedNoalias` arm
(mechanical theorem extension). `DiffCondPair` (10 edges incl.
both legs, masking, and both overflows + 1000 fuzz trials,
in-range native, Lean-Lean overflow, tamper-checked: `+9`
perturbation fails exactly one job) + `GoldenCondPair`
(pipeline + 5 rejections + `wr_pair` shape-exactness) +
`CondPairGate` (7 corpus + 4 adversarial branch rows + admission
+ message) + `ScopeReport` (flat cells + `bool`, overlapping L2
ranges, `c` value-rooted) + `DerivedNoalias` ride the roster
with a `g2b-condpair` content suite; spec stubs grow 115 → 116.
- Acceptance: 648 jobs TEST-OK, CHECK-OK.

### N14. Unknown-verdict branch-writer admission (G3 full framing) — DONE (2026-10-14)

S0 spike (report-only, `/tmp` scratch): a `Mem` program mirroring
the cond body plus `cellAt` hypotheses inverts to per-cell posts
under both verdicts — GO on a Mem-space open contract, NOT
OpenFunc (reuses `cellAt` / `memStore_cell` /
`memFind_memStore_other`, executable via `memAllocData`). S1 B2
scalar store (`CStmt.mstore` slot-addressed through the `Layout`
pin; pure side `AssertFail` by design — cell stores are
`Mem`-space, open contracts prove Mem-direct) + equation lemmas.
S2 opt-in pinning (`BorrowRole.pinnedCell`; `bindMemArgs`
matches `(role, value)`, disjoint-pair entry; every delivered
`rfl` bind re-verifies, old roles byte-identical). S3: S0
promoted to `CondFrame`, `CExpr.mload` + general
`memEvalExpr_add_ok`, `isAliasCondShape` (5 loads + triple,
shares `condPairDataflow`), verdict-independent admission arm
emitting `aliasCondFunc` (`pinnedCell` params, `mstore` /
`mload` body, `void` as zero word), 4-leg transfer (pinned ×
masked, caller-`Mem` aliased × masked) over the emitted body,
`FragKind.aliasCond` + `_spec` render with caller-supplied
`aliased` (the pipeline's silent-empty emission for
fragment-less admissions forced the render into S3 — no
silent empty). S4: goldens byte-identical (`spec_check` true
on 9 edges), `AliasCondGate` (pred + 4 adversarial + 2
admissions + message) + `GoldenAliasCond` (pipeline × 2 +
verdict-independence + 3 rejections + shape-exactness),
`DiffAliasCond` (10 edges + 1000 LCG trials, spec mirror vs
`Mem` evaluation of the emitted body vs native C++, both
verdicts; tamper-checked: driver `q+5` fails at the first
trial with the exact delta, restored green). S4b finding: the
masked leg under aliasing reads the shared cell, so both words
read back the stored result (`(10, 12)` → `(12, 12)` — caught
by the third (`Mem`) path, fixed in mirror + render + spec +
edge; the transfer leg already stated the single-cell post).
Suites ride the roster with a `g3-aliascond` content suite
(19 pins); spec stubs grow 116 → 117.
- Acceptance: 657 jobs TEST-OK, CHECK-OK.

### H1. Hoare rule library + gallery — DONE (2026-10-14)

H0 spike (report-only, `/tmp/hoare/h0.lean`, 167 lines,
sorry-free): `HTriple` def + skip / seq / consequence /
mstore-with-frame rules + two-cell `pa[0] += 1; pb[0] += 1`
gallery with framing — GO verdict (triples are thin sugar over
the equation lemmas, no new semantics). H1a:
`Circe/Hoare/Def.lean` + `Circe/Hoare/Rules.lean` (adds
`htriple_if_true/false` over plain `.b` guards — no narrowing
was needed; `htriple_return` with `.returned` post;
`hexpr_mload` expression helper — `mload` has no value mirror
by design, so loads live inside `mstore` value expressions;
index-0 pin documented complete — `cellAt` is singleton).
Guards take no fuel argument (`memEvalExpr` is fuel-free).
H1b: `tests/lean/HoareGallery.lean` compile-gated lakefile
root (dogfoods `hexpr_mload`) + this VERIFYING section.
Deferred with reasons named: seq-return propagation (no
Mem-side lemma), multi-word indexed assertions (H2 loops).
- Acceptance: Hoare files warning-free, gallery sorry-free,
658 jobs TEST-OK (657 + `hoare-gallery`).

### H2. Loop rules + alias_cond / countdown galleries — DONE (2026-10-14)

H2a: `memEvalStmtFuel_while_false` / `while_true` equations
beside the handlers, `HTripleAt` + `htriple_at_of`,
`htriple_while_at` (fuel-indexed invariant) and
`htriple_assign` in `Circe/Hoare/Rules.lean`, plus
`heval_usub_u32` / `heval_une_u32` value-side expression
lemmas. H2b: `hoare_aliasCond_true/false` triples over the
real `aliasCondFunc.body` (if-rules + framing + void return)
and `hoare_countdown` (`u32`, fuel index as bound); driver
`hoare-gallery` grows to 4 closed-instance jobs. Scope note:
the planned `cond_pair` gallery became `alias_cond` — the
real `cond_pair` body is `tif`+lets with no `if_` statement,
so it cannot exercise the if-rules; it needs a new
`htriple_let` rule and moves to H3. Multi-word indexed
assertions shipped in §A below (`cellsAt`).
- Acceptance: Hoare files warning-free, galleries sorry-free,
658 jobs TEST-OK (`HOAREGALLERY-OK passed=4`).

### H3. Let-rule + cond_pair gallery + micro-tactics — DONE (2026-10-14)

H3a: `memEvalExpr_add_agree` / `pair_agree` (mirroring
`usub_agree`), `htriple_let`, `heval_usub_u32` /
`heval_une_u32` value-side helpers;
`hoare_condPair_true/false` over the real `condPairFunc.body`
(`tif` + lets + pair return; the `¬c` case owes no `p` debt —
masking made explicit); driver `hoare-gallery` grows to 6
closed-instance jobs (pure-env `cond_pair` × 2). H3b,
measured: `hoare_lit_eval` + `hoare_guard_of` land in
`Circe/Hoare/Rules.lean`, the gallery rewrites onto them
(≈ 50 lines removed: seven lit blocks, five dead value
haves, two guard closures); grand `cir_hoare` rejected (frame
arguments not inferable), `hoare_eq` macro tried and
abandoned with reason (no `at`-splicing on this toolchain;
obtain-only flips the elimination side). Multi-word indexed
assertions shipped in §A below (`cellsAt`).
- Acceptance: Hoare files warning-free, galleries sorry-free,
658 jobs TEST-OK (`HOAREGALLERY-OK passed=6`).

### A. Whole-list assertions + read-only sum loop — DONE (2026-10-14)

A1: `cellsAt m a t l := memFind m a = some ⟨t, true, l⟩` in
`Circe/CondFrame.lean` generalizes singleton `cellAt`, with
`cellAt_cellsAt`, `memStore_cellsAt`,
`memFind_cellsAt_store`, `memLoad_cellsAt`. A2:
`hoare_sumLoop` in `tests/lean/HoareGallery.lean` (read-only
`while (i < len)` accumulation, total in a framed singleton
cell; per-prefix `checkedAddI32` debt `hdebt`, `u64` lengths
`hn`; memory floats existentially — see VERIFYING). Driver
`hoare-gallery` grows to 7 closed-instance jobs (`[1,2,3,4]`
totals 10).
B: `hoare_incrLoop` — in-place `arr[i] = arr[i] + 1` over one
block (no side cell); invariant carries the evolving prefix
(`take`/`map`/`drop`), per-word debt `hdebt`. Driver grows to
8 closed-instance jobs (`[1,2,3]` gives `[2,3,4]`).
- Acceptance: Hoare files warning-free, galleries sorry-free,
658 jobs TEST-OK (`HOAREGALLERY-OK passed=8`).

### Iris spike report — DONE (2026-10-12, report only, no migration)

Time-boxed evaluation of `iris-lean` for heap reasoning: no
`validate`/`Emit`/transfer churn, no vendored dependency (pin
mismatch — `iris-lean` at `lean4:v4.21.0` vs our `v4.34.0` —
plus a moving `Qq`). Scope is the MoSeL proof interface only;
even vendored it yields BI/separation-logic tactics, not Iris
program logic. It replaces neither the oracle (M3b verdicts stay
a checked cache) nor the `Mem` tags (disjoint-by-construction +
single-`&mut` containment transfers stand). Verdict: no
migration. Residue routing from the A-track probe (12 rows, zero
false-accepts): conditionally-live writers (`alias_cond`) are the
one case needing framing beyond equational specs (first concrete
Iris-spike input); sequential reborrows want an L-track consumer;
`noalias` reader pairs, closed two-alloca shapes, and free
single-`&mut` writers are shape admissions. Revisit trigger: a
slice admitting `alias_cond`-class framing (needs lifetime
evidence too — framing without live-range facts has nothing to
attach to).

Trigger status 2026-10-16: FIRED on both legs (N14/G3 admitted
`alias_cond`-class framing with verdicts PROVEN; L1/L3 supply
first/last-use facts and caller-dependent footprints — see L5).
Decision: DEFER revisit, continue pillar work. Native framing
keeps winning on burden (F2: two helpers + two theorems), and
the L2/L3 spikes confirm no lifetime-side consumer is waiting on
logic-level framing.
Known limitations of the native path (what Iris would buy when
deferral ends): per-shape posts — each new conditional shape
re-pays a bespoke `condPost` proof, with no general frame rule
carrying untouched locations through for free; `Mem`-boundary
store equations stay hypotheses under the S0 open contract
instead of discharged writes; no BI/separation-logic tactics,
so each shape re-derives its frame manually. What we hope Iris
(MoSeL interface) achieves then: a reusable frame rule + tactic
support once shapes multiply past the bespoke-post budget.
Deferral ends on F2's line — a second conditional shape, or a
`Mem`-level write need — at which point re-check the vendoring
blockers (pin mismatch `v4.21.0` vs `v4.34.0`, moving `Qq`) in a
fresh time-boxed spike.

### L. Lifetime-relevant evidence (extract-only) — DONE (2026-10-04..12)

Raw CIRGen carries no lifetime markers, so this track extracts
lexical lifetime evidence with golden pins and wires no
consumers (`validate`/`Emit`/transfer untouched throughout).
L1 (2026-10-04): per-function scope/alloca tree (`extractScopes`:
brace-depth fold, alloca birth depths, loud imbalance);
`ScopeReport` pins every corpus definition's locals and live
ranges. L2 (2026-10-12): per-local `(first-use, last-use)` facts
(region-aware SSA matching, load-copy chains only); proved
first-use ≤ last-use within the function extent. Its follow-up
admission predicate (`hasSequentialWriterRanges` → deferred
"sequential writers" recognition in `validate`, nothing
admitted) is the F1/N11 license input. L3 (2026-10-12): slot
content-roots (`ultimateRoot` address-identity claims, both ends
`Ref`, fuel-stable); `alias_reborrow` shares one address (F1
sequencing license in waiting), `alias_cond` names different
addresses (caller-dependent footprints confirmed textually).
Known limits (sound direction, all admit less): first-init wins,
value inits and copy ambiguity report `Unknown`.

### F2. Native conditional framing — DONE (2026-10-12, report-only)

The MoSeL question answered with evidence: `Circe/CondFrame.lean`
proves the `alias_cond` disjunctive post natively over `Mem`
(per-arm frame via `memFind_memStore_other` on the F0 addresses;
both disjoint and aliased splits proved). Burden is small (two
helpers + two posts), so MoSeL vendoring stays DEFERRED —
revisit on a second conditional shape or a `Mem`-level write
need. Full admission was blocked on two model gaps: triple
outputs (B1) and scalar `Mem` writes (B2); the S1–S3/G2–G3
slices lifted both (generalized struct construction +
`mstore`/`mload` + verdict-independent gate + open contract).

### S0–S4 + G1 dispositions — DONE (2026-10-12..14)

Report/model-only spikes with no admission churn: S0 (verdict GO
on a `Mem`-space open contract for the cond body — artifact
decision: open contract, not OpenFunc); G1 (model-only `CExpr.pair`
carrier, fixed 2×i32); S1 (`mstore` + `mload`, pure-side
`AssertFail` by design); S2 (opt-in `pinnedCell` pinning,
disjoint-pair entry); S3 (verdict-independent gate arm + 4-leg
transfer + `_spec` render); S4 (byte-identical goldens, gate +
golden + tamper-checked diff suites + docs). The functionalized
pipeline (scalar mutation as value-in/value-out + gate-side
L2/F0 licenses, F1-style) sidesteps Iris-style framing for
scalars entirely.

### L4. Second sequential-writer admission (L1b) — DONE (2026-10-16)

First L-track consumer: `alias_reborrow34` (`r += 3` then `s += 4`
through two loans to one address) is admitted through the
previously deferred sequential-writer branch. The L1a spike
verified all three licenses on the new corpus (structural
skeleton, L2-disjoint ranges, F0 same address) while the F1
const-use pins exclude it. Mechanical mirror of F1 with `1/2`
replaced by `3/4`: new `Circe/Emit/Reborrow34.lean`
(`reborrow34Func`/`reborrow34Fwd`/bridges), `reborrow34ConstUse`
+ `isReborrow34Shape` (mutually exclusive with `isReborrowShape`),
`FragKind.reborrow34`, `emitReborrow34Text/SpecText` with
ground-truth edges, `bindMemArgs`/`oracleNoalias`/`memTransfer`
mirrors, `GoldenReborrow34` (pipeline + wrong-const/wrapping/bare
rejects + cross-exactness both ways + admission row),
`DiffReborrow34` (7 edges + 1000 fuzz trials vs the corpus-linked
native driver), tamper-checked.
- Acceptance: 720 jobs TEST-OK, CHECK-OK.

### L5. Region/framing consumer spikes — DONE (2026-10-16, verdict-only, no wiring)

L2 (regions): proven vestigial-by-design, deliberately left
unwired. CIR carries no region-distinguishing marks
(`choose_ptr.cir`: both pointer params `llvm.noalias`, nothing
else); the documented model is single-region (`SUBSET.md`:
`mutBorrow(region)` unique-for-region, nested/multiple regions
rejected); the only reader (the `choose` `r1 == r2` arm in
`Match.lean`) is vacuous-by-construction (`mutBorrow 0` at both
construction sites, arm holds by `rfl`). Deriving distinct
regions would contradict admission (any two-borrow entry becomes
multi-region, hence rejected), so no slice is owed: distinct
regions buy no new admission and change no verdict.
L3 (framing): no consumer exists — `semSliceCond`/B2 were never
built — and the framing L3 was meant to enable is already
delivered natively (F2 `condPost_disjoint`/`condPost_aliased`
proved over `Mem`; S3 three-leg open-contract transfer; N14/G3
full-framing admission, verdicts PROVEN). L3 roots stay
extract-only evidence.
Iris revisit trigger FIRED: the 2026-10-12 trigger (framing
admission + lifetime evidence) now holds on both legs — N14
admitted `alias_cond`-class framing, L1/L3 supply first/last-use
facts and caller-dependent footprints. The revisit-or-defer
decision on MoSeL vendoring is now due (F2's second-shape line
also stands).
- Acceptance: report-only spike, no `validate`/Emit/transfer churn.

### O1/O2. `optional::value` throw-path slice — DONE (2026-10-16)

The Pillar 1 deferred probe (`optional::value` lowers to `cir.trap`)
is closed. The O0 spike showed the "throw path" has no EH ops at all
under `-fno-exceptions`: the `value()` callee is an engaged-check
`cir.if` (taken arm = the admitted `operator*` path) with a
`noreturn __throw_bad_optional_access` call (`abort()`) + `cir.trap`
fallthrough. Gate: `isOptValueExemptText` (noreturn-throw +
engaged-`if` + 3 calls + single return + no-EH pins) exempts the
callee text; `isOptValueOpShape` / `isOptThrowShape` /
`isOptValueShape` admit the leaf, the unconditional-abort helper
(`.fail`, `void`), and the guarded entry; `isOptValueUnguardedShape`
rejects unguarded `.value()` with a dedicated no-guard message
(O1). Model keeps the internal check explicit (`.if_` + `.fail` =
`AssertFail`, the standard loud arm) — no live check erased.
Proofs: `evalFuncFuel_optValueOp` / `evalFuncFuel_optThrow` /
`evalProgFunc_optValue` + full transfer mirrors
(`memEval*`/`memTransfer*`/`oracleNoalias_*`/`optValue*_correct`).
Harness: `tests/golden/OptValue{,Op,Throw}.lean` (+`_Spec`),
`GoldenOptional` (corpus pipeline with per-function validation +
6 new rejects: unguarded, trap-without-check, missing-`noreturn`,
live-`unreachable`, two-call throw helper), `DiffOptional`
(checked-leaf + helper Lean-Lean agreement, guarded entry vs native
with exceptions enabled — engaged exercises the real `.value()`),
tamper-checked (sentinel `-1`→`-2` caught as
`opt_value mismatch: lean=-1 native=-2`), CIR byte-reproducible via
`tools/emit-cir.sh`.
- Acceptance: 735 jobs TEST-OK, CHECK-OK.

### R. In-place `vector::reverse` slice — DONE (2026-10-16)

Pillar 2's first store-inside-loop shape: the countdown
two-pointer `vec_reverse` (single `mutBorrow` vector, `void` out).
The naive `n / 2` loop needs unsigned `div` (out per N6a — the R0
rejected corpus), so the loop counts `j` down from `size` while
`i` counts up under one `ult` guard. Gate: `isVecReverseShape`
(structural counts — 1 `size` + 4 mut-`at()` calls, 1 `while`,
1 `lt`, 1 `condition`, 2 consts, 1 `inc`/`dec`, 4 allocas / 16
loads / 8 stores — plus the SSA-dataflow swap/index pins
`vecReverseSwapPin`/`vecReverseIndexPin`, first `callArgOps`
consumer) admits the entry over the frozen `size`/checked-`at()`
leaves (composer precedent, V2 checked-only discipline).
Proofs: `RevInv` (`i + j = n` + mirrored outers + untouched
middle), `RevInv_step` (the `i = j - 1` touching-window case),
`RevInv_exit`, `evalProgFunc_vecReverse` (fuel induction against
`revIters`, `F = n + 1` suffices) + full transfer mirrors
(`memEvalStmtFuel_vecSet` — the first `vecSet`-iteration memory
threading, shadowing snapshot blocks by-find —
`memEval*`/`memTransfer*`/`oracleNoalias_vecReverse`/
`vecReverse_correct`).
Harness: `tests/golden/VecReverse.lean` (+`_Spec`),
`GoldenVecReverse` (corpus pipeline with per-function validation:
entry + 4 shared leaves byte-identical, 6 shape cross-checks, 2
rejects — self-recursive out-of-subset, bare-ptr alias-reject),
`DiffVecReverse` (eval/fwd composition + native agreement),
tamper-checked (swap-neutralized `v.at(i) = v.at(i)` caught as
`vec_reverse mismatch: lean=[2, 1] native=[1, 1]`; golden edit
caught), CIR byte-reproducible via `tools/emit-cir.sh`.
- Acceptance: 743 jobs TEST-OK, CHECK-OK.

### S. In-place `vector` segment-reverse slice — DONE (2026-10-17)

Pillar 2's window sibling of R: the countdown two-pointer
`vec_seg_reverse` (single `mutBorrow` vector + two owned `u64`
bounds, `void` out). No `size` call — the prelude binds `i ← lo`,
`j ← hi` as pure `let`s — and the R loop body is reused verbatim
(same `--j`, same two checked reads, same crossed `vecSet`
writes, `++i`). Gate: `isVecSegReverseShape` (structural counts —
4 mut-`at()` calls, no `size` call, 6 allocas / 17 loads / 10
stores, no consts — plus the SSA-dataflow swap/index pins, swap
pin shared with R via `vecReverseBody` line-identity) admits the
entry over the frozen checked-`at()` leaves.
Proofs: `SegInv` (`i + j = lo + hi` + mirrored outer window +
untouched middle and outsides), `SegInv_step` (the `i = j - 1`
touching-window case carries over; writes land inside `[lo, hi)`
so the outside legs thread through), `segGetElem` (window
indexing through `take`/`drop`/`reverse`), `SegInv_exit`,
`evalProgFunc_vecSegReverse` (fuel induction against `revIters`,
`F = n + 1` suffices; caller debt `lo ≤ hi ≤ length` selects the
forward's loud-guard leg) + full transfer mirrors
(`segMemBody_hit`/`segMemWhile_ok` with the `(1 + n)`-word
snapshot by-find, `segMemEvalProgFunc`/`segMemTransferProg`/
`oracleNoalias_vecSegReverse`/`vecSegReverse_correct`).
Harness: `tests/golden/VecSegReverse.lean` (+`_Spec`),
`GoldenVecSegReverse` (corpus pipeline with per-function
validation: entry + 4 shared leaves byte-identical, 6 shape
cross-checks, 2 rejects — self-recursive out-of-subset, bare-ptr
alias-reject), `DiffVecSegReverse` (eval/fwd composition +
native agreement over directed windows + fuzzed `(lo, hi)`),
tamper-checked (swap-neutralized `v.at(i) = v.at(i)` caught as
`vec_seg_reverse mismatch: lean=[3, 2, 1] native=[1, 2, 1]`;
golden edit caught), CIR byte-reproducible via
`tools/emit-cir.sh`.
- Acceptance: 751 jobs TEST-OK, CHECK-OK.

### T. In-place `vector` rotate-by-three-reversals slice — DONE (2026-10-18)

Pillar 2's loopless composer over S: `vec_rotate` (single
`mutBorrow` vector + one owned `u64` shift `k`, `void` out,
left rotation). The entry has no loop — one `size` call plus
three `vec_seg_reverse` calls with `(v, 0, k)`, `(v, k, n)`,
`(v, 0, n)` wiring (the C++ initially composed rotate-right;
the native driver caught `4 1 2 3` vs `2 3 4 1` and the
corpus, pin, composer, and match arms were recaptured to
left rotation). Gate: `isVecRotateShape` (structural counts —
1 `size` call + 3 seg calls, 3 allocas / 8 loads / 3 stores /
4 consts — plus the SSA-dataflow three-window pin off the
`v`/`k`/`n` allocas, the `u64`-zero consts, and a unique
`align(8)` store) admits the entry over the frozen `size` /
admitted-seg leaves.
Proofs: `segReverseWindow_length` (window lengths through
`take`/`drop`/`reverse`), `segWindow_rotate3` (the pure
rotation identity over the reused S forwards — no arithmetic
needed), `evalProgFunc_vecRotate` (three `callProg` steps via
the prog-parametric `evalProgFunc_vecSegReverse`, summed fuel
`(revIters 0 k + 1) + (revIters k n + 1) +
(revIters 0 n + 1) + 1`; caller debt `k ≤ n` selects the
forward's loud-guard leg) + full transfer mirrors
(`rotMemEvalProgFunc`/`rotMemTransferProg`/
`oracleNoalias_vecRotate`/`vecRotate_correct`).
Harness: `tests/golden/VecRotate.lean` (+`_Spec`),
`GoldenVecRotate` (corpus pipeline with per-function
validation: entry + size leaf byte-identical, 6 shape
cross-checks, 3 rejects — permuted three-call order
out-of-subset, bare-ptr alias-reject), `DiffVecRotate`
(eval/fwd composition + native agreement over directed `k` +
fuzzed `k ≤ n`), tamper-checked (native tamper and golden
edit caught), CIR byte-reproducible via `tools/emit-cir.sh`.
- Acceptance: 759 jobs TEST-OK, CHECK-OK.

### P3a. Program-level while rule + R rule-application — DONE (2026-10-19)

Pillar 3's frontier rule: `HTripleProg`/`HTripleProgAt`
promoted from the gallery to `Circe/Hoare/Def.lean`, and
`htripleProg_while_at` proved in `Circe/Hoare/Rules.lean` —
the `htriple_while_at` mirror over `memEvalProgStmt` (same
four premises; the existing `memEvalProgStmt_while_false/true`
equations make the proof a line-for-line port). The R
countdown is re-proved as a rule application
(`hoare_reverseWhileProg` with the fuel-indexed wrapper
`revInvK`, i.e. `revIters i j = k ∧ RevInv …` plus bindings,
snapshot, and layout): `hzero`/`hexit` via the new
`memEvalExpr_ult_ij` guard evaluator + `RevInv_exit`,
`hdec` by boolean case, `hstep` via the `hoare_reverseSwap`
step triple + `RevInv_step`/`revIters_step`/
`revU64_succ/pred_toNat`. Gallery grows to 10 closed-instance
jobs (whole-loop `[1,2,3] → [3,2,1]` executable instance).
Proof notes: `by_contra`/`push_neg` are unavailable in this
profile (use `by_cases`); named-`def` invariants need
`abbrev` (reducible) for `obtain` to see through them;
post-`subst` code must use the surviving names (subst
eliminates one side — check the context, don't assume which).

### P3b. S/T galleries + second-use prose notes — DONE (2026-10-19)

Gallery-per-shape kept current: `hoare_segSwap` (S swap-step
triple over `segMemBody_hit`, premise-for-premise port of
`hoare_reverseSwap` — only invariant, length-word snapshot,
and `hfind` differ; required renaming the window bound to
`hiW` since `obtain`'s `hi` lookup hypothesis shadows it) +
executable S window (`[1,2,3,4,5]` `[1,4)` → `[1,4,3,2,5]`)
and T rotate (`[1,2,3,4]` by 1 → `[2,3,4,1]`) instances via
`memEvalProgFunc`. T documents the while-rule boundary in
prose: the loopless entry needs program-level `seq`/`callRet`
composition rules (named future work, frame-rule
prerequisite). `hoare_reverseSwap`'s post records the layout
fact (was proof-internal). S-delta second-use notes in
`docs/ROADMAP.md` (still prose stage — third admitted loop
earns the Lean tactics). Gallery at 12 closed-instance jobs.

### Frontend MVP (`circe-emit` + `examples/hello/`) — DONE (2026-10-19)

First user loop: `tools/EmitCli.lean` (`lake exe circe-emit --
--in F.cir --out F.lean [--func m] [--fact n=v]...`) validates
via `validateModule` (explicit facts win; every other defined
function defaults to `.unknown`, the N4a precedent) and writes
`emitFunc` output — byte-identical to goldens on `vec_rotate`
(reject paths loud: multi-def without `--func`, `out-of-subset`
with the gate's code). `examples/hello/` is a workspace `Hello`
lib (own directory, imports only `Circe.*` — the external-user
shape without nested package builds): `hello.cpp` (checked
`add`), committed `Hello/Emitted.lean`, handwritten
`Hello/Spec.lean` (`hello_add_small` via `checkedAddI32_ok`,
`hello_add_comm` via `checkedAddI32_comm`,
`hello_spec_check`), `Hello.lean` root. Driver
`frontend-hello` job: nested `lake build circe-emit Hello`
(proof check), CLI re-emit to scratch, byte-compare with the
committed file, `#eval hello_spec_check = true` (tamper
verified: edited emission fails the job). README "For users"
with every command run verbatim. Deliberate deviation from the
proposal: workspace member instead of standalone package (keeps
the gate hermetic); copy-out template on user request.

### U1 user tactics — DONE (2026-10-19)

Tactic pack productized, no new tactics (rule of three holds —
nothing has a third use): T1 audited all five tactics on
user-shaped goals (`cir_simp` comm-goal, closed-goal,
`cir_fuel` side-goal, `cir_choose` get-put, `cir_step`
evaluator step, `cir_eval_closed` executable check).
Deliberate negative result: NO `cir_simp` set additions — the
one evidenced candidate (`checkedAddI32_comm`) was reverted
after the simp rewrite trace showed the set's own unfolding
shadows it and `simp` rejects the permutation anyway; algebraic
facts stay explicit (`exact checkedAddI32_comm`). T3 demos live
in `examples/hello/Hello/TacticsDemo.lean` (built by `lake
build Hello`, so the demo is the regression test — six
theorems: `hello_add_comm_simp`, `hello_add_ok_set`,
`hello_check_true`, `hello_fuel_side`, `hello_choose_get_put`,
`hello_step_uadd`). Audit findings documented as standing
limits in `docs/VERIFYING.md` ("For users": unfold your own
forward first; no commutation lemmas by design; `cir_choose`
needs a variable selector; `cir_step` needs every lookup
fact). Process note: `/tmp` probes are not verification —
several early "passes" were a `^error` grep that never matches
Lean's `file:line:col: error:` format; only `lake build` of the
consuming lib counts.

### U2 modular-proof harness — DONE (2026-10-19)

Contract template + three operators in VERIFYING.md
("Contracts and composition"): per-function contracts are an ok
leg plus an err leg over the emitted forward, proved from
callee contracts as hypotheses; sequential threading (callee
equations rewrite into the unfolded composer),
delegation (rewrite + callee spec), conjunction (independent
legs conjoined). No new proof obligations were invented — the
harness names the in-repo idiom: ten existing specs annotated
as template instances (`add3`/`addCaller` ok+err, `sumCaller`,
`translate_correct`, `stdVecGrowRealloc_correct_ok`,
`stdVecReserve_correct_realloc`,
`stdVecEmplaceBack_correct_slow/fast`). Deliberate deviation
from the proposal: no new multi-callee demo theorem — the
planned rotate-forward contract trio is vacuous (the forward is
stated directly via `drop`/`take`, so no callee subterm exists
for assumes to rewrite; its composition proof lives one level
down as `evalProgFunc_vecRotate`), and the only callee-stated
3-call composer (`mergeRunsFwd`) has no callee specs (new
verification, U3 material). The fan-out boundary is documented
instead: direct-stated composers compose at eval level;
callee-stated composers use one equation per call site.

### U3 reusable lemma packs — DONE (2026-10-19, P0 audit + P1 extraction; P2 negative, P3 closed)

P0 audit of repeated proof shapes across the slices, with use
counts and what varies per use (moved here from ROADMAP so the
roadmap keeps only the open triggers):

| # | Shape | Uses (observed) | Varies per use | Verdict |
|---|-------|-----------------|----------------|---------|
| 1 | Checked-index closes: `List.getElem` bounds, `List.length_set` chains, `length_reverse` bridges before `omega` | 34 `getElem` + 16 `length_set` cites across `Transfer/`, `Emit/VecReverse`, `Emit/VecSegReverse`, `Specs` | list expression, index, bridging length equation | P1 DONE: `Circe/Lemmas/CheckedIx.lean` (`doubleSet_read` + `doubleSet_length`); R and S `hset` proofs replaced by one application each |
| 2 | Countdown two-pointer invariant + step + fuel-indexed induction | `RevInv`/`SegInv` in `Emit` (R, S) | mirror function, leg shapes (R has no outers) | P2 NEGATIVE: P1 took the only verbatim-shared part; remainder is per-invariant mirror arithmetic + proof-script skeletons (tactic vehicle, needs three user-goal uses), not lemma material. Only two forward-level uses (gallery demos are Hoare-level, different machinery). Forcing R into segment form would churn R2/R3 + transfer + specs for zero statement gain |
| 3 | Checked-arithmetic ok/err legs, one equation per call site | 16 theorems in `Specs` + `_oob`/`_none` mirrors in `Transfer/Slice` | arity (2–4 adds), error destination | PROSE ONLY: two arities worked; extract on third |
| 4 | Transfer ok/err leg pairs: `memEvalFuncFuel_X` + `memTransfer_X` | dozens of pairs in `Transfer/Slice`, `Transfer/Flow`, `Transfer/Acc` | leaf shape, error outcome | PROSE ONLY: each pair is 2–4 lines; the vehicle would be a tactic, which needs three user-goal uses first (U1 rule) |
| 5 | Fuel arithmetic: step + `… + 1 ≤ F` countdown, summed across composed loops | R, S (reuse), rotate (sum of three) | loop count, per-loop measure | PROSE ONLY: two distinct uses; extract on third loop shape |
| 6 | `bindMemArgs`/`oracleNoalias` discharge | 116 cites in `Transfer/Slice` alone | argument roles, value shapes | ALREADY FACTORED: `Derived` lemmas discharge it; no pack needed |
| 7 | Per-function eval/transfer pairs (`evalProgFunc_X` + `memTransferProg_X`) | 30+ eval, 15 transfer | function under verification | NOT A PACK: this is the U2 contract level itself — per-function by definition |

P1 interface documented in VERIFYING.md ("Lemma packs",
incl. the P2 negative). 428 jobs TEST-OK + CHECK-OK at the
P1 gate; byte-identical goldens confirm the refactor changed
no statement.

### T1 fold-end tactic — DONE (2026-10-19)

`cir_fold_end (dropEq, hget)` in `Circe.LeafTactics`
(re-exported via `Circe.Tactics`): the `conv => lhs;
rw [<fold>_drop]` + `simp [hget]` suffix-fold end script,
shared verbatim by six sites (`spanFold_*`, `viewFold_*`,
`stdVecFold_*` step/nil pairs) — all converted. An `elab` in
two `evalTactic` steps re-parsing surface strings at the use
site (`rw`/`simp` arg kinds reject spliced idents — `cir_step`
precedent; a one-quotation `macro` would risk `simp` binding
inside the `conv` block). `hello_fold_end` Hello demo as the
regression test; VERIFYING.md For-users entry + standing
limit (the drop equation is per-fold by definition).
Explicit non-tactics from the same audit: `dite_eq_left/right`
closers are already one-line `simp only` calls (a tactic would
be pure indirection); the unfold-loop-`show` script stays prose
with two uses (third admitted loop shape earns it). 428 jobs
TEST-OK + CHECK-OK.

### H1 cell-kit promotion — DONE (2026-10-21)

`cellAt`/`cellsAt`, the store/read-back lemmas
(`memStore_cell`, `memFind_cell_store`, `memStore_cellsAt`,
`memFind_cellsAt_store`, `memLoad_cellsAt`, `cellAt_cellsAt`),
and the array-prefix trio (`take_map_drop_getElem`,
`drop_set_zero_cons`, `take_map_drop_set_succ`) moved from the
report-only `Circe/CondFrame.lean` spike to
`Circe/Mem/Agree.lean`, beside `memFind_memStore_other` — they
were defined in a no-suite-row file while admitted proofs
stood on them (`htriple_mstore_frame`, gallery
`sumLoop`/`incrLoop`). No import churn: `CondFrame` already
imports `Circe.Mem`, and `Rules`/gallery resolve the kit
transitively (verified by build, not by reasoning).
`CondFrame` keeps only its report-only `condExec` program.
Audit remainder (no code): the R/S store lockstep has exactly
two uses (prose stage); triple-level store rules have no
customer (loop bodies with stores contain calls, so they live
at prog level where frame is definitional per F3).

### P3c. Program-level seq rule (F1) — DONE (2026-10-21)

`memEvalProgStmt_seq` (no fuel split — the `seq` arm threads
state directly) + `htripleProg_seq` / fixed-fuel
`htripleProg_seq_at` (F1's rule refactored over the `At`
version), `fellThrough`-pinned like `htriple_seq` with the
same early-return deferral. `hoare_rotateSpine_seq` composes
the rotate prefix from five leaf triples (call leaves as
hypotheses).

### P3d. Program-level call rule + closed spine (F2) — DONE (2026-10-21)

`htripleProg_callProg_at`: caller triple from the callee run
at one less fuel (`At (F+1)` — the zero-fuel arm errors). The
U2 contract + transfer plug in as the run equation, never
re-verified. `hoare_rotateSpine_closed`: the closed rotate
prefix — all five leaves discharged (size/`z` wrap transfer
equations; each seg call composes `segMemEvalProgFunc` with
`vecSegReverse_correct`), four `seq_at` compositions at fuel
`G+1`. Deliberate scope: no gallery instance (general over
`l`/`k`, so a closed instance re-proves nothing); trailing
`return_` stays out (deferred seq-return equation).

### P3e. Program-level call frame rules (F3) — DONE (2026-10-21)

`htripleProg_callProg_frame_at` /
`htripleProg_callRet_frame_at`: a caller-memory frame rides
the call untouched. Definitional, not deep: the callee binds
into `emptyMem` (caller memory unreachable) and both call
equations keep `(m, π)`. `hoare_segCall1_framed` exercises the
rule. A fully framed spine waits for an actual multi-cell
caller; the real frame work is statement-level (H-track).

### P2-M1. Merge-drain specs — DONE (2026-10-22)

The missing `mergeRuns` callee contracts, named as U3 material,
closed as pure verification debt (no admission, no corpus/diff
changes). M1a: 14 U2 contracts in `Specs.lean` — ok plus
per-site err legs for main/both drains by fuel induction, with
the threading trio for the entry (`46a97b1`). M1b: mem-level
entry transfer — bind lemma, body mirrors, loop inductions, and
the general-caller-memory entry; new
`Circe/Transfer/VecMergeRuns.lean` (3079 lines) plus a
`Derived` helper (`c0e96c7`). M1c: the closed sort-segment
spine — sharing-frame call kit, seg/outer mirrors with pin
threading, whole-function entry, with small kit extensions in
`CoreIR`/`Derived`/`Eval`/`Mem` (`8f1efdc`).
- Acceptance: `lake build` green at each commit; no admission,
no corpus/diff changes (pure verification debt).

### P2-M2. Out-of-place checked transform — DONE (2026-10-22)

The `vec_transform_add` kernel (read-only input, checked-op
written output): first multi-block framed proof (`cellsAt` +
framed `cellsAt`, an H-kit customer) and the accumulate-adjacent
shape G2 unblocked. One admission pin
(`isVecTransformAddShape`). U2 contracts plus value and mem
transfer (`Circe/Transfer/VecTransformAdd.lean`); goldens
(`VecTransformAdd` + `_Spec`), `DiffVecTransformAdd` with
tamper-checked fuzz, `cir --verify-each`, byte-identical
emission.
- Acceptance: 433 jobs TEST-OK, CHECK-OK (`d555844`).

### P2-M3. In-place Lomuto partition — DONE (2026-10-22)

In-place partition (forward scan with stores): a new loop shape
beyond countdown/rotate, and the third data point for the
fuel-arithmetic (audit #5) and loop-tactic triggers. One
admission pin (`isVecPartitionShape`). U2 contracts plus value
and mem transfer; goldens (`VecPartition` + `_Spec`),
`DiffVecPartition` with tamper-checked fuzz.
- Acceptance: 438 jobs TEST-OK, CHECK-OK (`5c941c7`).

### P2-M4. Iterative selection sort — DONE (2026-10-22)

`vec_selection_sort` (`min_index` leaf + outer scan-and-swap
entry, calls in the loop body via the M1c kit): the second
vector sort (quicksort stays out — the gate rejects recursion)
and the fourth loop-shape data point. One admission pin
(`isVecSelectionSortShape` + `isVecMinIndexShape`). U2
contracts plus value and mem transfer (leaf at fuel level,
outer at program level with split fuels); goldens
(`VecMinIndex`/`VecSelectionSort` + `_Spec`),
`DiffVecSelectionSort` with tamper-checked fuzz.
- Acceptance: 445 jobs TEST-OK, CHECK-OK (`49c6d02`).

### P3-T2. Rule-of-three tactic harvest — DONE (2026-10-22)

Three reparse-based `elab` tactics in `Circe/LeafTactics.lean`
(reparse, not splice, so introduced names stay use-site
accessible): `cir_fuel_step` (the N5a `have hF'` +
`fuel_step_down` split, 10 sites), `cir_unfold_prog` (the
`have hwhile` step, value/mem family auto-detected from the
goal head, 63 sites), `cir_unfold_leaf` (the fuel-level
handler-set simp, 69 sites). Five old files gained a one-line
`import Circe.LeafTactics` (Span precedent). Two intentional
exclusions: the mem fuel-level rule stays prose (only 2 sites —
no third consumer yet) and the `GrowErase` term-mode use. Found
by the work: `rw at ⊢` wraps goals in `mdata`, which
`getAppFn` cannot see through (fixed with `consumeMData`).
- Acceptance: 445 jobs TEST-OK, CHECK-OK (`a7a88d2`).

### P2-M5. Selection-sort sort contract — DONE (2026-10-23)

N9-tier sortedness/permutation for selection sort, proved on
the fwd model and closed at eval. Pure `selectionSortList`
with `selectionSortList_sorted` (ascending under the kernel's
`slt`) and `selectionSortList_perm` (joint induction —
sortedness needs the tail permutation for membership
transport). `minIndexFwd_lower` (scan minimality, mirroring
`minIndexFwd_ok`), `swap_perm` (positional middle-swap over
take/drop splits), and the outer sorted-prefix bridge
`selectionSortFwd_sorted_perm` (positional invariant
discharged by `getElem?_set_ne` / `getElem?_set_self` +
`omega`), closed by `evalProgFunc_vecSelectionSort_spec`.
Proof-only, no admission. Queued follow-ups: the partition
permutation/partition-property contract and the merge-sort
sortedness/permutation contract.
- Acceptance: 445 jobs TEST-OK, CHECK-OK (`2150d07`).

### P2-M6. Partition contract — DONE (2026-10-23)

`partitionTake_perm` (take-step permutation via `swap_perm` +
`List.set_comm`), `PartitionedAt` (`[0,s)`-true / `[s,i)`-false
invariant), `partitionFwd_perm` + closing
`evalProgFunc_vecPartition_spec`. Proof-only, no admission.
- Acceptance: 445 jobs TEST-OK, CHECK-OK (`70b93e5`).

### P2-M7. Merge-sort contract — DONE (2026-10-23)

Sortedness + permutation over the M1c spine, same shape as
P2-M5. M7a: `mergeRunsMainFwd_sorted` joint sorted+perm
induction with cross-window conditions (strengthened with
bounds + length), drain-I/J sorted+perm, `mergeRunsFwd_sorted_perm`
assembly (plus `mergeRunsMain_mono/ge`, drain mono/ge
confinement). M7b: `sortCopyFwd_joint`, `sortSegFwd_joint`
(`MergeSegInv`, `BlockedSorted`), `sortOuterFwd_joint`
(equation + lengths + readability + perm + full sortedness),
with `perm_window_splice` / `SortedSeg_congr` /
`take_split_mid` helpers. M7c:
`memEvalProgFunc_vecMergeSort_spec` (memory evaluator returns
a sorted permutation; value-level `evalProgFunc` is out of
reach since the program threads memory). Proof-only, no
admission.
- Acceptance: 445 jobs TEST-OK, CHECK-OK (`84cbc70`,
  `c02cce9`, `f089c83`, `f7fdab5`, `d31b87f`, `a593cbd`,
  `ef179a2`).

### P2-M8. Recursive quicksort contract — DONE (2026-10-24)

First admitted recursion: `vec_quicksort` (Lomuto + 2 self-calls)
with the joint sorted+perm contract reusing the M6 partition bridge
and M7 sorted/perm vocabulary. Admission: corpus
`vec_quicksort.cpp` + real CIRGen `.cir` (9 mut `at()` + 2
`callProg` self-calls; `callRet` self-call and mutual recursion stay
rejected), recursive-caller shape + gate arm, `vecQuicksortFwd`
model, goldens + 1008/1008 diff fuzz. Proof-A:
`evalProgFunc` ok/err twins vs the forward model. Proof-B:
`qsPartFwd_joint` (scan split) and `vecQuicksortFwd_joint` (length,
confinement, perm, full sorted window via `sort_combine` + window
permutations). Proof-C: `vecQuicksort_spec` closing spec at value
level (no Transfer file — unlike M7, the program does not thread
memory). Driver fixes the admission missed: spec-stub count 136→137,
roster entries for `DiffVecQuicksort`/`GoldenVecQuicksort`.
- Acceptance: 452 jobs TEST-OK, CHECK-OK (`b79752a`,
  `f9b4e76`).

### P4 Phase 0. Iris vendoring re-check — DONE (2026-10-23, report-only)

All three 2026-10-12 blockers re-checked in `/tmp` scratch (no
repo churn, no vendored dependency yet): iris-lean now ships a
`v4.34.0` release tag matching our toolchain exactly; the tag
pins `Qq`/`Batteries` at the same commits as our manifest
(zero diamond-conflict risk, zero `Qq` drift surface); full
Iris core builds under `v4.34.0`; a MoSeL hello (`iintro`,
`ihave`, `icases`, `isplitl`/`isplitr`, `iframe`,
`iassumption`, `iexact`) typechecks. Stale-idiom note:
upstream `Examples/` still uses `open Iris.BI`, which no
longer resolves — the working idiom is `open Iris BI` per
`IrisTest`. Verdict: GO.
- Acceptance: report-only spike, no `validate`/Emit/transfer churn.

### P4 Phase 1. MVP: `Mem` points-to + reusable frame rule — DONE (2026-10-23)

Vendored iris-lean at the `v4.34.0` tag (MoSeL interface
scope only — no program logic, no oracle/`Mem` changes;
`lakefile.toml` + manifest, `Qq`/`Batteries` untouched). New
`Circe/Iris/`: `PointsTo.lean` reifies `Mem` into the
classical separation-logic state (`stateOf`, `cellAtI`/
`cellsAtI` points-to, bridges back to `cellAt`/`cellsAt`,
`sep_unfold`), proves `frame_memStore` once from
`memFind_memStore_other` (a successful index-0 cell store
updates its points-to and preserves an *arbitrary* frame),
and recovers native facts via adequacy (`split_cellAt`,
`star_cellAt`, `star_frame_cellAt` — the side swap rides
union/disjoint commutativity). `CondDemo.lean` proves both
`alias_cond` legs through the frame rule
(`condPost_disjoint_star`: two applications + `star_intro`,
the other cell riding the frame both times) and recovers the
EXACT native `condPost_disjoint` conclusions
(`condPost_disjoint_parity`); the aliased leg closes through
the bridge alone (one cell — the case a star would
conflate). Stretch `double_store_frame` reuses the rule
twice (the take-branch two-store pattern, second application
framing over the first result). Two MoSeL tactic demos over
`HeapProp Block` (`isplitl` commutativity, `ihave`/`iapply`
frame congruence — no hypotheses dropped, so no affinity
instance needed). Scope notes: index-0 single-cell stores
only; rule application across concrete states is a meta-step
with tactics driving the entailment plumbing. Iris syntax
lessons recorded in-file: the `∗`/`↔` tokens elaborate only
inside `iprop(...)`, the global `∃` macro means BI-exists
(use `Exists` for meta-level existence).
- Acceptance: sorry-free and warning-free, `lake build`
green, gate stays 445 jobs TEST-OK, CHECK-OK (`44a86c0`);
no driver jobs added, no `validate`/Emit/transfer churn.
