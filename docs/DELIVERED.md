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
