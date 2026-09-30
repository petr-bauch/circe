/-
Circe.Validator — the verified gate `validate : RawIR → Option Func`.

Rejects aliasing/out-of-subset inputs loudly with actionable codes
(`alias-reject`, `escape-reject`, `oob-possible`, `out-of-subset`).
Enforces docs/SUBSET.md rules and the
oracle `noalias` requirement, mapping the admitted corpus shapes to
their canonical `Func`s (the only `Func`s `Emit` handles). Anything else
is rejected with a precise code + message (golden-tested in
`tests/lean/GoldenPhase4.lean`, `GoldenPhase6.lean`, `GoldenPhase7.lean`,
`GoldenCalls.lean`).

Check order (first hit wins — rejection codes are priority-ordered):
1. oracle wiring (fact must name this function);
2. forbidden constructs (EH, int↔ptr casts, `void*`, volatile/atomics,
   float, `setjmp`/`longjmp`, globals,
   function pointers, VLAs, variadics, `goto` (`cir.br`),
   bitfields, signed wrapping arithmetic without `nsw` — all `outOfSubset`;
   `switch` is shape-aware (the admitted `cls` lowering passes, all other
   `switch` uses are `outOfSubset`);
   heap (`malloc`/`free`/`realloc`) and calls are shape-aware (see step 5):
   the admitted `vec_alloc` / `vec_copy_sum` / `vec_alloc_u64` /
   `vec_realloc` (M1c) shapes pass,
    all other heap/call uses are
   `outOfSubset` with dedicated messages (missing-`free`, double-`free`,
   `realloc`-shape, heap-shape, calls);
3. pointer discipline (`aliasReject`: raw pointer without `__restrict__`,
   or oracle verdict other than `noalias` with live pointer params);
5. shape admission (canonical `Func` or a precise code: `escapeReject`
   for non-`choose` pointer returns, `oobPossible` for unbounded
   `ptr_stride`, `outOfSubset` otherwise, including misshapen struct
   uses outside the S2 `translate` shape).
-/
import Circe.CoreIR
import Circe.Parser
import Circe.Oracle
import Circe.Emit

/-- Machine-readable rejection codes (see docs/SUBSET.md). -/
inductive RejectCode : Type
  | aliasReject
  | escapeReject
  | oobPossible
  | outOfSubset
  deriving DecidableEq, Repr

/-- A rejection: which function, which code, and a human message. -/
structure Rejection : Type where
  func : String
  code : RejectCode
  message : String
  deriving DecidableEq, Repr

/-- Validation result: either a `Func` ready for `Emit`, or a rejection. -/
abbrev Validation := Except Rejection Func

/-- Shorthand for rejecting. -/
def reject (func : String) (code : RejectCode) (message : String) :
    Validation :=
  .error { func, code, message }

/-! ## Shape predicates over extracted features -/

/-- The text calls function `fname` (`cir.call @fname(` with paren, so a
    callee merely named `@add_vec` does not match `@add`). -/
def callsFunc (text fname : String) : Bool :=
  containsSubstr text ("cir.call @" ++ fname ++ "(")

/-- A line performing a non-heap call (`malloc`/`free` plumbing excluded —
    those are gated by the vec shape instead). -/
def lineHasNonHeapCall (line : String) : Bool :=
  containsSubstr line "cir.call @" &&
  !containsSubstr line "cir.call @malloc(" &&
  !containsSubstr line "cir.call @free("

/-- Whole-text wrapper (cf. `hasWrappingSignedArith`). -/
def hasNonHeapCall (text : String) : Bool :=
  (text.splitOn "\n").any lineHasNonHeapCall

/-- Pointer params (discipline applies). -/
def ptrParams (raw : RawFunc) : List RawParam :=
  raw.params.filter (fun p => isPtrType p.ctype)

/-- No loop-exit or switch ops (S3a admits them only in the exact
    `skip_sum` / `cls` shapes; every older shape excludes them so a
    `break` can never validate as a plain loop). -/
def noBreakContinueSwitch (text : String) : Bool :=
  !containsSubstr text "cir.break" &&
  !containsSubstr text "cir.continue" &&
  !containsSubstr text "cir.switch" &&
  !containsSubstr text "cir.case"

/-- `add`: two by-value `i32`s, `i32` return, `nsw` add, no control flow,
    no calls (leaf: S1 callers target it, recursion is rejected below). -/
def isAddShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, b] =>
    isI32 a.ctype && isI32 b.ctype && isI32 raw.ret &&
    containsSubstr raw.text "cir.add nsw" &&
    noBreakContinueSwitch raw.text &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- `incr`: one `noalias` `i32` pointer, void return, `nsw` add. -/
def isIncrShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [p] =>
    noBreakContinueSwitch raw.text &&
    isPtrType p.ctype &&
    (match ptrInner p.ctype with | some inner => isI32 inner | none => false) &&
    raw.ret == "" &&
    containsSubstr raw.text "cir.add nsw" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while"
  | _ => false

/-- `choose`: `bool` + two `noalias` pointers, pointer return, ternary. -/
def isChooseShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [b, x, y] =>
    noBreakContinueSwitch raw.text &&
    isBoolType b.ctype && !isPtrType b.ctype &&
    isPtrType x.ctype && isPtrType y.ctype &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    containsSubstr raw.text "cir.ternary" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- `sum_array`: `noalias` pointer + length, `u32` return, bounded loop. -/
def isSumShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, n] =>
    noBreakContinueSwitch raw.text &&
    isPtrType a.ctype && isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 raw.ret &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-! ## Heap-plumbing predicates (line-aware) -/

/-- A line defining a real global (`cir.global @g = ...`), as opposed to
    merely *using* one (`cir.get_global`, which `malloc`/`free` plumbing
    also does — those lines contain `get_`). -/
def lineHasGlobalDef (line : String) : Bool :=
  containsSubstr line "cir.global" && !containsSubstr line "cir.get_global"

/-- A `cir.get_global` line unrelated to `malloc`/`free`/`realloc` plumbing
    (real CIR takes `@malloc`/`@free`/`@realloc` addresses via `get_global`;
    those lines are heap plumbing, gated by the vec shapes instead). -/
def lineHasNonHeapGlobal (line : String) : Bool :=
  containsSubstr line "cir.get_global" &&
  !containsSubstr line "@malloc" && !containsSubstr line "@free" &&
  !containsSubstr line "@realloc"

/-- A function-pointer type outside `malloc`/`free` plumbing (whose
    `get_global` ascriptions mention `cir.func<`). Actual indirect calls
    are still caught by `call_indirect` above. -/
def lineHasBareFuncPtr (line : String) : Bool :=
  containsSubstr line "cir.func<" && !containsSubstr line "get_global"

/-- Whole-text wrappers (split on newlines, cf. `hasWrappingSignedArith`). -/
def hasGlobalDef (text : String) : Bool :=
  (text.splitOn "\n").any lineHasGlobalDef

def hasNonHeapGlobal (text : String) : Bool :=
  (text.splitOn "\n").any lineHasNonHeapGlobal

def hasBareFuncPtr (text : String) : Bool :=
  (text.splitOn "\n").any lineHasBareFuncPtr

/-- `free` *call* sites (`cir.call @free(`/n): the `cir.func private @free`
    declaration also contains `@free(`, so a bare `@free(` needle would
    double-count every file. -/
def freeCallCount (text : String) : Nat :=
  ((text.splitOn "\n").filter (fun line =>
    containsSubstr line "cir.call @free(")).length

/-- `malloc` *call* sites (`cir.call @malloc(`/n): same line-aware
    rationale as `freeCallCount` — the `cir.func private @malloc`
    declaration also contains `@malloc(`. -/
def mallocCallCount (text : String) : Nat :=
  ((text.splitOn "\n").filter (fun line =>
    containsSubstr line "cir.call @malloc(")).length

/-- `realloc` *call* sites (`cir.call @realloc(`/n): same line-aware
    rationale as `freeCallCount` — the `cir.func private @realloc`
    declaration also contains `@realloc(`. -/
def reallocCallCount (text : String) : Nat :=
  ((text.splitOn "\n").filter (fun line =>
    containsSubstr line "cir.call @realloc(")).length

/-- A line performing a non-heap, non-`realloc` call (`malloc`/`free`
    plumbing excluded — those are gated by the vec shapes instead;
    `realloc` is gated by the M1c `vec_realloc` shape instead). -/
def lineHasNonHeapNonReallocCall (line : String) : Bool :=
  lineHasNonHeapCall line && !containsSubstr line "cir.call @realloc("

/-- Whole-text wrapper. -/
def hasNonHeapNonReallocCall (text : String) : Bool :=
  (text.splitOn "\n").any lineHasNonHeapNonReallocCall

/-! ## S2: struct-by-value shape (`translate`) -/

/-- The S2 `Point` struct type: CIRGen's `!rec_Point` alias (long-form
    `!cir.struct<"Point" …>` also matches via the `"Point"` substring;
    applied to short type tokens only, never whole text). -/
def isPointType (t : String) : Bool :=
  t == "!rec_Point" || containsSubstr t "Point"

/-- `translate`: by-value `Point` + two `i32` deltas, `Point` return,
    `cir.get_member` field reads (`x`/`y`) + `nsw` adds, no calls,
    no control flow, no heap, no indexing. -/
def isTranslateShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [p, dx, dy] =>
    noBreakContinueSwitch raw.text &&
    isPointType p.ctype && !isPtrType p.ctype &&
    isI32 dx.ctype && isI32 dy.ctype &&
    isPointType raw.ret &&
    containsSubstr raw.text "cir.get_member" &&
    containsSubstr raw.text "cir.add nsw" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-! ## S1: caller shapes (DAG calls into admitted leaves) -/

/-- `add_caller`: three by-value `i32`s, `i32` return, calls `@add`
    (exactly the admitted leaf; arithmetic lives in the callee, so no
    local `nsw`), no self-call (recursion rejected), no other callees. -/
def isAddCallerShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [x, y, z] =>
    noBreakContinueSwitch raw.text &&
    isI32 x.ctype && isI32 y.ctype && isI32 z.ctype && isI32 raw.ret &&
    callsFunc raw.text "add" &&
    !callsFunc raw.text raw.name &&
    !callsFunc raw.text "sum_array" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- `sum_caller`: `noalias` pointer + length, `u32` return, single call to
    `@sum_array` (the loop lives in the callee, so no local `cir.for`). -/
def isSumCallerShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, n] =>
    noBreakContinueSwitch raw.text &&
    isPtrType a.ctype && isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 raw.ret &&
    callsFunc raw.text "sum_array" &&
    !callsFunc raw.text raw.name &&
    !callsFunc raw.text "add" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- `vec_alloc`: length param, `u32` return, `malloc` + bounded `cir.for`
    loops over `cir.ptr_stride` + exactly one `free` call. -/
def isVecShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    noBreakContinueSwitch raw.text &&
    isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 raw.ret &&
    containsSubstr raw.text "malloc" &&
    !containsSubstr raw.text "realloc" &&
    containsSubstr raw.text "cir.call @free(" &&
    !(1 < freeCallCount raw.text) &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.switch"
  | _ => false

/-- `vec_copy_sum` (M1a): length param, `u32` return, two `malloc`s +
    bounded `cir.for` loops over `cir.ptr_stride` + exactly two `free`
    calls. The two `malloc` sites yield two `malloc` results, so the
    blocks are disjoint by construction (no aliasing expressible);
    exactly-two-`free` keeps the strict linear discipline (M1d loosens
    this later). -/
def isVec2Shape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    noBreakContinueSwitch raw.text &&
    isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 raw.ret &&
    mallocCallCount raw.text == 2 &&
    freeCallCount raw.text == 2 &&
    !containsSubstr raw.text "realloc" &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.switch"
  | _ => false

/-- `vec_alloc_u64` (M1b): length param, `u64` return, `malloc` + bounded
    `cir.for` loops over `cir.ptr_stride` + exactly one `free` call.
    Monomorphized mirror of `isVecShape` at width 64; disjoint from it by
    the return type (`isU32` vs `isU64`). -/
def isVec64Shape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    noBreakContinueSwitch raw.text &&
    isLengthType n.ctype && !isPtrType n.ctype &&
    isU64 raw.ret &&
    containsSubstr raw.text "malloc" &&
    !containsSubstr raw.text "realloc" &&
    containsSubstr raw.text "cir.call @free(" &&
    !(1 < freeCallCount raw.text) &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.switch"
  | _ => false

/-- `vec_realloc` (M1c): length param, `u32` return, one `malloc` + one
    `realloc` + exactly one `free` call, bounded `cir.for` loops over
    `cir.ptr_stride`. The single `realloc` grows the single live block
    (`realloc` never fails per the unbounded convention; the
    `realloc(p, 0)` = `free` and `realloc(NULL, n)` = `malloc` spellings
    are rejected by the dedicated branch in `validate`, never admitted
    here). -/
def isVecReallocShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    noBreakContinueSwitch raw.text &&
    isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 raw.ret &&
    mallocCallCount raw.text == 1 &&
    reallocCallCount raw.text == 1 &&
    freeCallCount raw.text == 1 &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    !hasNonHeapNonReallocCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.switch"
  | _ => false

/-! ## S3b: 64-bit loop-free widths (`add64`, `addu64`) -/

/-- `add64`: two by-value `i64`s, `i64` return, `nsw` add, no control
    flow, no calls — the `add` shape at width 64. -/
def isAdd64Shape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, b] =>
    isI64 a.ctype && isI64 b.ctype && isI64 raw.ret &&
    containsSubstr raw.text "cir.add nsw" &&
    noBreakContinueSwitch raw.text &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- `addu64`: two by-value `u64`s, `u64` return, plain (wrapping)
    unsigned add, no `nsw`, no control flow, no calls. -/
def isAddu64Shape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, b] =>
    isU64 a.ctype && isU64 b.ctype && isU64 raw.ret &&
    containsSubstr raw.text "cir.add " &&
    !containsSubstr raw.text "nsw" &&
    noBreakContinueSwitch raw.text &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- Small-width promotion: 8/16-bit integers appear only via `cir.cast`
    promotion to `i32` (S3b probe); there is no native small-width
    arithmetic to model, so any occurrence rejects loudly. -/
def hasSmallWidthInt (text : String) : Bool :=
  containsSubstr text "!s8i" || containsSubstr text "!u8i" ||
  containsSubstr text "!s16i" || containsSubstr text "!u16i" ||
  containsSubstr text "<s, 8>" || containsSubstr text "<s,8>" ||
  containsSubstr text "<u, 8>" || containsSubstr text "<u,8>" ||
  containsSubstr text "<s, 16>" || containsSubstr text "<s,16>" ||
  containsSubstr text "<u, 16>" || containsSubstr text "<u,16>"

/-! ## Forbidden constructs (all `outOfSubset`) -/

/-- One source line performs signed `add`/`sub`/`mul` on `i32`/`i64`
    without the `nsw` marker (wrapping signed overflow: UB in C,
    untranslatable). Per-line (not whole-text): `sum_array` legitimately
    mixes an unsigned wrapping `cir.add` (`!u32i`) with `!s32i` casts
    elsewhere, so the type and the op must occur on the same line. -/
def lineHasWrappingSignedArith (line : String) : Bool :=
  (containsSubstr line "cir.add " || containsSubstr line "cir.sub " ||
    containsSubstr line "cir.mul ") &&
  (containsSubstr line "!s32i" || containsSubstr line "<s, 32>" ||
    containsSubstr line "<s,32>" ||
    containsSubstr line "!s64i" || containsSubstr line "<s, 64>" ||
    containsSubstr line "<s,64>") &&
  !containsSubstr line "nsw"

/-- Whole-text wrapper (cf. `hasWrappingSignedArith`). -/
def hasWrappingSignedArith (text : String) : Bool :=
  (text.splitOn "\n").any lineHasWrappingSignedArith

/-! ## S3a: control-flow shapes (nested loops, break/continue,
early return, switch-as-if-chain) -/

/-- Count whole-text occurrences of a needle (for exact-shape pins:
    two `cir.for`, one `cir.return`, three `cir.case(`, …). -/
def opCount (text needle : String) : Nat :=
  ((text.splitOn needle).length - 1)

/-- `nested_sum`: two `u32` bounds, `u32` return, exactly two `cir.for`
    (nested), plain unsigned `cir.add` + `cir.mul` (wrapping; no `nsw`),
    single return, no calls/heap/control beyond the loops, no
    break/continue/switch. -/
def isNestedShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n, m] =>
    isU32 n.ctype && isU32 m.ctype && isU32 raw.ret &&
    opCount raw.text "cir.for" == 2 &&
    opCount raw.text "cir.return" == 1 &&
    containsSubstr raw.text "cir.mul " &&
    containsSubstr raw.text "cir.add " &&
    !containsSubstr raw.text "nsw" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.break" &&
    !containsSubstr raw.text "cir.continue" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.case"
  | _ => false

/-- `skip_sum`: one `u32` bound, `u32` return, one `cir.for` with
    `cir.break` + `cir.continue` guarded by `cir.cmp eq` against the
    pinned consts `2`/`8` (the canonical `Func` hard-codes them, so the
    shape must too), plain unsigned `cir.add`, single return. -/
def isSkipShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    isU32 n.ctype && isU32 raw.ret &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.break" &&
    containsSubstr raw.text "cir.continue" &&
    containsSubstr raw.text "cir.if" &&
    containsSubstr raw.text "cir.cmp eq" &&
    containsSubstr raw.text "#cir.int<2>" &&
    containsSubstr raw.text "#cir.int<8>" &&
    containsSubstr raw.text "cir.add " &&
    opCount raw.text "cir.return" == 1 &&
    !containsSubstr raw.text "nsw" &&
    !containsSubstr raw.text "cir.mul" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.case"
  | _ => false

/-- `find_eq`: `noalias` `u32` pointer + length + `u32` needle, `u32`
    return, bounded `cir.for` over `cir.ptr_stride` with a `cir.cmp eq`
    guard and two `cir.return` (early return in the loop, fall-through
    after). The `u64` (`size_t`) length spelling is admitted
    (`isLengthType`); the canonical `Func` narrows it to `u32`, exactly
    as in `sum` (runtime excess is `OOB`). -/
def isFindEqShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, n, k] =>
    isPtrType a.ctype && isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 k.ctype && !isPtrType k.ctype &&
    isU32 raw.ret &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    containsSubstr raw.text "cir.if" &&
    containsSubstr raw.text "cir.cmp eq" &&
    opCount raw.text "cir.return" == 2 &&
    !containsSubstr raw.text "nsw" &&
    !containsSubstr raw.text "cir.mul" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.break" &&
    !containsSubstr raw.text "cir.continue" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.case"
  | _ => false

/-- Text-level lowering check for `cir.switch`: equality cases on the
    pinned consts `0`/`1` plus `default`, every case returning a pinned
    const (`10`/`20`/`30`). This is the `forbiddenOp` exemption gate;
    full admission additionally pins the signature (`isClsShape`). -/
def isClsLowerableText (text : String) : Bool :=
  containsSubstr text "cir.switch" &&
  opCount text "cir.case(" == 3 &&
  containsSubstr text "cir.case(equal, [#cir.int<0>" &&
  containsSubstr text "cir.case(equal, [#cir.int<1>" &&
  containsSubstr text "cir.case(default, [])" &&
  containsSubstr text "#cir.int<10>" &&
  containsSubstr text "#cir.int<20>" &&
  containsSubstr text "#cir.int<30>"

/-- `cls`: one `u32` scrutinee, `u32` return, lowerable `cir.switch`
    (see `isClsLowerableText`), no loops/calls/heap/indexing. -/
def isClsShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [x] =>
    isU32 x.ctype && isU32 raw.ret &&
    isClsLowerableText raw.text &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.break" &&
    !containsSubstr raw.text "cir.continue" &&
    !containsSubstr raw.text "cir.mul" &&
    !containsSubstr raw.text "nsw"
  | _ => false

/-- A line with a bare unstructured branch (`cir.br` from `goto`),
    excluding `cir.break` (which merely *contains* the substring
    `cir.br`: S3a admits `break` in the exact `skip_sum` shape). -/
def lineHasBareBr (line : String) : Bool :=
  containsSubstr line "cir.br" && !containsSubstr line "cir.break"

/-- Whole-text wrapper. -/
def hasBareBr (text : String) : Bool :=
  (text.splitOn "\n").any lineHasBareBr

/-- First forbidden construct found (all `outOfSubset`), if any. -/
def forbiddenOp (text : String) : Option String :=
  if containsSubstr text "cir.try" then some "exception handling (`cir.try`/cleanup/EH)"
  else if containsSubstr text "landingpad" then some "exception handling (landingpad)"
  else if containsSubstr text "int_to_ptr" then some "integer→pointer cast"
  else if containsSubstr text "ptr_to_int" then some "pointer→integer cast"
  else if containsSubstr text ": !cir.ptr<!cir.void>" then some "`void*` (unownable)"
  else if containsSubstr text "-> !cir.ptr<!cir.void>" then some "`void*` (unownable)"
  else if containsSubstr text "volatile" then some "`volatile` access"
  else if containsSubstr text "atomic" then some "atomic access"
  else if containsSubstr text "inline_asm" then some "inline assembly"
  else if containsSubstr text "!cir.float" then some "float type"
  else if containsSubstr text "!cir.double" then some "double type"
  else if containsSubstr text "setjmp" then some "`setjmp` (non-local control flow)"
  else if containsSubstr text "longjmp" then some "`longjmp` (non-local control flow)"
  else if hasGlobalDef text then some "global state (`cir.global`: only read-only `const` globals, and none yet in v0.1)"
  else if hasNonHeapGlobal text then some "global access (`cir.get_global`: only read-only `const` globals, and none yet in v0.1)"
  else if containsSubstr text "call_indirect" then some "function pointer (indirect call: no function pointers in v0.1)"
  else if hasBareFuncPtr text then some "function pointer type (no function pointers in v0.1)"
  else if containsSubstr text "stack_save" then some "variable-length array (`stack_save`: no VLAs in v0.1)"
  else if containsSubstr text "stack_restore" then some "variable-length array (`stack_restore`: no VLAs in v0.1)"
  else if containsSubstr text "va_arg" then some "variadic arguments (`va_arg`: no variadics in v0.1)"
  else if containsSubstr text "cir.switch" && !isClsLowerableText text then some "`switch` (`cir.switch`: lower to an if-chain before CIR or it is rejected)"
  else if hasBareBr text then some "unstructured branch (`cir.br` from `goto`: no `goto` in v0.1; structured `cir.cond_br`/`cir.for` only)"
  else if containsSubstr text "bitfield" then some "bitfield (no bitfields in v0.1)"
  else if hasWrappingSignedArith text then some "signed wrapping arithmetic without `nsw` (signed overflow is UB in C: mark the op `nsw` or use unsigned arithmetic)"
  else none

/-! ## The gate -/

/-- The verified gate: `RawFunc` + oracle fact → admitted `Func`.
    Only the canonical shapes pass (`add`/`incr`/`choose`/`sum`,
    `vec_alloc`, `vec_alloc_u64` (M1b), `vec_realloc` (M1c), S1 DAG
    callers, S2 `translate`, S3a control flow, S3b 64-bit loop-free
    `add64`/`addu64`); everything
    else is rejected with a precise code (see the module docstring for
    check order). -/
def validate (raw : RawFunc) (oracle : OracleFact) : Validation :=
  if raw.name != oracle.funcName then
    reject raw.name .outOfSubset
      s!"out-of-subset: oracle fact is for '{oracle.funcName}', not '{raw.name}' (wiring error; refusing to translate)"
  else match forbiddenOp raw.text with
  | some what =>
    reject raw.name .outOfSubset
      s!"out-of-subset: function '{raw.name}' uses {what}, outside the v0.1 Ownable-C subset (see docs/CIR_SUBSET.md)"
  | none =>
    match raw.params.find? (fun p => isPtrType p.ctype && !p.noalias) with
    | some p =>
      reject raw.name .aliasReject
        s!"alias-reject: function '{raw.name}': param '{p.name}' has pointer type '{p.ctype}' without `__restrict__` (no `llvm.noalias`): uniqueness cannot be established (see docs/OWNERSHIP.md rule 1)"
    | none =>
      if !(ptrParams raw).isEmpty && !verdictAdmits oracle.verdict then
        let why := match oracle.verdict with
          | .mayAlias => "reports `mayAlias`"
          | .unknown => "is inconclusive (`unknown`)"
          | .noalias => "is unreachable"
        reject raw.name .aliasReject
          s!"alias-reject: function '{raw.name}': oracle {why}: live pointer params require an explicit `noalias` verdict (see docs/OWNERSHIP.md)"
      else if isAddShape raw then
        .ok { addFunc with name := raw.name }
      else if isIncrShape raw then
        .ok { incrFunc with name := raw.name }
      else if isChooseShape raw then
        .ok { chooseFunc with name := raw.name }
      else if isSumShape raw then
        .ok { sumFunc with name := raw.name }
      else if isVecShape raw then
        .ok { vecFunc with name := raw.name }
      else if isVec2Shape raw then
        .ok { vec2Func with name := raw.name }
      else if isVec64Shape raw then
        .ok { vec64Func with name := raw.name }
      else if isVecReallocShape raw then
        .ok { vecReallocFunc with name := raw.name }
      else if isAddCallerShape raw then
        .ok { addCallerFunc with name := raw.name }
      else if isSumCallerShape raw then
        .ok { sumCallerFunc with name := raw.name }
      else if isTranslateShape raw then
        .ok { translateFunc with name := raw.name }
      else if isNestedShape raw then
        .ok { nestedFunc with name := raw.name }
      else if isSkipShape raw then
        .ok { skipFunc with name := raw.name }
      else if isFindEqShape raw then
        .ok { findEqFunc with name := raw.name }
      else if isClsShape raw then
        .ok { clsFunc with name := raw.name }
      else if isAdd64Shape raw then
        .ok { add64Func with name := raw.name }
      else if isAddu64Shape raw then
        .ok { addu64Func with name := raw.name }
      else if callsFunc raw.text raw.name then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls itself (recursive call): S1 admits DAG calls into call-free leaves only (see docs/ROADMAP.md S1)"
      else if hasNonHeapCall raw.text &&
          !containsSubstr raw.text "realloc" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses function call outside the admitted call shapes (S1: calls into `add`/`sum_array` with the exact `add_caller`/`sum_caller` shapes only), outside the Ownable-C subset (see docs/SUBSET.md)"
      else if containsSubstr raw.text "malloc" &&
          !containsSubstr raw.text "cir.call @free(" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls `malloc` without a matching `free`: heap blocks must be freed exactly once on every path (strict linear discipline, see docs/SUBSET.md rule 8 and docs/ROADMAP.md)"
      else if 1 < freeCallCount raw.text &&
          mallocCallCount raw.text < freeCallCount raw.text then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls `free` more times than `malloc`: double-`free` is rejected (heap blocks are freed exactly once, see docs/SUBSET.md rule 8)"
      else if containsSubstr raw.text "realloc" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses `realloc` outside the admitted `vec_realloc` shape (single `malloc`, one `realloc` to `2*n`, single `free`, fill / fill-extension / sum discipline; `realloc(p, 0)` (= `free`) and `realloc(NULL, n)` (= `malloc`) spellings are rejected: use `free`/`malloc` directly, see docs/ROADMAP.md M1c)"
      else if containsSubstr raw.text "malloc" ||
          containsSubstr raw.text "cir.call @free(" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses heap allocation (`malloc`/`free`/`realloc`) outside the admitted `vec_alloc` / `vec_copy_sum` / `vec_alloc_u64` / `vec_realloc` shapes (see docs/ROADMAP.md)"
      else if isPtrType raw.ret then
        reject raw.name .escapeReject
          s!"escape-reject: function '{raw.name}' returns pointer type '{raw.ret}' outside the borrow-return (`choose`) shape: the return must be exactly one of the `noalias` inputs (see docs/SUBSET.md rule 6)"
      else if containsSubstr raw.text "cir.ptr_stride" then
        reject raw.name .oobPossible
          s!"oob-possible: function '{raw.name}' indexes via `cir.ptr_stride` without the length-paired bound form (`(ptr, n)` params + `cir.for`): unbounded indexing cannot be functionalized (see docs/SUBSET.md rule 4)"
      else if containsSubstr raw.text "cir.get_member" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses struct field access (`cir.get_member`) outside the admitted `translate` shape (S2: by-value `Point` + two `i32` deltas with `nsw` field adds only; see docs/SUBSET.md)"
      else if containsSubstr raw.text "cir.switch" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses `switch` (`cir.switch`) outside the admitted `cls` shape (S3a: equality cases on `0`/`1` + `default`, every case a bare const `return` of `10`/`20`/`30`; see docs/SUBSET.md)"
      else if containsSubstr raw.text "cir.break" ||
          containsSubstr raw.text "cir.continue" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses `break`/`continue` outside the admitted `skip_sum` shape (S3a: single bounded `u32` loop, `continue` at `i == 2`, `break` at `i == 8`, wrapping `s += i` only; see docs/SUBSET.md)"
      else if hasSmallWidthInt raw.text then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses 8/16-bit integers (CIRGen promotes them to `i32` via `cir.cast`: no native small-width arithmetic to model; S3b admits 64-bit loop-free widths only, see docs/SUBSET.md)"
      else
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' is not in the admitted Phase-4 fragment (see `matchFrag` contract in `Circe.Emit`)"

/-! ## Text-level pipeline + machine-checked corpus linkage -/

/-- End-to-end pipeline at the text level: parse one function, validate
    against the oracle fact, emit file bytes. Errors are message strings;
    success is the emitted file text (compare with `tests/golden/`).
    String-level throughout, so `native_decide` checks below need no
    `DecidableEq` on `CoreIR` (which core Lean cannot derive for the
    `List`-nested `CType`). -/
def runPipeline (text : String) (oracle : OracleFact) : Except String String :=
  match parseFunc text with
  | none => .error "parse failed: no `cir.func` signature found"
  | some raw =>
    match validate raw oracle with
    | .error rej =>
      .error s!"{rej.func}: [{(repr rej.code).pretty}] {rej.message}"
    | .ok f => .ok (emitFileText (emitFunc f))

/-- `Option` projection (core Lean decides `Option String` equality, but
    not `Except` equality — so the machine-checked examples below use
    this; `runPipeline` itself keeps the richer error type for the
    golden-runner diagnostics). -/
def runPipelineOpt (text : String) (oracle : OracleFact) : Option String :=
  (runPipeline text oracle).toOption

/-- The checked-in `add` CIR validates (pure: oracle `unknown` suffices)
    and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/add.cir") ⟨"add", .unknown⟩
    = some (include_str "../tests/golden/Add.lean") := by native_decide

/-- The checked-in `incr` CIR validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/incr_ptr.cir")
    ⟨"incr", .noalias⟩
    = some (include_str "../tests/golden/Incr.lean") := by native_decide

/-- The checked-in `choose` CIR validates and emits exactly the golden
    (forward + backward). -/
example : runPipelineOpt (include_str "../tests/cir/choose_ptr.cir")
    ⟨"choose", .noalias⟩
    = some (include_str "../tests/golden/Choose.lean") := by native_decide

/-- The checked-in `sum_array` CIR validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/sum_array.cir")
    ⟨"sum_array", .noalias⟩
    = some (include_str "../tests/golden/SumArray.lean") := by native_decide

/-- The checked-in `vec_alloc` CIR (real CIRGen output with `malloc`/`free`
    plumbing) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/vec_alloc.cir")
    ⟨"vec_alloc", .unknown⟩
    = some (include_str "../tests/golden/VecAlloc.lean") := by native_decide

/-- The checked-in `vec_copy_sum` CIR (M1a: real CIRGen output, two
    `malloc`s + two `free`s) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/vec_copy_sum.cir")
    ⟨"vec_copy_sum", .unknown⟩
    = some (include_str "../tests/golden/VecCopySum.lean") := by native_decide

/-- The checked-in `vec_alloc_u64` CIR (M1b: real CIRGen output, `u64`
    elements) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/vec_alloc_u64.cir")
    ⟨"vec_alloc_u64", .unknown⟩
    = some (include_str "../tests/golden/VecAllocU64.lean") := by native_decide

/-- The checked-in `vec_realloc` CIR (M1c: real CIRGen output, `malloc` +
    `realloc` + `free`) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/vec_realloc.cir")
    ⟨"vec_realloc", .unknown⟩
    = some (include_str "../tests/golden/VecRealloc.lean") := by native_decide

/-- The checked-in `add_caller` CIR (two DAG calls into `add`) validates
    and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/add_caller.cir")
    ⟨"add_caller", .unknown⟩
    = some (include_str "../tests/golden/AddCaller.lean") := by native_decide

/-- The checked-in `sum_caller` CIR (single DAG call into `sum_array`)
    validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/sum_caller.cir")
    ⟨"sum_caller", .noalias⟩
    = some (include_str "../tests/golden/SumCaller.lean") := by native_decide

/-- The checked-in `translate` CIR (real CIRGen output with
    `cir.get_member` field reads) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/struct_by_value.cir")
    ⟨"translate", .unknown⟩
    = some (include_str "../tests/golden/StructByValue.lean") := by native_decide

/-- The checked-in `nested_sum` CIR (real CIRGen output, nested
    `cir.for`) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/nested_sum.cir")
    ⟨"nested_sum", .unknown⟩
    = some (include_str "../tests/golden/NestedSum.lean") := by native_decide

/-- The checked-in `skip_sum` CIR (real CIRGen output with
    `cir.break`/`cir.continue`) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/skip_sum.cir")
    ⟨"skip_sum", .unknown⟩
    = some (include_str "../tests/golden/SkipSum.lean") := by native_decide

/-- The checked-in `find_eq` CIR (real CIRGen output, early return in a
    bounded loop) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/find_eq.cir")
    ⟨"find_eq", .noalias⟩
    = some (include_str "../tests/golden/FindEq.lean") := by native_decide

/-- The checked-in `cls` CIR (real CIRGen output, `cir.switch` lowered
    to an if-chain) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/cls.cir")
    ⟨"cls", .unknown⟩
    = some (include_str "../tests/golden/Cls.lean") := by native_decide

/-- The checked-in `add64` CIR (real CIRGen output, `nsw` add on
    `!s64i`) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/add64.cir")
    ⟨"add64", .unknown⟩
    = some (include_str "../tests/golden/Add64.lean") := by native_decide

/-- The checked-in `addu64` CIR (real CIRGen output, wrapping add on
    `!u64i`) validates and emits exactly the golden. -/
example : runPipelineOpt (include_str "../tests/cir/addu64.cir")
    ⟨"addu64", .unknown⟩
    = some (include_str "../tests/golden/Addu64.lean") := by native_decide
