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
   function pointers, VLAs, variadics, cleanup regions (`cir.cleanup`),
   trap (`cir.trap`), `goto` (`cir.br`),
   bitfields, signed wrapping arithmetic without `nsw` — all `outOfSubset`;
   `switch` is shape-aware (the admitted `cls` lowering passes, all other
   `switch` uses are `outOfSubset`);
   heap (`malloc`/`free`/`realloc`) and calls are shape-aware (see step 5):
   the admitted `vec_alloc` / `vec_copy_sum` / `vec_alloc_u64` /
   `vec_realloc` (M1c) shapes pass (M1d: each with `free <= expected`:
   leak is forgetting a value, sound),
    all other heap/call uses are
   `outOfSubset` with dedicated messages (double-`free`,
   `realloc`-shape, heap-shape, calls);
3. pointer discipline (`aliasReject`: raw pointer without `__restrict__`
   and without the C++ single-reference triple (N2c carve-out: the single
   live array of a recovered reader shape — `recoveredNoalias` —
   recovers noalias from construction instead of attr text), oracle
   verdict other than `noalias` with live oracle-governed pointer params
   (same N2c carve-out), or writer+reader ambiguity — two or more live
   oracle-governed pointer params outside the `choose` borrow-return
   shape);
5. shape admission (canonical `Func` or a precise code: `escapeReject`
   for non-`choose` pointer returns (borrow-after-free when a heap
   `free`/`delete` is present, escaping-borrow when there are no pointer
   inputs at all), `oobPossible` for unbounded
   `ptr_stride`, `outOfSubset` otherwise, including misshapen struct
   uses outside the S2 `translate` shape, the M2a method shapes, and
   the M2b `Acc` leaf shapes, the M2b entry shape (with its
   `cleanup`/`trap` exemption), and by-value struct params stuck in
   the deferred `coerce` lowering).
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
    those are gated by the vec shape instead; `new`/`delete` excluded —
    those are gated by the M2c `box_through` shape instead). -/
def lineHasNonHeapCall (line : String) : Bool :=
  containsSubstr line "cir.call @" &&
  !containsSubstr line "cir.call @malloc(" &&
  !containsSubstr line "cir.call @free(" &&
  !containsSubstr line "cir.call @_Znwm(" &&
  !containsSubstr line "cir.call @_ZdlPvm("

/-- Whole-text wrapper (cf. `hasWrappingSignedArith`). -/
def hasNonHeapCall (text : String) : Bool :=
  (text.splitOn "\n").any lineHasNonHeapCall

/-- Count whole-text occurrences of a needle (for exact-shape pins:
    two `cir.for`, one `cir.call @`, three `cir.case(`, …). -/
def opCount (text needle : String) : Nat :=
  ((text.splitOn needle).length - 1)

/-- Pointer params (discipline applies). -/
def ptrParams (raw : RawFunc) : List RawParam :=
  raw.params.filter (fun p => isPtrType p.ctype)

/-- Pointer params the oracle must speak about: every raw pointer
    except C++ single-reference (`this` / `const&`) params, whose
    uniqueness is established by the `nonnull + dereferenceable +
    noundef` attrs in the CIR text itself, so no oracle fact is needed
    (M2). (`__restrict__` / `noalias` params still need an explicit
    `noalias` verdict: the attr is a claim, the verdict confirms it.) -/
def oracleParams (raw : RawFunc) : List RawParam :=
  raw.params.filter (fun p => isPtrType p.ctype && !p.singleRef)

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

/-- `new` *call* sites (`cir.call @_Znwm(`/n): same line-aware
    rationale as `freeCallCount` — the `cir.func private @_Znwm`
    declaration also contains `@_Znwm(`. -/
def newCallCount (text : String) : Nat :=
  ((text.splitOn "\n").filter (fun line =>
    containsSubstr line "cir.call @_Znwm(")).length

/-- Sized-`delete` *call* sites (`cir.call @_ZdlPvm(`/n): same line-aware
    rationale as `freeCallCount` — the `cir.func private @_ZdlPvm`
    declaration also contains `@_ZdlPvm(`. -/
def deleteCallCount (text : String) : Nat :=
  ((text.splitOn "\n").filter (fun line =>
    containsSubstr line "cir.call @_ZdlPvm(")).length

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

/-! ## M2a: POD const-method shapes (`_ZNK5Point3sumEv` leaf + entry) -/

/-- The M2a method leaf: single `this` parameter (`!cir.ptr<!rec_Point>`
    with the single-reference triple — never `noalias`), `i32` return,
    `cir.get_member` field reads (`x`/`y`) + `nsw` add: the S2 body with
    a pointer param. No calls, control flow, heap, or indexing. -/
def isMethodSumShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with | some inner => isPointType inner | none => false) &&
    isI32 raw.ret &&
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

/-- The M2a entry: single `const&` parameter (same triple-attr
    `!cir.ptr<!rec_Point>` as `this`), `i32` return, exactly one call
    site to the mangled method leaf (S1 `callRet` discipline: the
    arithmetic lives in the callee, so no local `nsw` / `get_member`). -/
def isPointSumRefShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [p] =>
    noBreakContinueSwitch raw.text &&
    isPtrType p.ctype && p.singleRef &&
    (match ptrInner p.ctype with | some inner => isPointType inner | none => false) &&
    isI32 raw.ret &&
    callsFunc raw.text "_ZNK5Point3sumEv" &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
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

/-! ## N4a: overload + namespace shapes -/

/-- Known overload-leaf callees (mangled): the two `i32`-leaf overloads
    plus the namespaced leaf. Caller gates admit calls into the
    (name, arity) pairs named in `validate` below; this registry names
    every known leaf for the wrong-shape rejection. Adding an overload
    extends the registry plus one gate arm — unknown mangled callees
    still reject. -/
def overloadLeafCallees : List String :=
  ["_Z3addii", "_Z3addiii", "_ZN2ns3addEii"]

/-- `add` at arity 3: the `_Z3addiii` overload leaf (two `nsw` adds
    threaded over three by-value `i32`s, no calls — the `add` idiom
    with one more operand). Name-agnostic like `isAddShape`: any
    triple-`i32` double-add validates to the canonical leaf. -/
def isAdd3Shape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, b, c] =>
    isI32 a.ctype && isI32 b.ctype && isI32 c.ctype && isI32 raw.ret &&
    containsSubstr raw.text "cir.add nsw" &&
    noBreakContinueSwitch raw.text &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- Single-delegation caller into one known overload leaf (S1
    discipline at a mangled name: exactly one call site to `callee`,
    arithmetic lives in the callee so no local `nsw`, no self-call). -/
def isOverloadCallerShape (raw : RawFunc) (callee : String) : Bool :=
  match raw.params with
  | [x, y] =>
    noBreakContinueSwitch raw.text &&
    isI32 x.ctype && isI32 y.ctype && isI32 raw.ret &&
    callsFunc raw.text callee &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
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

/-- Calls a known overload leaf but not with an admitted (name, arity,
    single-site) shape (e.g. wrong arg count, extra call sites, local
    arithmetic): dedicated rejection naming the admitted pairs. -/
def callsOverloadWrongShape (raw : RawFunc) : Bool :=
  overloadLeafCallees.any (callsFunc raw.text)

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
    loops over `cir.ptr_stride` + at most one `free` call (M1d: leak =
    forgetting a value, sound; `free` count is `≤ 1`, never `> malloc`). -/
def isVecShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    noBreakContinueSwitch raw.text &&
    isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 raw.ret &&
    mallocCallCount raw.text == 1 &&
    !containsSubstr raw.text "realloc" &&
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
    at most two `free`s (M1d: leak allowed, `free ≤ malloc` still enforced
    by the double-`free` gate below). -/
def isVec2Shape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    noBreakContinueSwitch raw.text &&
    isLengthType n.ctype && !isPtrType n.ctype &&
    isU32 raw.ret &&
    mallocCallCount raw.text == 2 &&
    !(2 < freeCallCount raw.text) &&
    !containsSubstr raw.text "realloc" &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.switch"
  | _ => false

/-- `vec_alloc_u64` (M1b): length param, `u64` return, `malloc` + bounded
    `cir.for` loops over `cir.ptr_stride` + at most one `free` call (M1d:
    leak allowed, like `isVecShape`).
    Monomorphized mirror of `isVecShape` at width 64; disjoint from it by
    the return type (`isU32` vs `isU64`). -/
def isVec64Shape (raw : RawFunc) : Bool :=
  match raw.params with
  | [n] =>
    noBreakContinueSwitch raw.text &&
    isLengthType n.ctype && !isPtrType n.ctype &&
    isU64 raw.ret &&
    mallocCallCount raw.text == 1 &&
    !containsSubstr raw.text "realloc" &&
    !(1 < freeCallCount raw.text) &&
    containsSubstr raw.text "cir.for" &&
    containsSubstr raw.text "cir.ptr_stride" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.switch"
  | _ => false

/-- `vec_realloc` (M1c): length param, `u32` return, one `malloc` + one
    `realloc` + at most one `free` call (M1d: leak allowed), bounded
    `cir.for` loops over `cir.ptr_stride`. The single `realloc` grows the single live block
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
    !(1 < freeCallCount raw.text) &&
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

/-! ## M3b: derived noalias (C only, text-derived, no oracle) -/

/-- C shapes with no pointer params (entry footprint vacuously disjoint:
    pure leaves, S1 `add_caller`, S2 `translate`, M1 heap shapes (whose
    disjointness is internal — distinct `malloc` results by construction),
    S3a flow, S3b widths). C++ shapes never match (M3d). -/
def isCNoPtrShape (raw : RawFunc) : Bool :=
  isAddShape raw || isAddCallerShape raw || isTranslateShape raw ||
  isVecShape raw || isVec2Shape raw || isVec64Shape raw ||
  isVecReallocShape raw || isNestedShape raw || isSkipShape raw ||
  isClsShape raw || isAdd64Shape raw || isAddu64Shape raw

/-- Text-derived noalias evidence (C only): no live pointer params and an
    admitted no-ptr C shape (vacuous), one `noalias` param in an admitted
    single-pointer shape (`incr` / `sum` / `sum_caller` / `find_eq`:
    singleton footprint), or two `noalias` params in the admitted
    two-pointer shape (`choose`: functionalized scalars, empty footprint).
    Everything else — including all C++ — is `false` (out of M3b scope).
    `Oracle.lookupOracle` / `verdictAdmits` are unchanged; `validate`
    behavior is unchanged (this is a parallel check, not a gate). -/
def derivedNoalias (raw : RawFunc) : Bool :=
  match oracleParams raw with
  | [] => isCNoPtrShape raw
  | [p] =>
    p.noalias &&
    (isIncrShape raw || isSumShape raw || isSumCallerShape raw ||
      isFindEqShape raw)
  | [p1, p2] =>
    p1.noalias && p2.noalias && isChooseShape raw
  | _ => false

/-- `derivedNoalias` never claims a param without its `noalias` attr:
    every oracle-governed param carries the text evidence. -/
theorem derivedNoalias_all_noalias (raw : RawFunc)
    (h : derivedNoalias raw = true) :
    ∀ p ∈ oracleParams raw, p.noalias = true := by
  intro q hq
  cases hps : oracleParams raw with
  | nil =>
    simp [hps] at hq
  | cons p rest =>
    cases rest with
    | nil =>
      have hD : (p.noalias &&
          (isIncrShape raw || isSumShape raw || isSumCallerShape raw ||
            isFindEqShape raw)) = true := by
        have hT : derivedNoalias raw = true := h
        unfold derivedNoalias at hT
        rw [hps] at hT
        exact hT
      have hpT : p.noalias = true := (Bool.and_eq_true_iff.mp hD).1
      have hqq : q = p := by simpa [hps] using hq
      subst hqq
      exact hpT
    | cons p2 rest2 =>
      cases rest2 with
      | nil =>
        have hD : (p.noalias && p2.noalias && isChooseShape raw) = true := by
          have hT : derivedNoalias raw = true := h
          unfold derivedNoalias at hT
          rw [hps] at hT
          exact hT
        have h1 : p.noalias = true :=
        (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp hD).1).1
        have h2 : p2.noalias = true :=
          (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp hD).1).2
        have hqq : q = p ∨ q = p2 := by simpa [hps] using hq
        cases hqq with
        | inl hqq => subst hqq; exact h1
        | inr hqq => subst hqq; exact h2
      | cons _ _ =>
        have hD : (false : Bool) = true := by
          have hT : derivedNoalias raw = true := h
          unfold derivedNoalias at hT
          rw [hps] at hT
          exact hT
        simp at hD

/-- `derivedNoalias` only fires inside the admitted C fragment (no C++
    shape, no misshapen text, no 3+-pointer shape). -/
theorem derivedNoalias_admitted_c (raw : RawFunc)
    (h : derivedNoalias raw = true) :
    (isCNoPtrShape raw || isIncrShape raw || isSumShape raw ||
      isSumCallerShape raw || isFindEqShape raw || isChooseShape raw) = true := by
  cases hps : oracleParams raw with
  | nil =>
    have hD : isCNoPtrShape raw = true := by
      have hT : derivedNoalias raw = true := h
      unfold derivedNoalias at hT
      rw [hps] at hT
      exact hT
    simp [hD]
  | cons p rest =>
    cases rest with
    | nil =>
      have hD : (p.noalias &&
          (isIncrShape raw || isSumShape raw || isSumCallerShape raw ||
            isFindEqShape raw)) = true := by
        have hT : derivedNoalias raw = true := h
        unfold derivedNoalias at hT
        rw [hps] at hT
        exact hT
      have hS := (Bool.and_eq_true_iff.mp hD).2
      rw [Bool.or_eq_true] at hS
      cases hS with
      | inl h1 =>
        rw [Bool.or_eq_true] at h1
        cases h1 with
        | inl h2 =>
          rw [Bool.or_eq_true] at h2
          cases h2 with
          | inl ha => simp [ha]
          | inr hb => simp [hb]
        | inr hc => simp [hc]
      | inr hd => simp [hd]
    | cons p2 rest2 =>
      cases rest2 with
      | nil =>
        have hD : (p.noalias && p2.noalias &&
            isChooseShape raw) = true := by
          have hT : derivedNoalias raw = true := h
          unfold derivedNoalias at hT
          rw [hps] at hT
          exact hT
        have hc : isChooseShape raw = true :=
          (Bool.and_eq_true_iff.mp hD).2
        simp [hc]
      | cons _ _ =>
        have hD : (false : Bool) = true := by
          have hT : derivedNoalias raw = true := h
          unfold derivedNoalias at hT
          rw [hps] at hT
          exact hT
        simp at hD

/-! ## N2c: construction-recovered noalias (reader shapes, no attr text) -/

/-- Text-level recovery (N2c): a single live pointer param in an admitted
    single-reader shape (`sum` / `sum_caller` / `find_eq`) recovers noalias
    from construction — singleton footprint (see `oracleNoalias_sum` /
    `oracleNoalias_sumCaller` / `oracleNoalias_findEq` in `Circe.Derived`,
    all attr-free) plus a CoreIR with no array-write primitive plus N2a
    reader alias-soundness — instead of demanding `llvm.noalias` attr
    text. Notably the param's `noalias` flag is NOT consulted: that is
    the recovery. Writers (`incr`, `choose`) and multi-pointer shapes
    never recover (see `recoveredNoalias_single_oracle`); C++ is untouched
    (`oracleParams` already excludes the single-ref triple). -/
def recoveredNoalias (raw : RawFunc) : Bool :=
  match oracleParams raw with
  | [_] =>
    isSumShape raw || isSumCallerShape raw || isFindEqShape raw
  | _ => false

/-- Recovery fires only inside the admitted single-reader shapes. -/
theorem recoveredNoalias_admitted_reader (raw : RawFunc)
    (h : recoveredNoalias raw = true) :
    (isSumShape raw || isSumCallerShape raw || isFindEqShape raw) = true := by
  cases hps : oracleParams raw with
  | nil =>
    have hD : (false : Bool) = true := by
      have hT : recoveredNoalias raw = true := h
      unfold recoveredNoalias at hT
      rw [hps] at hT
      exact hT
    simp at hD
  | cons p rest =>
    cases rest with
    | nil =>
      have hD : (isSumShape raw || isSumCallerShape raw ||
          isFindEqShape raw) = true := by
        have hT : recoveredNoalias raw = true := h
        unfold recoveredNoalias at hT
        rw [hps] at hT
        simpa using hT
      exact hD
    | cons _ _ =>
      have hD : (false : Bool) = true := by
        have hT : recoveredNoalias raw = true := h
        unfold recoveredNoalias at hT
        rw [hps] at hT
        exact hT
      simp at hD

/-- Recovery pins exactly one live oracle-governed param (the recovered
    reader is unambiguous; writers and writer+reader pairs never recover). -/
theorem recoveredNoalias_single_oracle (raw : RawFunc)
    (h : recoveredNoalias raw = true) :
    (oracleParams raw).length = 1 := by
  cases hps : oracleParams raw with
  | nil =>
    have hD : (false : Bool) = true := by
      have hT : recoveredNoalias raw = true := h
      unfold recoveredNoalias at hT
      rw [hps] at hT
      exact hT
    simp at hD
  | cons p rest =>
    cases rest with
    | nil => simp
    | cons _ _ =>
      have hD : (false : Bool) = true := by
        have hT : recoveredNoalias raw = true := h
        unfold recoveredNoalias at hT
        rw [hps] at hT
        exact hT
      simp at hD

/-- A param whose missing `llvm.noalias` is recovered from construction:
    the function is a recovered reader shape and this param is its single
    live array. (`recoveredNoalias_single_oracle` pins `oracleParams` to a
    singleton, so the recovered reader is unambiguous.) -/
def isRecoveredParam (raw : RawFunc) (p : RawParam) : Bool :=
  recoveredNoalias raw && decide (p ∈ oracleParams raw)

/-! ## M2b: value-ctor scope exemption (`acc_two` entry) -/

/-- The M2b `Acc` struct type: CIRGen's `!rec_Acc` alias (long-form
    `!cir.struct<"Acc" …>` also matches via the `"Acc"` substring;
    applied to short type tokens only, never whole text). -/
def isAccType (t : String) : Bool :=
  t == "!rec_Acc" || containsSubstr t "Acc"

/-- Text-level exemption check for the M2b entry: a `cleanup.scope` /
    `cleanup normal` region (the local `Acc` with its user-defined
    no-op dtor) closed by the unreachable `cir.trap`, with exactly the
    `acc_two` call multiset (1 ctor + 2 `add` + 1 `get` + 1 dtor, 5
    `cir.call` sites total) and no EH (`cir.try` / `personality` /
    `cleanup eh`) or heap. This is the `forbiddenOp` exemption gate
    (cf. `isClsLowerableText` for `cir.switch`); full admission
    additionally pins the signature (`isAccTwoShape`). -/
def isAccTwoExemptText (text : String) : Bool :=
  containsSubstr text "cir.cleanup.scope" &&
  containsSubstr text "cleanup normal" &&
  containsSubstr text "cir.trap" &&
  callsFunc text "_ZN3AccC2Ev" &&
  callsFunc text "_ZN3Acc3addEi" &&
  callsFunc text "_ZNK3Acc3getEv" &&
  callsFunc text "_ZN3AccD2Ev" &&
  opCount text "cir.call @" == 5 &&
  opCount text "cir.call @_ZN3Acc3addEi(" == 2 &&
  opCount text "cir.call @_ZN3AccC2Ev(" == 1 &&
  opCount text "cir.call @_ZNK3Acc3getEv(" == 1 &&
  opCount text "cir.call @_ZN3AccD2Ev(" == 1 &&
  !containsSubstr text "cir.try" &&
  !containsSubstr text "personality" &&
  !containsSubstr text "cleanup eh" &&
  !containsSubstr text "cir.call @malloc" &&
  !containsSubstr text "cir.call @free("

/-- The M2b ctor leaf: no params in CoreIR (field-init `s = 0`), but the
    CIR def takes single `this` (`!cir.ptr<!rec_Acc>` with the
    single-reference triple) and carries the `cxx_ctor` marker;
    `get_member` + `cir.const 0` + store, void return. No calls,
    control flow, heap, or indexing. -/
def isAccCtorShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with | some inner => isAccType inner | none => false) &&
    raw.ret == "" &&
    containsSubstr raw.text "cxx_ctor" &&
    containsSubstr raw.text "cir.get_member" &&
    containsSubstr raw.text "cir.const" &&
    containsSubstr raw.text "#cir.int<0>" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The M2b `add` method leaf: `this` + one `i32`, void return,
    `get_member` + one `nsw` add (the store-back is functionalized).
    No calls, control flow, heap, or indexing. -/
def isAccAddShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this, v] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with | some inner => isAccType inner | none => false) &&
    isI32 v.ctype && !isPtrType v.ctype &&
    raw.ret == "" &&
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

/-- The M2b `get` const-getter leaf: single `this`, `i32` return,
    `get_member` read with no arithmetic (identity). No calls, control
    flow, heap, or indexing. -/
def isAccGetShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with | some inner => isAccType inner | none => false) &&
    isI32 raw.ret &&
    containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.add nsw" &&
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

/-- The M2b trivial-dtor leaf: single `this`, void return, the
    `cxx_dtor` marker, empty body (no `get_member`, no arithmetic).
    No calls, control flow, heap, or indexing. -/
def isAccDtorShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with | some inner => isAccType inner | none => false) &&
    raw.ret == "" &&
    containsSubstr raw.text "cxx_dtor" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.add nsw" &&
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

/-- The N4b move-ctor leaf (`_ZN3AccC2EOS_`): two single-reference
    `this`-style params (destination + source, both `!cir.ptr<!rec_Acc>`
    with the triple), void return, the `cxx_ctor<…, move>` marker,
    `get_member` reads/writes + the `cir.const 0` source-zeroing store,
    no arithmetic. No calls, control flow, heap, or indexing. (The
    default-ctor shape takes exactly one param, so the two never
    overlap.) -/
def isAccMoveCtorShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [dst, src] =>
    noBreakContinueSwitch raw.text &&
    isPtrType dst.ctype && dst.singleRef &&
    (match ptrInner dst.ctype with | some inner => isAccType inner | none => false) &&
    isPtrType src.ctype && src.singleRef &&
    (match ptrInner src.ctype with | some inner => isAccType inner | none => false) &&
    raw.ret == "" &&
    containsSubstr raw.text "cxx_ctor" &&
    containsSubstr raw.text ", move>" &&
    containsSubstr raw.text "cir.get_member" &&
    containsSubstr raw.text "cir.const" &&
    containsSubstr raw.text "#cir.int<0>" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- Text-level exemption check for the N4b `move_acc` entry: nested
    `cleanup.scope` / `cleanup normal` regions (one per live `Acc`:
    `dst`'s scope nests inside `src`'s) closed by the unreachable
    `cir.trap`, with exactly the `move_acc` call multiset (1 default
    ctor + 1 move ctor + 2 `add` + 1 `get` + 2 dtors, 7 `cir.call`
    sites total) and no EH (`cir.try` / `personality` / `cleanup eh`)
    or heap. Same exemption role as `isAccTwoExemptText`; full
    admission additionally pins the signature (`isMoveAccShape`). -/
def isMoveAccExemptText (text : String) : Bool :=
  containsSubstr text "cir.cleanup.scope" &&
  containsSubstr text "cleanup normal" &&
  containsSubstr text "cir.trap" &&
  callsFunc text "_ZN3AccC2Ev" &&
  callsFunc text "_ZN3AccC2EOS_" &&
  callsFunc text "_ZN3Acc3addEi" &&
  callsFunc text "_ZNK3Acc3getEv" &&
  callsFunc text "_ZN3AccD2Ev" &&
  opCount text "cir.call @" == 7 &&
  opCount text "cir.call @_ZN3AccC2Ev(" == 1 &&
  opCount text "cir.call @_ZN3AccC2EOS_(" == 1 &&
  opCount text "cir.call @_ZN3Acc3addEi(" == 2 &&
  opCount text "cir.call @_ZNK3Acc3getEv(" == 1 &&
  opCount text "cir.call @_ZN3AccD2Ev(" == 2 &&
  !containsSubstr text "cir.try" &&
  !containsSubstr text "personality" &&
  !containsSubstr text "cleanup eh" &&
  !containsSubstr text "cir.call @malloc" &&
  !containsSubstr text "cir.call @free("

/-- The N4b `move_acc` entry: two by-value `i32`s, `i32` return, the
    exempt nested-`cleanup` / `trap` scope (see `isMoveAccExemptText`;
    the arithmetic lives in the callees, so no local `nsw` /
    `get_member`), no other control flow, heap, or indexing.
    Post-move reads of the source evaluate to the zeroed word in the
    model (the move ctor's `o.s = 0` store is threaded as an `assign`),
    so no textual no-read pin is needed. -/
def isMoveAccShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, b] =>
    noBreakContinueSwitch raw.text &&
    isI32 a.ctype && isI32 b.ctype && isI32 raw.ret &&
    isMoveAccExemptText raw.text &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- Text-level exemption check for the N4b `scope_early` entry: a
    `cleanup.scope` / `cleanup normal` region (the single local `Acc`)
    closed by the unreachable `cir.trap`, with exactly the
    `scope_early` call multiset (1 default ctor + 2 `add` + 2 `get` +
    1 dtor, 6 `cir.call` sites total), the early-return `cir.if` over
    `cir.cmp eq`, and no EH (`cir.try` / `personality` / `cleanup eh`)
    or heap. Same exemption role as `isAccTwoExemptText`; full
    admission additionally pins the signature (`isScopeEarlyShape`). -/
def isScopeEarlyExemptText (text : String) : Bool :=
  containsSubstr text "cir.cleanup.scope" &&
  containsSubstr text "cleanup normal" &&
  containsSubstr text "cir.trap" &&
  callsFunc text "_ZN3AccC2Ev" &&
  callsFunc text "_ZN3Acc3addEi" &&
  callsFunc text "_ZNK3Acc3getEv" &&
  callsFunc text "_ZN3AccD2Ev" &&
  opCount text "cir.call @" == 6 &&
  opCount text "cir.call @_ZN3AccC2Ev(" == 1 &&
  opCount text "cir.call @_ZN3Acc3addEi(" == 2 &&
  opCount text "cir.call @_ZNK3Acc3getEv(" == 2 &&
  opCount text "cir.call @_ZN3AccD2Ev(" == 1 &&
  !containsSubstr text "cir.try" &&
  !containsSubstr text "personality" &&
  !containsSubstr text "cleanup eh" &&
  !containsSubstr text "cir.call @malloc" &&
  !containsSubstr text "cir.call @free("

/-- The N4b `scope_early` entry: two by-value `i32`s, `i32` return,
    the exempt `cleanup` / `trap` scope (see
    `isScopeEarlyExemptText`), one `cir.cmp eq` + `cir.if`
    early-return inside the scope (the dtor runs on all paths in C++;
    both dtors are no-ops so the model returns directly), no local
    `nsw` / `get_member`, no other control flow, heap, or indexing. -/
def isScopeEarlyShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, b] =>
    noBreakContinueSwitch raw.text &&
    isI32 a.ctype && isI32 b.ctype && isI32 raw.ret &&
    isScopeEarlyExemptText raw.text &&
    containsSubstr raw.text "cir.cmp eq" &&
    containsSubstr raw.text "cir.if" &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The M2b entry: two by-value `i32`s, `i32` return, the exempt
    `cleanup` / `trap` scope (see `isAccTwoExemptText`; the arithmetic
    lives in the callees, so no local `nsw` / `get_member`), no other
    control flow, heap, or indexing. -/
def isAccTwoShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, b] =>
    noBreakContinueSwitch raw.text &&
    isI32 a.ctype && isI32 b.ctype && isI32 raw.ret &&
    isAccTwoExemptText raw.text &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-! ## M2c: `new` / `delete` as ownership ops (`box_through` entry) -/

/-- The M2c `Box` struct type: CIRGen's `!rec_Box` alias (long-form
    `!cir.struct<"Box" …>` also matches via the `"Box"` substring;
    applied to short type tokens only, never whole text). -/
def isBoxType (t : String) : Bool :=
  t == "!rec_Box" || containsSubstr t "Box"

/-- Text-level exemption check for the M2c entry: a `cleanup.scope` /
    `cleanup normal` region (the sized `delete` inside the null guard)
    with exactly the `box_through` call multiset (1 `new` + 1 sized
    `delete`, 2 `cir.call` sites total), the null guard (`cir.cmp ne`
    vs `#cir.ptr<null>` + `cir.if`), the 4-byte size const, bitcasts,
    and no EH (`cir.try` / `personality` / `cleanup eh`) or C heap.
    This is the `forbiddenOp` exemption gate (cf.
    `isAccTwoExemptText`); full admission additionally pins the
    signature (`isBoxThroughShape`). The leak variant (1 `new`, 0
    `delete`, no `cleanup`) needs no exemption: it has no `cir.cleanup`
    for the general gate to fire on. -/
def isBoxThroughExemptText (text : String) : Bool :=
  containsSubstr text "cir.cleanup.scope" &&
  containsSubstr text "cleanup normal" &&
  callsFunc text "_Znwm" &&
  callsFunc text "_ZdlPvm" &&
  containsSubstr text "cir.cmp ne" &&
  containsSubstr text "#cir.ptr<null>" &&
  containsSubstr text "cir.if" &&
  containsSubstr text "#cir.int<4>" &&
  containsSubstr text "bitcast" &&
  opCount text "cir.call @" == 2 &&
  newCallCount text == 1 &&
  deleteCallCount text == 1 &&
  !containsSubstr text "cir.try" &&
  !containsSubstr text "personality" &&
  !containsSubstr text "cleanup eh" &&
  !containsSubstr text "cir.call @malloc" &&
  !containsSubstr text "cir.call @free("

/-- The M2c entry: one by-value `i32`, `i32` return, `new Box{x}` (the
    4-byte `!u64i` size const + `cir.call @_Znwm` + bitcast + field
    store) + read (`cir.get_member` `x`) + at most one sized `delete`
    (M1d: leak is forgetting a value, sound — the 1-`new`/0-`delete`
    spelling validates to the same body; more `delete`s than `new`s is
    double-`delete`). The full spelling additionally pins the
    null-guarded `cleanup`-scoped delete (see
    `isBoxThroughExemptText`); the leak spelling has no `cleanup` /
    null guard. No other control flow, arithmetic, C heap, or
    indexing. -/
def isBoxThroughShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [x] =>
    noBreakContinueSwitch raw.text &&
    isI32 x.ctype && isI32 raw.ret &&
    callsFunc raw.text "_Znwm" &&
    newCallCount raw.text == 1 &&
    !(1 < deleteCallCount raw.text) &&
    opCount raw.text "cir.call @" == newCallCount raw.text + deleteCallCount raw.text &&
    containsSubstr raw.text "#cir.int<4>" &&
    containsSubstr raw.text "bitcast" &&
    containsSubstr raw.text "cir.get_member" &&
    containsSubstr raw.text "\"x\"" &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.try" &&
    !containsSubstr raw.text "personality" &&
    !containsSubstr raw.text "cleanup eh" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "realloc" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    (match deleteCallCount raw.text with
     | 1 =>
       containsSubstr raw.text "cir.cleanup.scope" &&
       containsSubstr raw.text "cleanup normal" &&
       containsSubstr raw.text "cir.cmp ne" &&
       containsSubstr raw.text "#cir.ptr<null>" &&
       containsSubstr raw.text "cir.if" &&
       !containsSubstr raw.text "cir.trap"
     | _ =>
       !containsSubstr raw.text "cir.cleanup" &&
       !containsSubstr raw.text "cir.trap")
  | _ => false

/-- First forbidden construct found (all `outOfSubset`), if any.
    `cir.cleanup` / `cir.trap` reject generally (C++ destructor /
    unreachable lowering); the exact M2b `acc_two` entry shape is
    exempt via `isAccTwoExemptText` and the exact M2c `box_through`
    entry shape via `isBoxThroughExemptText` (everything else stays
    loud). -/
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
  else if containsSubstr text "cir.cleanup" && !isAccTwoExemptText text && !isMoveAccExemptText text && !isScopeEarlyExemptText text && !isBoxThroughExemptText text then some "cleanup region (`cir.cleanup`: destructor / EH cleanup lowering — outside the v0.1 Ownable-C subset; admitted only in the exact M2b / N4b shapes, see docs/ROADMAP.md M2)"
  else if containsSubstr text "cir.trap" && !isAccTwoExemptText text && !isMoveAccExemptText text && !isScopeEarlyExemptText text then some "trap (`cir.trap`: unreachable terminator — outside the v0.1 Ownable-C subset; admitted only in the exact M2b / N4b shapes, see docs/ROADMAP.md M2)"
  else if containsSubstr text "cir.switch" && !isClsLowerableText text then some "`switch` (`cir.switch`: lower to an if-chain before CIR or it is rejected)"
  else if hasBareBr text then some "unstructured branch (`cir.br` from `goto`: no `goto` in v0.1; structured `cir.cond_br`/`cir.for` only)"
  else if containsSubstr text "bitfield" then some "bitfield (no bitfields in v0.1)"
  else if hasWrappingSignedArith text then some "signed wrapping arithmetic without `nsw` (signed overflow is UB in C: mark the op `nsw` or use unsigned arithmetic)"
  else none

/-! ## The gate -/

/-- The verified gate: `RawFunc` + oracle fact → admitted `Func`.
    Only the canonical shapes pass (`add`/`incr`/`choose`/`sum`,
    `vec_alloc`, `vec_alloc_u64` (M1b), `vec_realloc` (M1c), S1 DAG
    callers, S2 `translate`, M2a const-methods, M2b `Acc` ctor/add/get/
    dtor leaves + `acc_two` entry (the `cleanup`/`trap` exemption),
    N4b move-ctor leaf + `move_acc` entry (nested-`cleanup` exemption,
    source-zeroing `assign`),
    M2c `box_through` entry (the `cleanup`-scoped-delete exemption),
    S3a control flow, S3b 64-bit loop-free `add64`/`addu64`); everything
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
    match raw.params.find? (fun p =>
      isPtrType p.ctype && !p.noalias && !p.singleRef &&
      !isRecoveredParam raw p) with
    | some p =>
      reject raw.name .aliasReject
        s!"alias-reject: function '{raw.name}': param '{p.name}' has pointer type '{p.ctype}' without `__restrict__` (no `llvm.noalias`) or the full C++ single-reference triple (`nonnull + dereferenceable + noundef`): uniqueness cannot be established (see docs/SUBSET.md rule 1)"
    | none =>
      if !(oracleParams raw).isEmpty && !verdictAdmits oracle.verdict &&
          !recoveredNoalias raw then
        let why := match oracle.verdict with
          | .mayAlias => "reports `mayAlias`"
          | .unknown => "is inconclusive (`unknown`)"
          | .noalias => "is unreachable"
        reject raw.name .aliasReject
          s!"alias-reject: function '{raw.name}': oracle {why}: live pointer params require an explicit `noalias` verdict (see docs/OWNERSHIP.md)"
      else if 2 ≤ (oracleParams raw).length && !isChooseShape raw then
        reject raw.name .aliasReject
          s!"alias-reject: function '{raw.name}': {(oracleParams raw).length} live pointer parameters outside the borrow-return (`choose`) shape: a live writer may alias a live reader (writer+reader) and the pair cannot be discharged as read-only sharing — only the exact `choose` shape (one of two `noalias` inputs returned via `cir.ternary`) is admitted (see docs/SUBSET.md rules 2, 6; N2a admits no multi-reader `Func` yet)"
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
      else if isAdd3Shape raw then
        .ok { add3Func with name := raw.name }
      else if isOverloadCallerShape raw "_Z3addii" then
        .ok { useAddFunc with name := raw.name }
      else if isOverloadCallerShape raw "_ZN2ns3addEii" then
        .ok { useNsAddFunc with name := raw.name }
      else if callsOverloadWrongShape raw then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls a known overload leaf but not with an admitted (name, arity, single-site) shape: admitted callers are single-site 2-`i32` delegations into `_Z3addii` (`use_add` shape) and `_ZN2ns3addEii` (`use_ns_add` shape) only (known overload leaves `_Z3addii` / `_Z3addiii` / `_ZN2ns3addEii`; see docs/SUBSET.md)"
      else if isTranslateShape raw then
        .ok { translateFunc with name := raw.name }
      else if isMethodSumShape raw then
        .ok { methodSumFunc with name := raw.name }
      else if isPointSumRefShape raw then
        .ok { pointSumRefFunc with name := raw.name }
      else if isAccCtorShape raw then
        .ok { accCtorFunc with name := raw.name }
      else if isAccAddShape raw then
        .ok { accAddFunc with name := raw.name }
      else if isAccGetShape raw then
        .ok { accGetFunc with name := raw.name }
      else if isAccDtorShape raw then
        .ok { accDtorFunc with name := raw.name }
      else if isAccTwoShape raw then
        .ok { accTwoFunc with name := raw.name }
      else if isAccMoveCtorShape raw then
        .ok { accMoveCtorFunc with name := raw.name }
      else if isMoveAccShape raw then
        .ok { moveAccFunc with name := raw.name }
      else if isScopeEarlyShape raw then
        .ok { scopeEarlyFunc with name := raw.name }
      else if isBoxThroughShape raw then
        .ok { boxThroughFunc with name := raw.name }
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
      else if containsSubstr raw.text "alloca \"coerce\"" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' passes a struct by value (the `coerce` alloca + `bitcast` lowering): by-value struct params are deferred — pass by `const&` instead (M2a admits `const&` / `this` pointers only; see docs/ROADMAP.md M2)"
      else if callsFunc raw.text raw.name then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls itself (recursive call): S1 admits DAG calls into call-free leaves only (see docs/ROADMAP.md S1)"
      else if hasNonHeapCall raw.text &&
          !containsSubstr raw.text "realloc" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses function call outside the admitted call shapes (S1: calls into `add`/`sum_array` with the exact `add_caller`/`sum_caller` shapes only; N4a: single-site 2-`i32` calls into the known overload leaves `_Z3addii` / `_ZN2ns3addEii` only; M2b/N4b: the exact `Acc` leaf/entry call multisets only), outside the Ownable-C subset (see docs/SUBSET.md)"
      else if 1 < freeCallCount raw.text &&
          mallocCallCount raw.text < freeCallCount raw.text then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls `free` more times than `malloc`: double-`free` is rejected (heap blocks are freed at most once; leak is allowed, double-`free` is not, see docs/SUBSET.md rule 8)"
      else if newCallCount raw.text < deleteCallCount raw.text then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls sized `delete` more times than `new`: double-`delete` is rejected (heap boxes are deleted at most once; leak is allowed, double-`delete` is not, see docs/SUBSET.md rule 15)"
      else if isPtrType raw.ret &&
          (0 < freeCallCount raw.text || 0 < deleteCallCount raw.text) then
        reject raw.name .escapeReject
          s!"escape-reject: function '{raw.name}' frees a heap block and returns pointer type '{raw.ret}': the returned borrow may dangle (borrow-after-free) — return values, not pointers, after `free`/`delete` (see docs/SUBSET.md rules 6, 8)"
      else if containsSubstr raw.text "_Znwm" ||
          containsSubstr raw.text "_ZdlPvm" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses `new`/`delete` outside the admitted `box_through` shape (single `new` of a 4-byte `Box` + field read + at most one null-guarded `cleanup`-scoped sized `delete` (leak allowed, M1d); double-`delete` is rejected, see docs/ROADMAP.md M2c)"
      else if containsSubstr raw.text "realloc" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses `realloc` outside the admitted `vec_realloc` shape (single `malloc`, one `realloc` to `2*n`, at most one `free` (leak allowed, M1d), fill / fill-extension / sum discipline; `realloc(p, 0)` (= `free`) and `realloc(NULL, n)` (= `malloc`) spellings are rejected: use `free`/`malloc` directly, see docs/ROADMAP.md M1c)"
      else if containsSubstr raw.text "malloc" ||
          containsSubstr raw.text "cir.call @free(" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses heap allocation (`malloc`/`free`/`realloc`) outside the admitted `vec_alloc` / `vec_copy_sum` / `vec_alloc_u64` / `vec_realloc` shapes (see docs/ROADMAP.md)"
      else if isPtrType raw.ret && (oracleParams raw).isEmpty &&
          (raw.params.filter (fun p => isPtrType p.ctype)).isEmpty then
        reject raw.name .escapeReject
          s!"escape-reject: function '{raw.name}' returns pointer type '{raw.ret}' with no pointer inputs: an escaping borrow of a locally-created address cannot be returned (escaping-borrow) — borrow-return (`choose`) requires the return to be exactly one of the `noalias` inputs (see docs/SUBSET.md rule 6)"
      else if isPtrType raw.ret then
        reject raw.name .escapeReject
          s!"escape-reject: function '{raw.name}' returns pointer type '{raw.ret}' outside the borrow-return (`choose`) shape: the return must be exactly one of the `noalias` inputs (see docs/SUBSET.md rule 6)"
      else if containsSubstr raw.text "cir.ptr_stride" then
        reject raw.name .oobPossible
          s!"oob-possible: function '{raw.name}' indexes via `cir.ptr_stride` without the length-paired bound form (`(ptr, n)` params + `cir.for`): unbounded indexing cannot be functionalized (see docs/SUBSET.md rule 4)"
      else if containsSubstr raw.text "cir.get_member" then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' uses struct field access (`cir.get_member`) outside the admitted `translate` shape (S2: by-value `Point` + two `i32` deltas with `nsw` field adds only), the admitted M2a method shapes (M2a: single `this` / `const&` with the single-reference triple, `get_member` x/y + one `nsw` add in the leaf, exactly one mangled method call in the entry), the admitted M2b `Acc` leaf shapes (M2b: single `this` with the single-reference triple, `cxx_ctor` field-init / `add` one-`nsw`-add / `get` identity), and the admitted M2c `box_through` entry shape (M2c: `new` + `Box.x` field write/read + at most one sized `delete`; see docs/SUBSET.md)"
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

/-! ## Module validation (M2: multi-definition C++ files) -/

/-- Validate every *defined* function in one `.cir` file text.
    Declarations (`cir.func private @callee...` without a body) are
    skipped (S1 precedent: caller files carry callee declarations).
    A defined function without an oracle fact is a loud error — except
    functions with a C++ single-reference (`this` / `const&`) pointer
    param (M2a method/entry defs, M2b `Acc` leaf defs): their uniqueness
    comes from the `nonnull + dereferenceable + noundef` attrs in the
    CIR text itself, so they validate under a synthetic `unknown` fact.
    (The M2b int-only entry needs its fact, like every int-only func.) -/
def validateModule (text : String) (facts : List OracleFact) :
    List (String × Validation) :=
  match parseModule text with
  | none =>
    [("module", reject "module" .outOfSubset
      "out-of-subset: parse failed: no `cir.func` signature found")]
  | some ir => (ir.funcs.filter isFuncDef).map (fun raw =>
      match lookupOracle facts raw.name with
      | none =>
        if raw.params.any (fun p => isPtrType p.ctype && p.singleRef) then
          (raw.name, validate raw ⟨raw.name, .unknown⟩)
        else
          (raw.name, reject raw.name .outOfSubset
            s!"out-of-subset: function '{raw.name}' is defined but has no oracle fact (wiring error; refusing to translate)")
      | some fact => (raw.name, validate raw fact))

/-- End-to-end module pipeline: validate every defined function, emit
    each to file bytes. Errors are message strings; success pairs each
    function name with its emitted file text (compare with
    `tests/golden/`). -/
def runModulePipeline (text : String) (facts : List OracleFact) :
    Except String (List (String × String)) :=
  (validateModule text facts).mapM (fun (name, res) =>
    match res with
    | .error rej =>
      .error s!"{name}: [{(repr rej.code).pretty}] {rej.message}"
    | .ok f => .ok (name, emitFileText (emitFunc f)))

/-- `Option` projection (same rationale as `runPipelineOpt`: core Lean
    decides `Option` equality, but not `Except` equality). -/
def runModulePipelineOpt (text : String) (facts : List OracleFact) :
    Option (List (String × String)) :=
  (runModulePipeline text facts).toOption

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

/-- The checked-in `point_sum_ref` C++ module (real CIRGen output with
    `-fno-exceptions`: entry + method leaf, no oracle facts) validates
    and emits exactly the goldens, in file order. -/
example : runModulePipelineOpt (include_str "../tests/cir/point_sum_ref.cir") [] =
    some [("_Z13point_sum_refRK5Point",
      include_str "../tests/golden/PointSumRef.lean"),
      ("_ZNK5Point3sumEv",
      include_str "../tests/golden/MethodSum.lean")] := by native_decide



/-- The checked-in `acc_two` C++ module (real CIRGen output with
    `-fno-exceptions`: int-only entry + ctor/add/get/dtor leaves, one
    oracle fact for the entry) validates and emits exactly the goldens,
    in file order. -/
example : runModulePipelineOpt (include_str "../tests/cir/acc_two.cir")
    [⟨"_Z7acc_twoii", .unknown⟩] =
    some [("_Z7acc_twoii",
      include_str "../tests/golden/AccTwo.lean"),
      ("_ZN3AccC2Ev",
      include_str "../tests/golden/AccCtor.lean"),
      ("_ZN3Acc3addEi",
      include_str "../tests/golden/AccAdd.lean"),
      ("_ZNK3Acc3getEv",
      include_str "../tests/golden/AccGet.lean"),
      ("_ZN3AccD2Ev",
      include_str "../tests/golden/AccDtor.lean")] := by native_decide
