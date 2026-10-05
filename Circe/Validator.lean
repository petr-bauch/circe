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
1b. N4d-iv-b2 composer pin (a text calling `_M_realloc_insert` /
   `emplace_back` / `push_back` is multi-call growth composition,
   deferred to b2 — actionable message before any other gate);
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
   recovers noalias from construction instead of attr text; N4d-iv-b1
   carve-out: borrowed erased-offset `int*`/`s8*`/`void*` params inside
   a pinned growth-leaf shape — `isVecGrowErasedParam` — need no
   uniqueness since the value model erases them to `u64` offsets or
   drops them), oracle
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
   `cleanup`/`trap` exemption), the N4d-iv-b1 growth-leaf shapes (with
   the dtor `cleanup`-only exemption — no `trap`), and by-value struct
   params stuck in the deferred `coerce` lowering).
-/
import Circe.CoreIR
import Circe.Parser
import Circe.Oracle
import Circe.Emit
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose

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

/-! ## N4c: template-instantiation shapes -/

/-- Known template-instantiation-leaf callees (mangled): the 32-bit and
    64-bit `tadd` monomorphs. Caller gates admit calls into the
    (name, arity) pairs named in `validate` below; this registry names
    every known instantiation for the wrong-shape rejection. Adding an
    instantiation extends the registry plus one gate arm — unknown
    mangled callees still reject. -/
def templateLeafCallees : List String :=
  ["_Z4taddIiET_S0_S0_", "_Z4taddIlET_S0_S0_"]

/-- Single-delegation caller into one known 64-bit instantiation leaf
    (the `isOverloadCallerShape` discipline at width 64: exactly one
    call site to `callee`, arithmetic lives in the callee so no local
    `nsw`, no self-call). -/
def isOverloadCaller64Shape (raw : RawFunc) (callee : String) : Bool :=
  match raw.params with
  | [x, y] =>
    noBreakContinueSwitch raw.text &&
    isI64 x.ctype && isI64 y.ctype && isI64 raw.ret &&
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

/-- Calls a known template-instantiation leaf but not with an admitted
    (name, arity, single-site) shape: dedicated rejection naming the
    admitted pairs. -/
def callsTemplateWrongShape (raw : RawFunc) : Bool :=
  templateLeafCallees.any (callsFunc raw.text)

/-! ## N4d-i: `std::array<int, 4>` read shapes -/

/-- The N4d-i `std::array<int32_t, 4>` object type (CIRGen's
    `!rec_std3A3Aarray3Cint2C_4UL3E` alias; the `4UL` extent is part of
    the admitted monomorph — each instantiation is its own shape, the
    N4c monomorphization precedent). -/
def isStdArray4Type (t : String) : Bool :=
  containsSubstr t "array" && containsSubstr t "4UL"

/-- The `_S_ref` unchecked-index leaf: single `const&` to the raw
    4-word `i32` array (`!cir.ptr<!cir.array<!s32i …>>`, truncated by
    the extractor at the first space — hence the prefix pin) with the
    single-reference triple, `u64` index, pointer-to-`i32` return, one
    `cir.get_element`, no calls, no arithmetic, no control flow. -/
def isArrayRefShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [t, n] =>
    noBreakContinueSwitch raw.text &&
    isPtrType t.ctype && t.singleRef &&
    isPrefixOfList "!cir.ptr<!cir.array<!s32i".toList t.ctype.toList &&
    isU64 n.ctype && !isPtrType n.ctype &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    containsSubstr raw.text "cir.get_element" &&
    !hasNonHeapCall raw.text &&
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

/-- The `operator[]` single-delegation entry: single `const&` to the
    `std::array<int, 4>` object with the single-reference triple,
    `u64` index, pointer-to-`i32` return, exactly one call site to the
    `_S_ref` leaf (the `_M_elems` projection + call are fused into the
    `idxi` read downstream, cf. `arrayAtFunc`), one `cir.get_member`,
    no local indexing or arithmetic. -/
def isArrayAtShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a, n] =>
    noBreakContinueSwitch raw.text &&
    isPtrType a.ctype && a.singleRef && isStdArray4Type a.ctype &&
    isU64 n.ctype && !isPtrType n.ctype &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    callsFunc raw.text arrayRefName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The `array_sum` 4-call entry: single `const&` to the
    `std::array<int, 4>` object with the single-reference triple,
    `i32` return, exactly four call sites to `operator[]` (const
    `u64` indices 0–3 functionalized as `let_`-bound words downstream,
    since `callRet` args are environment names), three threaded `nsw`
    adds over eight `cir.const` index spellings (4 `s32i` + 4 `u64i`),
    no projection/indexing ops of its own. -/
def isArraySumShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [a] =>
    noBreakContinueSwitch raw.text &&
    isPtrType a.ctype && a.singleRef && isStdArray4Type a.ctype &&
    isI32 raw.ret &&
    callsFunc raw.text arrayAtName &&
    opCount raw.text "cir.call @" == 4 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.add nsw" == 3 &&
    opCount raw.text "cir.const" == 8 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- Known `std::array` leaf callees (mangled): the `_S_ref`
    unchecked-index leaf and the `operator[]` delegation entry. Entry
    gates admit calls into the (name, arity, site-count) pairs named in
    `validate` below; this registry names every known array leaf for
    the wrong-shape rejection. -/
def arrayLeafCallees : List String :=
  [arrayRefName, arrayAtName]

/-- Calls a known `std::array` leaf but not with an admitted (name,
    arity, site-count) shape: dedicated rejection naming the admitted
    triples. -/
def callsArrayWrongShape (raw : RawFunc) : Bool :=
  arrayLeafCallees.any (callsFunc raw.text)

/-! ## N4d-ii: `std::optional<int32_t>` guarded-deref shapes -/

/-- The `std::optional<int>` object type (CIRGen's
    `!rec_std3A3Aoptional3Cint3E` alias; the `int` payload is part of
    the admitted monomorph — each instantiation is its own shape, the
    N4c monomorphization precedent). -/
def isStdOptionalIntType (t : String) : Bool :=
  containsSubstr t "rec_std3A3Aoptional3Cint3E"

/-- The `_Optional_base_impl<int, …>` inner type (the `_M_is_engaged`
    / impl `_M_get` receiver). -/
def isOptBaseImplType (t : String) : Bool :=
  containsSubstr t "_Optional_base_impl"

/-- The `_Optional_payload_base<int>` inner type (the payload
    `_M_get` receiver). -/
def isOptPayloadBaseType (t : String) : Bool :=
  containsSubstr t "_Optional_payload_base"

/-- The `_M_is_engaged` engaged-bit leaf: single `const&` to the
    base-impl object with the single-reference triple, `bool` return,
    the `derived [0]` + `get_member [0]` (`_M_payload`) + `base [0]`
    + `get_member [1]` (`_M_engaged`) projection chain with the bit
    load, no calls, no control flow. -/
def isOptHasShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with
     | some inner => isOptBaseImplType inner
     | none => false) &&
    isBoolType raw.ret &&
    opCount raw.text "cir.get_member" == 2 &&
    containsSubstr raw.text "_M_engaged" &&
    containsSubstr raw.text "_M_payload" &&
    opCount raw.text "cir.derived_class_addr" == 1 &&
    opCount raw.text "cir.base_class_addr" == 1 &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The payload `_M_get` leaf: single `const&` to the payload-base
    object with the single-reference triple, pointer-to-`i32` return,
    the `get_member [0]` (`_M_payload`) + `get_member [1]`
    (`_M_value`) projection pair (no class-addr steps: the receiver
    already is the payload base), no calls, no control flow. -/
def isOptGetShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with
     | some inner => isOptPayloadBaseType inner
     | none => false) &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    opCount raw.text "cir.get_member" == 2 &&
    containsSubstr raw.text "_M_payload" &&
    containsSubstr raw.text "_M_value" &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The `has_value` single-delegation entry: single `const&` to the
    `std::optional<int>` object with the single-reference triple,
    `bool` return, exactly one call site to the `_M_is_engaged` leaf
    (the `base_class_addr [0]` projection is fused into the `optHas`
    read downstream, cf. `optHasValueFunc`), no local projections. -/
def isOptHasValueShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [o] =>
    noBreakContinueSwitch raw.text &&
    isPtrType o.ctype && o.singleRef && isStdOptionalIntType o.ctype &&
    isBoolType raw.ret &&
    callsFunc raw.text optHasName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.base_class_addr" == 1 &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The impl `_M_get` delegation entry: single `const&` to the
    base-impl object with the single-reference triple,
    pointer-to-`i32` return, exactly two call sites — the live
    payload-`_M_get` call plus the `_M_is_engaged` call in the dead
    assert arm — with the dead disabled-`__glibcxx_assert` skeleton
    pinned exactly (single `cir.ternary` over three `#false` consts,
    one-sided `cir.if`, `cir.unreachable`, `cir.do`/`cir.condition`;
    a live-assert variant rejects loudly). The dead scope is dropped
    downstream (cf. `optImplGetFunc`). -/
def isOptImplGetShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [o] =>
    noBreakContinueSwitch raw.text &&
    isPtrType o.ctype && o.singleRef &&
    (match ptrInner o.ctype with
     | some inner => isOptBaseImplType inner
     | none => false) &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    callsFunc raw.text optGetName &&
    callsFunc raw.text optHasName &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.ternary" == 1 &&
    opCount raw.text "cir.if" == 1 &&
    containsSubstr raw.text "cir.unreachable" &&
    containsSubstr raw.text "cir.do" &&
    containsSubstr raw.text "cir.condition" &&
    opCount raw.text "cir.const" == 3 &&
    containsSubstr raw.text "cir.const #false" &&
    !containsSubstr raw.text "cir.const #cir.int" &&
    opCount raw.text "cir.get_member" == 1 &&
    containsSubstr raw.text "_M_payload" &&
    opCount raw.text "cir.derived_class_addr" == 1 &&
    opCount raw.text "cir.base_class_addr" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The `operator*` fused leaf: single `const&` to the
    `std::optional<int>` object with the single-reference triple,
    pointer-to-`i32` return, exactly one call site to impl `_M_get`
    (the `base_class_addr [0]` projection, the impl→payload edge,
    and the caller-side load are all fused into the `optGet` read
    downstream, cf. `optDerefOpFunc`), no local projections. -/
def isOptDerefOpShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [o] =>
    noBreakContinueSwitch raw.text &&
    isPtrType o.ctype && o.singleRef && isStdOptionalIntType o.ctype &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    callsFunc raw.text optImplGetName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.base_class_addr" == 1 &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The `opt_deref` guarded-deref entry: single `const&` to the
    `std::optional<int>` object with the single-reference triple,
    `i32` return, exactly two call sites (`has_value` for the guard,
    `operator*` for the engaged word), the one-sided `cir.if` with
    the deref inside, two `cir.const` (the live `-1` sentinel plus
    the stray dead `1`, dropped downstream), no projections of its
    own. -/
def isOptDerefShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [o] =>
    noBreakContinueSwitch raw.text &&
    isPtrType o.ctype && o.singleRef && isStdOptionalIntType o.ctype &&
    isI32 raw.ret &&
    callsFunc raw.text optHasValueName &&
    callsFunc raw.text optDerefOpName &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.if" == 1 &&
    opCount raw.text "cir.const" == 2 &&
    containsSubstr raw.text "#cir.int<-1>" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- Known `std::optional<int32_t>` leaf callees (mangled): the
    `_M_is_engaged` engaged-bit leaf, the payload `_M_get` leaf, the
    impl `_M_get` delegation entry, the `has_value` delegation entry,
    and the fused `operator*` leaf. Entry gates admit calls into the
    (name, arity, site-count) pairs named in `validate` below; this
    registry names every known optional leaf for the wrong-shape
    rejection. -/
def optLeafCallees : List String :=
  [optHasName, optGetName, optImplGetName, optHasValueName, optDerefOpName]

/-- Calls a known `std::optional` leaf but not with an admitted
    (name, arity, site-count) shape: dedicated rejection naming the
    admitted shapes. -/
def callsOptWrongShape (raw : RawFunc) : Bool :=
  optLeafCallees.any (callsFunc raw.text)

/-! ## N4d-iii: `std::span<const int32_t>` index-sum shapes -/

/-- The `std::span<const int, …>` object type (CIRGen's
    `!rec_std3A3Aspan…` alias; the element type and dynamic extent
    are part of the admitted monomorph — each instantiation is its
    own shape, the N4c monomorphization precedent). -/
def isStdSpanType (t : String) : Bool :=
  containsSubstr t "rec_std3A3Aspan"

/-- The `__extent_storage<…>` inner type (the `_M_extent` receiver). -/
def isSpanExtentStorageType (t : String) : Bool :=
  containsSubstr t "__extent_storage"

/-- The `_M_extent` extent leaf: single `const&` to the
    extent-storage object with the single-reference triple, `u64`
    return, the single `get_member [0]` (`_M_extent_value`)
    projection with the value load, no calls, no control flow. -/
def isSpanExtentShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef &&
    (match ptrInner this.ctype with
     | some inner => isSpanExtentStorageType inner
     | none => false) &&
    isU64 raw.ret &&
    opCount raw.text "cir.get_member" == 1 &&
    containsSubstr raw.text "_M_extent_value" &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The `size` single-delegation entry: single `const&` to the
    `std::span` object with the single-reference triple, `u64`
    return, exactly one call site to the `_M_extent` leaf (the
    `get_member [1]` (`_M_extent`) projection is fused into the
    `spanLen` read downstream, cf. `spanSizeFunc`), no local
    control flow. -/
def isSpanSizeShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [s] =>
    noBreakContinueSwitch raw.text &&
    isPtrType s.ctype && s.singleRef && isStdSpanType s.ctype &&
    isU64 raw.ret &&
    callsFunc raw.text spanExtentName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.get_member" == 1 &&
    containsSubstr raw.text "_M_extent" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.base_class_addr"
  | _ => false

/-- The `operator[]` fused leaf: the span `const&` (with the
    single-reference triple) plus the `u64` index, pointer-to-`i32`
    return, exactly one call site — the live `size()` call in the
    dead assert arm — with the dead disabled-assert skeleton pinned
    exactly (single `cir.ternary` over three `#false` consts, one
    `cir.cmp lt`, one `cir.not`, one-sided `cir.if`,
    `cir.unreachable`, `cir.do`/`cir.condition`; a variant with the
    assert enabled, or without it, rejects loudly). The live tail
    (`get_member [0]` (`_M_ptr`) + `ptr_stride` + both loads) is
    fused into the `spanAt` read downstream
    (cf. `spanIndexFunc`). -/
def isSpanIndexShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this, idx] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef && isStdSpanType this.ctype &&
    isU64 idx.ctype &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    callsFunc raw.text spanSizeName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.ternary" == 1 &&
    opCount raw.text "cir.cmp" == 1 &&
    containsSubstr raw.text "cir.cmp lt" &&
    opCount raw.text "cir.not" == 1 &&
    opCount raw.text "cir.if" == 1 &&
    containsSubstr raw.text "cir.unreachable" &&
    containsSubstr raw.text "cir.do" &&
    containsSubstr raw.text "cir.condition" &&
    opCount raw.text "cir.const" == 3 &&
    containsSubstr raw.text "cir.const #false" &&
    !containsSubstr raw.text "cir.const #cir.int" &&
    opCount raw.text "cir.get_member" == 1 &&
    containsSubstr raw.text "_M_ptr" &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.base_class_addr"
  | _ => false

/-- The `span_sum` index-loop entry: the span **by value** (no
    pointer, no aliasing question on the object itself — the viewed
    words are a `sharedBorrow` snapshot downstream), `i32` return,
    exactly two call sites (`size` in `cond`, `operator[]` in
    `body`), the single `cir.for` with the `lt` comparison, the
    `u64` increment, and the one `nsw` accumulation add. Three
    `cir.const` (the two live `0` inits plus one stray dead `i32`
    `0`, the clang init quirk — dropped downstream, cf. the N4d-ii
    stray `const 1`), no projections of its own. -/
def isSpanSumShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [s] =>
    noBreakContinueSwitch raw.text &&
    !isPtrType s.ctype && isStdSpanType s.ctype &&
    isI32 raw.ret &&
    callsFunc raw.text spanSizeName &&
    callsFunc raw.text spanIndexName &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.for" == 1 &&
    opCount raw.text "cir.cmp" == 1 &&
    containsSubstr raw.text "cir.cmp lt" &&
    opCount raw.text "cir.inc" == 1 &&
    opCount raw.text "cir.add nsw" == 1 &&
    opCount raw.text "cir.const" == 3 &&
    containsSubstr raw.text "#cir.int<0>" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- Known `std::span<const int32_t>` leaf callees (mangled): the
    `_M_extent` extent leaf, the `size` delegation entry, and the
    fused `operator[]` leaf. Entry gates admit calls into the
    (name, arity, site-count) pairs named in `validate` below; this
    registry names every known span leaf for the wrong-shape
    rejection. -/
def spanLeafCallees : List String :=
  [spanExtentName, spanSizeName, spanIndexName]

/-- Calls a known `std::span` leaf but not with an admitted (name,
    arity, site-count) shape: dedicated rejection naming the
    admitted shapes. -/
def callsSpanWrongShape (raw : RawFunc) : Bool :=
  spanLeafCallees.any (callsFunc raw.text)

/-- The `std::vector<int32_t>` object type (the `_M_start` /
    `_M_finish` / `_M_end_of_storage` triple). -/
def isStdVectorType (t : String) : Bool :=
  containsSubstr t "rec_std3A3Avector"

/-- The `size` projection leaf: single `const&` to the vector object
    with the single-reference triple, `u64` return, no calls at all,
    the double `_M_impl` projection pair (`_M_finish` + `_M_start`
    loads) with exactly one `ptr_diff` and one integral `cast`
    (`s64 → u64`), no control flow. -/
def isStdVecSizeShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [s] =>
    noBreakContinueSwitch raw.text &&
    isPtrType s.ctype && s.singleRef && isStdVectorType s.ctype &&
    isU64 raw.ret &&
    opCount raw.text "cir.call @" == 0 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.base_class_addr" == 4 &&
    opCount raw.text "cir.get_member" == 4 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_finish" &&
    containsSubstr raw.text "_M_start" &&
    opCount raw.text "cir.ptr_diff" == 1 &&
    containsSubstr raw.text "cir.cast integral" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.derived_class_addr"
  | _ => false

/-- The `operator[]` fused leaf: the vector `const&` (with the
    single-reference triple) plus the `u64` index, pointer-to-`i32`
    return, no calls at all (no assert skeleton — unchecked indexing
    is UB, so the model reports `OOB`), the pure projection chain
    (`base [0]` + `get_member [0]` (`_M_impl`) + `base [0]` +
    `get_member [0]` (`_M_start`) + both loads + one `ptr_stride`).
    Any const/cmp/branch beside the chain rejects. -/
def isStdVecIndexShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this, idx] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef && isStdVectorType this.ctype &&
    isU64 idx.ctype &&
    (match ptrInner raw.ret with | some inner => isI32 inner | none => false) &&
    opCount raw.text "cir.call @" == 0 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.base_class_addr" == 2 &&
    opCount raw.text "cir.get_member" == 2 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_start" &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ptr_diff" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.derived_class_addr"
  | _ => false

/-- The `vec_read_sum` index-loop entry: single `const&` to the
    vector object with the single-reference triple (unlike span's
    by-value entry — the vector cannot pass by value without a copy
    ctor, so the triple carries uniqueness like every M2a
    single-reference param), `i32` return, exactly two call sites
    (`size` in `cond`, `operator[]` in `body`), the single `cir.for`
    with the `lt` comparison, the `u64` increment, and the one `nsw`
    accumulation add. Three `cir.const` (the two live `0` inits plus
    one stray dead `i32` `0`, the clang init quirk — dropped
    downstream), no projections of its own. -/
def isStdVecReadSumShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [s] =>
    noBreakContinueSwitch raw.text &&
    isPtrType s.ctype && s.singleRef && isStdVectorType s.ctype &&
    isI32 raw.ret &&
    callsFunc raw.text stdVecSizeName &&
    callsFunc raw.text stdVecIndexName &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.for" == 1 &&
    opCount raw.text "cir.cmp" == 1 &&
    containsSubstr raw.text "cir.cmp lt" &&
    opCount raw.text "cir.inc" == 1 &&
    opCount raw.text "cir.add nsw" == 1 &&
    opCount raw.text "cir.const" == 3 &&
    containsSubstr raw.text "#cir.int<0>" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.get_element" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.derived_class_addr" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-! ## N4d-iv-b1: `std::vector<int>` growth leaves (no composition) -/

/-- Exact-ctype single-reference param (the C++ `this` / `const&` /
    allocator-ref triple on a pinned pointee; `isStdVectorType` covers
    the vector object, these cover the base/impl/allocator/iterator
    family whose rec names nest and must not prefix-match). -/
def isVecGrowRef (want : String) (p : RawParam) : Bool :=
  isPtrType p.ctype && p.singleRef && p.ctype == want

/-- Borrowed erased-offset param: noundef-only `int*` / `s8*` / `void*`
    (no triple, no `noalias`). The b1 value model erases these to `u64`
    offsets (or drops them: the `check_len` message, the `allocate`
    hint, the freed pointer via null-iff-`cap == 0`), so they need no
    uniqueness evidence — see `isVecGrowErasedParam`. -/
def isErasedIntPtr (p : RawParam) : Bool :=
  (p.ctype == "!cir.ptr<!s32i>" || p.ctype == "!cir.ptr<!s8i>" ||
    p.ctype == "!cir.ptr<!void>") && !p.singleRef && !p.noalias

/-- By-value iterator param (N4d-iv-b2): the exact
    `__normal_iterator<int*, vector<int>>` record alias, passed by
    value with neither the single-reference triple nor `noalias`
    (the risk noted in the b2 plan). The value model erases it to a
    `u64` offset (the wrapped pointer), so it needs no uniqueness
    evidence — cf. `isErasedIntPtr`, which covers only pointer
    spellings, never record spellings. Any other record alias (or the
    same alias with uniqueness attrs) fails loudly. -/
def isVecGrowIterParam (p : RawParam) : Bool :=
  p.ctype ==
    "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
  !p.singleRef && !p.noalias

/-- N4d-iv-b2 composer anchor: the `_M_realloc_insert` name (own
    signature or a call site), a call into `emplace_back`, or a call
    into `push_back`. No b1 leaf calls these (checked against the
    corpus inventories), so any text hitting this is multi-call growth
    composition — deferred to N4d-iv-b2. Checked before `forbiddenOp`
    so composers get the actionable b2 message rather than the generic
    cleanup/call message. -/
def isVecGrowComposerText (text : String) : Bool :=
  containsSubstr text "_M_realloc_insert" ||
  callsFunc text "_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_" ||
  callsFunc text "_ZNSt6vectorIiSaIiEE9push_backEOi"

/-- N4d-iv-b1 dtor `cleanup` exemption: the four `cir.cleanup.scope`
    (with `cleanup normal`, no `cir.trap`) destructor bodies whose
    exact call multisets fuse to the dtor/consume model
    (`vector-D2`: getTp + base-D2 + destroy range; `base-D2`: impl-D2
    + deallocate; `impl-D2`: allocator-D2; `allocator-D2`:
    new-allocator-D2). This is the `forbiddenOp` exemption gate (cf.
    `isAccTwoExemptText`); full admission additionally pins the
    signature (`isStdVecDtorShape` / `isStdVecUnitShape`). The b2 entry
    (`cir.trap`) and non-`scope` cleanups are not exempt. -/
def isVecDtorExemptText (text : String) : Bool :=
  containsSubstr text "cir.cleanup.scope" &&
  containsSubstr text "cleanup normal" &&
  !containsSubstr text "cir.trap" &&
  (opCount text "cir.call @" == 3 &&
    callsFunc text stdVecGetTpName &&
    callsFunc text stdVecBaseDtorName &&
    callsFunc text stdVecDestroyName ||
  opCount text "cir.call @" == 2 &&
    callsFunc text stdVecImplDtorName &&
    callsFunc text stdVecDeallocName ||
  opCount text "cir.call @" == 1 &&
    (callsFunc text stdVecAllocDtorName ||
     callsFunc text stdVecNewAllocDtorName))

/-- Known `std::vector<int32_t>` leaf callees (mangled): the `size`
    projection leaf and the fused `operator[]` leaf (N4d-iv-a), plus
    every N4d-iv-b1 growth leaf (the ctor/dtor/consume/max/iterator/
    allocate/deallocate/construct/relocate family). Entry gates
    admit calls into the (name, arity, site-count) pairs named in
    `validate` below; this registry names every known vector leaf
    for the wrong-shape rejection. -/
def stdVecLeafCallees : List String :=
  [stdVecSizeName, stdVecIndexName,
   stdVecCtorName, stdVecBaseCtorName, stdVecImplCtorName,
   stdVecImplDataCtorName, stdVecNewAllocCtorName, stdVecAllocCtorName,
   stdVecDtorName, stdVecBaseDtorName, stdVecImplDtorName,
   stdVecAllocDtorName, stdVecNewAllocDtorName,
   stdVecDestroyName, stdVecDestroy2Name, stdVecDestroyAuxName,
   stdVecTraitsDestroyName, stdVecNewAllocDestroyName,
   stdVecGetTpName, stdVecGetTpConstName,
   stdVecMMaxSizeName, stdVecSMaxSizeName, stdVecMaxSizeName,
   stdVecNewAllocMaxSizeName, stdVecTraitsMaxSizeName,
   stdVecMaxName, stdVecMinName, stdVecCheckLenName,
   stdVecBeginName, stdVecEndName, stdVecBackName,
   stdVecIterCtorName, stdVecNIterBaseName, stdVecIterBaseName,
   stdVecIterDerefName, stdVecMinusElName, stdVecMinusName,
   stdVecAllocateName, stdVecTraitsAllocName, stdVecNewAllocName,
   stdVecDeallocName, stdVecTraitsDeallocName, stdVecNewDeallocName,
   stdVecTraitsConstructName, stdVecNewConstructName,
   stdVecRelocName, stdVecDoRelocName, stdVecRelocAName,
   stdVecRelocA1Name]

/-- Calls a known `std::vector` leaf but not with an admitted (name,
    arity, site-count) shape: dedicated rejection naming the
    admitted shapes. -/
def callsStdVecWrongShape (raw : RawFunc) : Bool :=
  stdVecLeafCallees.any (callsFunc raw.text)

/-- The default-ctor chain: `vector-C2` (single delegation into
    `base-C2`), `base-C2` (into `impl-C2` over `_M_impl`),
    `impl-C2` (into the allocator ctor + impl-data ctor), and
    `impl-data-C2` (call-free: the three null field stores). All fuse
    to the empty triple (`stdVecEmptyCtorFunc`). -/
def isStdVecEmptyCtorShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this] =>
    raw.ret == "" &&
    (isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
      callsFunc raw.text stdVecBaseCtorName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 1 &&
      !containsSubstr raw.text "cir.get_member" ||
    isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
      callsFunc raw.text stdVecImplCtorName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.get_member" == 1 &&
      containsSubstr raw.text "_M_impl" ||
    isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E3A3A_Vector_impl>"
      this &&
      callsFunc raw.text stdVecAllocCtorName &&
      callsFunc raw.text stdVecImplDataCtorName &&
      opCount raw.text "cir.call @" == 2 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 2 ||
    isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E3A3A_Vector_impl_data>"
      this &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 3 &&
      opCount raw.text "cir.const" == 3) &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.cleanup"
  | _ => false

/-- The empty-effect leaves: the allocator ctors (each a single
    delegation into the next, or call-free) and the inner dtors
    (`impl-D2` into the allocator dtor, `allocator-D2` into the
    new-allocator dtor — both under fused `cleanup` scopes — and the
    call-free new-allocator dtor / ctor, which share one variant).
    All fuse to nothing (`stdVecUnitFunc`, void as `i32 0`). -/
def isStdVecUnitShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  !containsSubstr raw.text "cir.trap" &&
  match raw.params with
  | [this] =>
    raw.ret == "" &&
    (isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" this &&
      callsFunc raw.text stdVecNewAllocCtorName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 1 &&
      !containsSubstr raw.text "cir.cleanup" ||
    isVecGrowRef "!cir.ptr<!rec___gnu_cxx3A3Anew_allocator3Cint3E>" this &&
      opCount raw.text "cir.call @" == 0 &&
      !containsSubstr raw.text "cir.cleanup" &&
      !containsSubstr raw.text "cir.get_member" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" ||
    isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E3A3A_Vector_impl>"
      this &&
      containsSubstr raw.text "cir.cleanup.scope" &&
      containsSubstr raw.text "cleanup normal" &&
      callsFunc raw.text stdVecAllocDtorName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name ||
    isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" this &&
      containsSubstr raw.text "cir.cleanup.scope" &&
      containsSubstr raw.text "cleanup normal" &&
      callsFunc raw.text stdVecNewAllocDtorName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name) &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for"
  | _ => false

/-- The destructors: `vector-D2` (getTp + base-D2 + destroy range
    under one fused `cleanup` scope) and `base-D2` (impl-D2 +
    deallocate with the computed size, likewise scoped). Both fuse to
    the `0 < cap`-guarded consume (`stdVecDtorFunc`, triple
    threading for b2). -/
def isStdVecDtorShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  containsSubstr raw.text "cir.cleanup.scope" &&
  containsSubstr raw.text "cleanup normal" &&
  !containsSubstr raw.text "cir.trap" &&
  match raw.params with
  | [this] =>
    raw.ret == "" &&
    (isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
      callsFunc raw.text stdVecGetTpName &&
      callsFunc raw.text stdVecBaseDtorName &&
      callsFunc raw.text stdVecDestroyName &&
      opCount raw.text "cir.call @" == 3 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.get_member" == 4 &&
      opCount raw.text "cir.base_class_addr" == 6 &&
      !containsSubstr raw.text "cir.cast" &&
      !containsSubstr raw.text "cir.ptr_diff" ||
    isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
      callsFunc raw.text stdVecImplDtorName &&
      callsFunc raw.text stdVecDeallocName &&
      opCount raw.text "cir.call @" == 2 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.get_member" == 7 &&
      opCount raw.text "cir.cast" == 1 &&
      opCount raw.text "cir.ptr_diff" == 1) &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.for"
  | _ => false

/-- The destroy range: the 3-arg `_Destroy` (into the 2-arg one), the
    2-arg `_Destroy` (into `_Destroy_aux`), and `_Destroy_aux`
    (call-free twin stores — the trivial-`int` no-op). All take
    erased `u64` offsets (`stdVecDestroyNoopFunc`). -/
def isStdVecDestroyNoopShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [a, b, al] =>
    raw.ret == "" && isErasedIntPtr a && isErasedIntPtr b &&
    isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" al &&
    callsFunc raw.text stdVecDestroy2Name &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free("
  | [a, b] =>
    raw.ret == "" && isErasedIntPtr a && isErasedIntPtr b &&
    (callsFunc raw.text stdVecDestroyAuxName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name ||
    opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.store" == 2) &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for"
  | _ => false

/-- Element destroy: `traits::destroy` (into the new-allocator one)
    and `new_allocator::destroy` (call-free — no-op for `int`). The
    allocator ref drops, the offset stays (`stdVecDestroyPtrFunc`). -/
def isStdVecDestroyPtrShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [al, p] =>
    raw.ret == "" && isErasedIntPtr p &&
    (isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" al &&
      callsFunc raw.text stdVecNewAllocDestroyName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 1 ||
    isVecGrowRef "!cir.ptr<!rec___gnu_cxx3A3Anew_allocator3Cint3E>" al &&
      opCount raw.text "cir.call @" == 0 &&
      !containsSubstr raw.text "cir.get_member" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if") &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for"
  | _ => false

/-- The allocator projection: both `_M_get_Tp_allocator` overloads
    (call-free single `_M_impl` member access fusing to the erased
    allocator, `i32 0`) → `stdVecGetTpFunc`. -/
def isStdVecGetTpShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    raw.ret == "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" &&
    opCount raw.text "cir.call @" == 0 &&
    opCount raw.text "cir.get_member" == 1 &&
    containsSubstr raw.text "_M_impl" &&
    opCount raw.text "cir.base_class_addr" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- The max-size chain: `_M_max_size` (call-free `S64_MAX / 4` div),
    the two pure delegations into it, and the `min(diffmax, allocmax)`
    chain (`_S_max_size` with the pinned `diffmax` const, `max_size`
    over getTp). All five fold to `maxDiff`
    (`stdVecDiffMaxFunc`). -/
def isStdVecDiffMaxShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  isU64 raw.ret &&
  !containsSubstr raw.text "cir.call @malloc" &&
  !containsSubstr raw.text "cir.call @free(" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.for" &&
  match raw.params with
  | [p] =>
    (isVecGrowRef "!cir.ptr<!rec___gnu_cxx3A3Anew_allocator3Cint3E>" p &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.div" == 1 &&
      opCount raw.text "cir.const" == 3 &&
      containsSubstr raw.text "9223372036854775807" ||
    isVecGrowRef "!cir.ptr<!rec___gnu_cxx3A3Anew_allocator3Cint3E>" p &&
      callsFunc raw.text stdVecMMaxSizeName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name ||
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>" p &&
      (callsFunc raw.text stdVecGetTpName ||
        callsFunc raw.text stdVecGetTpConstName) &&
      callsFunc raw.text stdVecSMaxSizeName &&
      opCount raw.text "cir.call @" == 2 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 1 ||
    isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" p &&
      callsFunc raw.text stdVecNewAllocMaxSizeName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 1 ||
    isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" p &&
      callsFunc raw.text stdVecTraitsMaxSizeName &&
      callsFunc raw.text stdVecMinName &&
      opCount raw.text "cir.call @" == 2 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.const" == 1 &&
      containsSubstr raw.text "2305843009213693951")
  | _ => false

/-- `std::max` over `u64`: the early-return-`if` form (`a < b`
    then `b` else `a`, references loaded through the `__a`/`__b`
    allocas). The operand order is the only max/min difference, so the
    first comparison load is pinned (`%5` from the `__a` alloca `%0`;
    CIRGen emission order — like every site-count pin, exact). -/
def isStdVecMaxShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [a, b] =>
    isVecGrowRef "!cir.ptr<!u64i>" a && isVecGrowRef "!cir.ptr<!u64i>" b &&
    raw.ret == "!cir.ptr<!u64i>" &&
    opCount raw.text "cir.call @" == 0 &&
    opCount raw.text "cir.if" == 1 &&
    opCount raw.text "cir.cmp" == 1 &&
    containsSubstr raw.text "cir.cmp lt" &&
    containsSubstr raw.text "%5 = cir.load %0" &&
    opCount raw.text "cir.load" == 8 &&
    opCount raw.text "cir.store" == 4 &&
    opCount raw.text "cir.return" == 2 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- `std::min` over `u64`: the mirror image (`b < a` then `b` else
    `a`; the comparison loads `__b` first — see `isStdVecMaxShape`). -/
def isStdVecMinShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [a, b] =>
    isVecGrowRef "!cir.ptr<!u64i>" a && isVecGrowRef "!cir.ptr<!u64i>" b &&
    raw.ret == "!cir.ptr<!u64i>" &&
    opCount raw.text "cir.call @" == 0 &&
    opCount raw.text "cir.if" == 1 &&
    opCount raw.text "cir.cmp" == 1 &&
    containsSubstr raw.text "cir.cmp lt" &&
    containsSubstr raw.text "%5 = cir.load %1" &&
    !containsSubstr raw.text "%5 = cir.load %0" &&
    opCount raw.text "cir.load" == 8 &&
    opCount raw.text "cir.store" == 4 &&
    opCount raw.text "cir.return" == 2 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member"
  | _ => false

/-- `_M_check_len`: the `length_error` throw (fused to `fail`), the
    `size`/`max_size`/`max` call multisets, the wrapping `sub`, both
    `cir.ternary`, the single `if`. The `s8` message param is unused
    (dropped downstream; erased-param carve-out at the alias gate). -/
def isStdVecCheckLenShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this, n, msg] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isU64 n.ctype && !isPtrType n.ctype &&
    isErasedIntPtr msg &&
    isU64 raw.ret &&
    callsFunc raw.text stdVecSizeName &&
    opCount raw.text ("cir.call @" ++ stdVecSizeName ++ "(") == 4 &&
    callsFunc raw.text stdVecMaxSizeName &&
    opCount raw.text ("cir.call @" ++ stdVecMaxSizeName ++ "(") == 3 &&
    callsFunc raw.text stdVecMaxName &&
    opCount raw.text ("cir.call @" ++ stdVecMaxName ++ "(") == 1 &&
    callsFunc raw.text "_ZSt20__throw_length_errorPKc" &&
    opCount raw.text "cir.call @" == 9 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.if" == 1 &&
    opCount raw.text "cir.ternary" == 2 &&
    opCount raw.text "cir.cmp" == 3 &&
    opCount raw.text "cir.sub" == 1 &&
    opCount raw.text "cir.const" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- `begin` / `end`: the `_M_start` / `_M_finish` load fused with
    the single iterator-ctor call (offsets `0` / `len`). The loaded
    field is the only begin/end difference. -/
def isStdVecBeginShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
    callsFunc raw.text stdVecIterCtorName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.get_member" == 2 &&
    opCount raw.text "cir.base_class_addr" == 2 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_start" &&
    !containsSubstr raw.text "_M_finish" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- `end`: the `_M_finish` twin of `begin`. -/
def isStdVecEndShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
    callsFunc raw.text stdVecIterCtorName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.get_member" == 2 &&
    opCount raw.text "cir.base_class_addr" == 2 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_finish" &&
    !containsSubstr raw.text "_M_start" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- `back`: the `end` / `miEl` / `deref` chain fusing to `len - 1`
    (wrapping `usub`; empty is UB) → `stdVecBackFunc`. -/
def isStdVecBackShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    raw.ret == "!cir.ptr<!s32i>" &&
    callsFunc raw.text stdVecEndName &&
    callsFunc raw.text stdVecMinusElName &&
    callsFunc raw.text stdVecIterDerefName &&
    opCount raw.text "cir.call @" == 3 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.const" == 2 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- The iterator identities: `iterator-C2` (stores the pointed-to
    pointer into `_M_current`), `__niter_base` (call-free identity),
    `base` (the address-of-field collapsing to the value), and
    `operator*` (the stored pointer is the offset). All erase to the
    `u64` identity (`stdVecIterIdFunc`). -/
def isStdVecIterIdShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  !containsSubstr raw.text "cir.call @malloc" &&
  !containsSubstr raw.text "cir.call @free(" &&
  !containsSubstr raw.text "cir.const" &&
  !containsSubstr raw.text "cir.cmp" &&
  !containsSubstr raw.text "cir.if" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.for" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.ptr_diff" &&
  match raw.params with
  | [this, pp] =>
    raw.ret == "" &&
    isVecGrowRef
      "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
      this &&
    isVecGrowRef "!cir.ptr<!cir.ptr<!s32i>>" pp &&
    opCount raw.text "cir.call @" == 0 &&
    opCount raw.text "cir.get_member" == 1 &&
    containsSubstr raw.text "_M_current"
  | [p] =>
    (isErasedIntPtr p && raw.ret == "!cir.ptr<!s32i>" &&
      opCount raw.text "cir.call @" == 0 &&
      !containsSubstr raw.text "cir.get_member") ||
    (isVecGrowRef
      "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
      p &&
      (raw.ret == "!cir.ptr<!cir.ptr<!s32i>>" ||
       raw.ret == "!cir.ptr<!s32i>") &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 1 &&
      containsSubstr raw.text "_M_current")
  | _ => false

/-- `miEl`: `cir.minus` + `ptr_stride` fuse to wrapping `usub` (the
    `s64` step arrives as the same bits) → `stdVecMinusElFunc`. -/
def isStdVecMinusElShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [it, n] =>
    isVecGrowRef
      "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
      it &&
    isI64 n.ctype && !isPtrType n.ctype &&
    raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
    callsFunc raw.text stdVecIterCtorName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.get_member" == 1 &&
    opCount raw.text "cir.minus" == 1 &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- `mi`: the double `base` + `ptr_diff` fuse to bit-exact `s64diff`
    → `stdVecMinusFunc`. -/
def isStdVecMinusShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [a, b] =>
    isVecGrowRef
      "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
      a &&
    isVecGrowRef
      "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
      b &&
    isI64 raw.ret &&
    callsFunc raw.text stdVecIterBaseName &&
    opCount raw.text ("cir.call @" ++ stdVecIterBaseName ++ "(") == 2 &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.ptr_diff" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The allocate chain: `_M_allocate` (the `n != 0` ternary kept),
    `traits::allocate` (single delegation), and
    `new_allocator::allocate` (the `n > maxDiff` throw pair, the dead
    aligned-new skeleton, operator `new` as fresh storage). The
    `this` / allocator-ref / hint params drop; `n` stays
    (`stdVecAllocFunc`). -/
def isStdVecAllocShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  raw.ret == "!cir.ptr<!s32i>" &&
  !containsSubstr raw.text "cir.call @malloc" &&
  !containsSubstr raw.text "cir.call @free(" &&
  !containsSubstr raw.text "cir.for" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.ptr_diff" &&
  match raw.params with
  | [this, n] =>
    isU64 n.ctype && !isPtrType n.ctype &&
    (isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
      callsFunc raw.text stdVecTraitsAllocName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.ternary" == 1 &&
      opCount raw.text "cir.cmp" == 1 &&
      containsSubstr raw.text "cir.cmp ne" &&
      opCount raw.text "cir.const" == 3 ||
    isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" this &&
      callsFunc raw.text stdVecNewAllocName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.const" == 1 &&
      opCount raw.text "cir.base_class_addr" == 1 &&
      !containsSubstr raw.text "cir.ternary" &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if")
  | [this, n, hint] =>
    isVecGrowRef "!cir.ptr<!rec___gnu_cxx3A3Anew_allocator3Cint3E>" this &&
    isU64 n.ctype && !isPtrType n.ctype &&
    isErasedIntPtr hint &&
    callsFunc raw.text stdVecMMaxSizeName &&
    callsFunc raw.text "_ZSt28__throw_bad_array_new_lengthv" &&
    callsFunc raw.text "_ZSt17__throw_bad_allocv" &&
    callsFunc raw.text "_Znwm" &&
    containsSubstr raw.text "_ZnwmSt11align_val_t" &&
    opCount raw.text "cir.call @" == 5 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.if" == 3 &&
    opCount raw.text "cir.cmp" == 3 &&
    opCount raw.text "cir.const" == 9 &&
    opCount raw.text "cir.mul" == 2 &&
    opCount raw.text "cir.div" == 1 &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for"
  | _ => false

/-- The unconditional consume: `traits::deallocate` (single
    delegation) and `new_allocator::deallocate` (the dead `4 > 16`
    aligned-delete skeleton drops, both deletes consume). The
    allocator ref and freed pointer drop (null-iff-`cap == 0`)
    (`stdVecDeallocFunc`). -/
def isStdVecDeallocShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [al, p, n] =>
    raw.ret == "" && isErasedIntPtr p &&
    isU64 n.ctype && !isPtrType n.ctype &&
    (isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" al &&
      callsFunc raw.text stdVecNewDeallocName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 1 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" ||
    isVecGrowRef "!cir.ptr<!rec___gnu_cxx3A3Anew_allocator3Cint3E>" al &&
      callsFunc raw.text "_ZdlPvm" &&
      containsSubstr raw.text "_ZdlPvmSt11align_val_t" &&
      opCount raw.text "cir.call @" == 2 &&
      opCount raw.text "cir.if" == 1 &&
      opCount raw.text "cir.cmp" == 1 &&
      containsSubstr raw.text "cir.cmp gt" &&
      opCount raw.text "cir.const" == 5 &&
      containsSubstr raw.text "#cir.int<16>" &&
      opCount raw.text "cir.cast" == 2 &&
      opCount raw.text "cir.mul" == 2 &&
      opCount raw.text "cir.return" == 2) &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- `_M_deallocate`: the `ptr_to_bool` guard kept as the `n == 0`
    test around the unconditional consume (sound by the call-site
    invariant that a null `p` pairs with `n == 0`)
    (`stdVecDeallocGuardFunc`). -/
def isStdVecDeallocGuardShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this, p, n] =>
    raw.ret == "" &&
    isVecGrowRef
      "!cir.ptr<!rec_std3A3A_Vector_base3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isErasedIntPtr p &&
    isU64 n.ctype && !isPtrType n.ctype &&
    callsFunc raw.text stdVecTraitsDeallocName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.if" == 1 &&
    opCount raw.text "cir.get_member" == 1 &&
    opCount raw.text "cir.cast" == 1 &&
    opCount raw.text "cir.base_class_addr" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- The construct chain: `traits::construct` (single delegation) and
    `new_allocator::construct` (call-free placement store with the
    `&&`-arg double load). The allocator ref drops; the triple, the
    offset, and the `i32` word stay (`stdVecConstructFunc`, returning
    the updated triple for b2). -/
def isStdVecConstructShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [al, p, v] =>
    raw.ret == "" && isErasedIntPtr p &&
    isVecGrowRef "!cir.ptr<!s32i>" v &&
    (isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" al &&
      callsFunc raw.text stdVecNewConstructName &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.base_class_addr" == 1 ||
    isVecGrowRef "!cir.ptr<!rec___gnu_cxx3A3Anew_allocator3Cint3E>" al &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.const" == 1 &&
      opCount raw.text "cir.cast" == 2) &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- The relocate chain: `_S_relocate` (into `_S_do_relocate`),
    `_S_do_relocate` (into `__relocate_a`, dropping the
    `integral_constant` tag), `__relocate_a` (three `__niter_base`
    projections into `__relocate_a_1`), and `__relocate_a_1` (the
    `count > 0`-guarded `memmove`, unrolled to the copy loop). All
    take erased offsets and fuse to the copy loop
    (`stdVecRelocFunc`; the `result + count` return drops — b2
    recomputes the offset). -/
def isStdVecRelocShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  raw.ret == "!cir.ptr<!s32i>" &&
  !containsSubstr raw.text "cir.call @malloc" &&
  !containsSubstr raw.text "cir.call @free(" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.for" &&
  !containsSubstr raw.text "cir.get_member" &&
  match raw.params with
  | [a, b, c, al] =>
    isErasedIntPtr a && isErasedIntPtr b && isErasedIntPtr c &&
    isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" al &&
    !callsFunc raw.text raw.name &&
    (callsFunc raw.text stdVecDoRelocName &&
      opCount raw.text "cir.call @" == 1 &&
      !containsSubstr raw.text "cir.cast" &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.ptr_stride" &&
      !containsSubstr raw.text "cir.ptr_diff" ||
    callsFunc raw.text stdVecNIterBaseName &&
      opCount raw.text ("cir.call @" ++ stdVecNIterBaseName ++ "(") == 3 &&
      callsFunc raw.text stdVecRelocA1Name &&
      opCount raw.text "cir.call @" == 4 &&
      !containsSubstr raw.text "cir.cast" &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.ptr_stride" &&
      !containsSubstr raw.text "cir.ptr_diff" ||
    callsFunc raw.text "memmove" &&
      opCount raw.text "cir.call @" == 1 &&
      opCount raw.text "cir.cmp" == 1 &&
      opCount raw.text "cir.if" == 1 &&
      opCount raw.text "cir.const" == 3 &&
      opCount raw.text "cir.ptr_stride" == 1 &&
      opCount raw.text "cir.ptr_diff" == 1 &&
      opCount raw.text "cir.cast" == 3)
  | [a, b, c, al, tag] =>
    isErasedIntPtr a && isErasedIntPtr b && isErasedIntPtr c &&
    isVecGrowRef "!cir.ptr<!rec_std3A3Aallocator3Cint3E>" al &&
    !isPtrType tag.ctype &&
    tag.ctype == "!rec_std3A3Aintegral_constant3Cbool2C_true3E" &&
    callsFunc raw.text stdVecRelocAName &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- `_M_realloc_insert` (N4d-iv-b2): the 16-site growth composition
    (`check_len` + `begin` + `mi` + `allocate` + `construct`-at-`k` +
    two `_S_relocate`s + the cap-counted `deallocate`, with the
    const-folded live `cir.if #true` arm and the const-folded dead
    destroy/deallocate `cir.if #false` arm). The fused `Func`
    (`stdVecGrowReallocFunc`) keeps all eight leaf calls
    (`begin`/`mi` included — the position stays absolute until the
    `mi` call) and drops only provably-dead code: the `getTp`
    allocator tokens (no b1 callee takes one), the `base` pointer
    projections (the erased `u64` iterator param carries the offset),
    the `.str` message and `s8` hint (unused), the `array_to_ptrdecay`
    cast, the dead `cir.if #false` arm (pinned here, never executed),
    and the header pointer stores (the fresh triple already carries
    the buffer and capacity — see `vgrowSetLen`). The dead-arm
    destroy/`Destroy`/deallocate calls are pinned by exact site
    counts below (1 each), so a live destroy would fail loudly. -/
def isStdVecReallocInsertShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  raw.ret == "" &&
  containsSubstr raw.text "cir.const #true" &&
  containsSubstr raw.text "cir.const #false" &&
  match raw.params with
  | [this, pos, x] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowIterParam pos &&
    isVecGrowRef "!cir.ptr<!s32i>" x &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecCheckLenName &&
    opCount raw.text ("cir.call @" ++ stdVecCheckLenName ++ "(") == 1 &&
    callsFunc raw.text stdVecBeginName &&
    opCount raw.text ("cir.call @" ++ stdVecBeginName ++ "(") == 1 &&
    callsFunc raw.text stdVecMinusName &&
    opCount raw.text ("cir.call @" ++ stdVecMinusName ++ "(") == 1 &&
    callsFunc raw.text stdVecAllocateName &&
    opCount raw.text ("cir.call @" ++ stdVecAllocateName ++ "(") == 1 &&
    callsFunc raw.text stdVecTraitsConstructName &&
    opCount raw.text
      ("cir.call @" ++ stdVecTraitsConstructName ++ "(") == 1 &&
    callsFunc raw.text stdVecRelocName &&
    opCount raw.text ("cir.call @" ++ stdVecRelocName ++ "(") == 2 &&
    callsFunc raw.text stdVecDeallocName &&
    opCount raw.text ("cir.call @" ++ stdVecDeallocName ++ "(") == 2 &&
    callsFunc raw.text stdVecGetTpName &&
    opCount raw.text ("cir.call @" ++ stdVecGetTpName ++ "(") == 3 &&
    callsFunc raw.text stdVecIterBaseName &&
    opCount raw.text ("cir.call @" ++ stdVecIterBaseName ++ "(") == 2 &&
    callsFunc raw.text stdVecTraitsDestroyName &&
    opCount raw.text
      ("cir.call @" ++ stdVecTraitsDestroyName ++ "(") == 1 &&
    callsFunc raw.text stdVecDestroyName &&
    opCount raw.text ("cir.call @" ++ stdVecDestroyName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 16 &&
    opCount raw.text "cir.if" == 3 &&
    opCount raw.text "cir.const" == 6 &&
    opCount raw.text "cir.scope" == 5 &&
    opCount raw.text "cir.ptr_stride" == 4 &&
    opCount raw.text "cir.ptr_diff" == 1 &&
    opCount raw.text "cir.cast" == 4 &&
    opCount raw.text "cir.get_member" == 14 &&
    opCount raw.text "cir.base_class_addr" == 22 &&
    opCount raw.text "cir.get_global" == 1 &&
    opCount raw.text "cir.return" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.trap" &&
    !containsSubstr raw.text "cir.cleanup"
  | _ => false

/-- `emplace_back` (N4d-iv-b2): the guard (`_M_finish` /
    `_M_end_of_storage` loads + raw-pointer `cmp ne` + `cir.if`)
    with the fast `traits::construct` + finish-bump (`ptr_stride`)
    arm, the slow `end()` + `_M_realloc_insert` arm, and the shared
    `back()` tail. The fused `Func` (`stdVecEmplaceBackFunc`) keeps
    the finish/end loads as `len` / `cap` lets with a `.une`
    dispatch, the four leaf/composer calls by name, and drops only
    the fused-away material: the member projections, the `__args` /
    iterator allocas, and the `back()` + `__retval` tail (the C++
    reference functionalizes as triple threading — cf.
    `stdVecEmplaceBackFunc`). Exact site counts below pin the shape;
    anything else fails loudly. -/
def isStdVecEmplaceBackShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  raw.ret == "!cir.ptr<!s32i>" &&
  match raw.params with
  | [this, x] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowRef "!cir.ptr<!s32i>" x &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecTraitsConstructName &&
    opCount raw.text
      ("cir.call @" ++ stdVecTraitsConstructName ++ "(") == 1 &&
    callsFunc raw.text stdVecEndName &&
    opCount raw.text ("cir.call @" ++ stdVecEndName ++ "(") == 1 &&
    callsFunc raw.text stdVecGrowReallocName &&
    opCount raw.text ("cir.call @" ++ stdVecGrowReallocName ++ "(") == 1 &&
    callsFunc raw.text stdVecBackName &&
    opCount raw.text ("cir.call @" ++ stdVecBackName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 4 &&
    opCount raw.text "cir.alloca" == 4 &&
    opCount raw.text "cir.store" == 5 &&
    opCount raw.text "cir.load" == 9 &&
    opCount raw.text "cir.const" == 1 &&
    opCount raw.text "cir.cmp" == 1 &&
    opCount raw.text "cir.if" == 1 &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.scope" == 1 &&
    opCount raw.text "cir.get_member" == 9 &&
    opCount raw.text "cir.base_class_addr" == 10 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ptr_diff" &&
    !containsSubstr raw.text "cir.trap" &&
    !containsSubstr raw.text "cir.cleanup"
  | _ => false

/-- N4d-iv-b2 `push_back` forwarder shape: the 8-site corpus def
    (`this` / `__x` spill+reload fused to the direct params, one
    `emplace_back` call whose reference result is discarded before
    the void return). -/
def isStdVecPushBackShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  raw.ret == "" &&
  match raw.params with
  | [this, x] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowRef "!cir.ptr<!s32i>" x &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecEmplaceBackName &&
    opCount raw.text ("cir.call @" ++ stdVecEmplaceBackName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 1 &&
    opCount raw.text "cir.alloca" == 2 &&
    opCount raw.text "cir.store" == 2 &&
    opCount raw.text "cir.load" == 2 &&
    opCount raw.text "cir.return" == 1 &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.scope" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ptr_diff" &&
    !containsSubstr raw.text "cir.trap" &&
    !containsSubstr raw.text "cir.cleanup"
  | _ => false

/-- Any N4d-iv-b1 growth-leaf shape (disjunction for the alias-gate
    carve-outs: a func matching one of these has exactly the pinned
    params, so the erased-offset params need no uniqueness). -/
def isVecGrowShape (raw : RawFunc) : Bool :=
  isStdVecEmptyCtorShape raw || isStdVecUnitShape raw ||
  isStdVecDtorShape raw || isStdVecDestroyNoopShape raw ||
  isStdVecDestroyPtrShape raw || isStdVecGetTpShape raw ||
  isStdVecDiffMaxShape raw || isStdVecMaxShape raw ||
  isStdVecMinShape raw || isStdVecCheckLenShape raw ||
  isStdVecBeginShape raw || isStdVecEndShape raw ||
  isStdVecBackShape raw || isStdVecIterIdShape raw ||
  isStdVecMinusElShape raw || isStdVecMinusShape raw ||
  isStdVecAllocShape raw || isStdVecDeallocShape raw ||
  isStdVecDeallocGuardShape raw || isStdVecConstructShape raw ||
  isStdVecRelocShape raw

/-- A param whose missing `llvm.noalias` needs no recovery: a borrowed
    erased-offset pointer inside a pinned b1 shape (cf.
    `isRecoveredParam`: same carve-out role, value-model erasure
    instead of reader recovery). -/
def isVecGrowErasedParam (raw : RawFunc) (p : RawParam) : Bool :=
  isVecGrowShape raw && isErasedIntPtr p

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
  else if containsSubstr text "cir.cleanup" && !isAccTwoExemptText text && !isMoveAccExemptText text && !isScopeEarlyExemptText text && !isBoxThroughExemptText text && !isVecDtorExemptText text then some "cleanup region (`cir.cleanup`: destructor / EH cleanup lowering — outside the v0.1 Ownable-C subset; admitted only in the exact M2b / N4b / N4d-iv-b1-dtor shapes, see docs/ROADMAP.md M2)"
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
  else if isStdVecReallocInsertShape raw then
    .ok { stdVecGrowReallocFunc with name := raw.name }
  else if isStdVecEmplaceBackShape raw then
    .ok { stdVecEmplaceBackFunc with name := raw.name }
  else if isStdVecPushBackShape raw then
    .ok { stdVecPushBackFunc with name := raw.name }
  else if isVecGrowComposerText raw.text then
    reject raw.name .outOfSubset
      s!"out-of-subset: function '{raw.name}' is an N4d-iv-b2 growth composer (the `vec_push_sum` entry over the admitted `push_back` forwarder: multi-call growth composition — checked length, fresh storage, value relocation): growth leaves and composers validate in N4d-iv-b1/N4d-iv-b2, the entry is deferred (see docs/ROADMAP.md N4d-iv-b)"
  else match forbiddenOp raw.text with
  | some what =>
    reject raw.name .outOfSubset
      s!"out-of-subset: function '{raw.name}' uses {what}, outside the v0.1 Ownable-C subset (see docs/CIR_SUBSET.md)"
  | none =>
    match raw.params.find? (fun p =>
      isPtrType p.ctype && !p.noalias && !p.singleRef &&
      !isRecoveredParam raw p && !isVecGrowErasedParam raw p) with
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
      else if 2 ≤ (oracleParams raw).length && !isChooseShape raw &&
          !isVecGrowShape raw then
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
      else if isOverloadCallerShape raw "_Z4taddIiET_S0_S0_" then
        .ok { useTadd32Func with name := raw.name }
      else if isOverloadCaller64Shape raw "_Z4taddIlET_S0_S0_" then
        .ok { useTadd64Func with name := raw.name }
      else if callsTemplateWrongShape raw then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls a known template-instantiation leaf but not with an admitted (name, arity, single-site) shape: admitted callers are single-site 2-`i32` delegations into `_Z4taddIiET_S0_S0_` (`use_tadd32` shape) and single-site 2-`i64` delegations into `_Z4taddIlET_S0_S0_` (`use_tadd64` shape) only (known instantiation leaves `_Z4taddIiET_S0_S0_` / `_Z4taddIlET_S0_S0_`; see docs/SUBSET.md)"
      else if isArrayRefShape raw then
        .ok { arrayRefFunc with name := raw.name }
      else if isArrayAtShape raw then
        .ok { arrayAtFunc with name := raw.name }
      else if isArraySumShape raw then
        .ok { arraySumFunc with name := raw.name }
      else if callsArrayWrongShape raw then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls a known `std::array` leaf but not with an admitted (name, arity, site-count) shape: admitted callers are the single-site `operator[]` delegation into `{arrayRefName}` (`array_at` shape) and the 4-site `array_sum` entry into `{arrayAtName}` (`array_sum` shape) only (known array leaves `{arrayRefName}` / `{arrayAtName}`; see docs/SUBSET.md)"
      else if isOptHasShape raw then
        .ok { optHasFunc with name := raw.name }
      else if isOptGetShape raw then
        .ok { optGetFunc with name := raw.name }
      else if isOptHasValueShape raw then
        .ok { optHasValueFunc with name := raw.name }
      else if isOptImplGetShape raw then
        .ok { optImplGetFunc with name := raw.name }
      else if isOptDerefOpShape raw then
        .ok { optDerefOpFunc with name := raw.name }
      else if isOptDerefShape raw then
        .ok { optDerefFunc with name := raw.name }
      else if callsOptWrongShape raw then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls a known `std::optional` leaf but not with an admitted (name, arity, site-count) shape: admitted shapes are the `_M_is_engaged` engaged-bit leaf (`opt_has`), the payload `_M_get` leaf (`opt_get`), the single-site `has_value` delegation (`opt_has_value`), the impl `_M_get` delegation with the dead assert skeleton (`opt_impl_get`), the single-site `operator*` fused leaf (`opt_deref_op`), and the 2-site `opt_deref` guarded entry (`opt_deref`) only (known optional leaves `{optHasName}` / `{optGetName}` / `{optImplGetName}` / `{optHasValueName}` / `{optDerefOpName}`; see docs/SUBSET.md)"
      else if isSpanExtentShape raw then
        .ok { spanExtentFunc with name := raw.name }
      else if isSpanSizeShape raw then
        .ok { spanSizeFunc with name := raw.name }
      else if isSpanIndexShape raw then
        .ok { spanIndexFunc with name := raw.name }
      else if isSpanSumShape raw then
        .ok { spanSumFunc with name := raw.name }
      else if callsSpanWrongShape raw then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls a known `std::span` leaf but not with an admitted (name, arity, site-count) shape: admitted shapes are the `_M_extent` extent leaf (`span_extent`), the single-site `size` delegation (`span_size`), the single-site `operator[]` fused leaf with the dead assert skeleton (`span_index`), and the 2-site `span_sum` index-loop entry (`span_sum`) only (known span leaves `{spanExtentName}` / `{spanSizeName}` / `{spanIndexName}`; see docs/SUBSET.md)"
      else if isStdVecSizeShape raw then
        .ok { stdVecSizeFunc with name := raw.name }
      else if isStdVecIndexShape raw then
        .ok { stdVecIndexFunc with name := raw.name }
      else if isStdVecReadSumShape raw then
        .ok { stdVecReadSumFunc with name := raw.name }
      else if isStdVecEmptyCtorShape raw then
        .ok { stdVecEmptyCtorFunc with name := raw.name }
      else if isStdVecUnitShape raw then
        .ok { stdVecUnitFunc with name := raw.name }
      else if isStdVecDtorShape raw then
        .ok { stdVecDtorFunc with name := raw.name }
      else if isStdVecDestroyNoopShape raw then
        .ok { stdVecDestroyNoopFunc with name := raw.name }
      else if isStdVecDestroyPtrShape raw then
        .ok { stdVecDestroyPtrFunc with name := raw.name }
      else if isStdVecGetTpShape raw then
        .ok { stdVecGetTpFunc with name := raw.name }
      else if isStdVecDiffMaxShape raw then
        .ok { stdVecDiffMaxFunc with name := raw.name }
      else if isStdVecMaxShape raw then
        .ok { stdVecMaxFunc with name := raw.name }
      else if isStdVecMinShape raw then
        .ok { stdVecMinFunc with name := raw.name }
      else if isStdVecCheckLenShape raw then
        .ok { stdVecCheckLenFunc with name := raw.name }
      else if isStdVecBeginShape raw then
        .ok { stdVecBeginFunc with name := raw.name }
      else if isStdVecEndShape raw then
        .ok { stdVecEndFunc with name := raw.name }
      else if isStdVecBackShape raw then
        .ok { stdVecBackFunc with name := raw.name }
      else if isStdVecIterIdShape raw then
        .ok { stdVecIterIdFunc with name := raw.name }
      else if isStdVecMinusElShape raw then
        .ok { stdVecMinusElFunc with name := raw.name }
      else if isStdVecMinusShape raw then
        .ok { stdVecMinusFunc with name := raw.name }
      else if isStdVecAllocShape raw then
        .ok { stdVecAllocFunc with name := raw.name }
      else if isStdVecDeallocShape raw then
        .ok { stdVecDeallocFunc with name := raw.name }
      else if isStdVecDeallocGuardShape raw then
        .ok { stdVecDeallocGuardFunc with name := raw.name }
      else if isStdVecConstructShape raw then
        .ok { stdVecConstructFunc with name := raw.name }
      else if isStdVecRelocShape raw then
        .ok { stdVecRelocFunc with name := raw.name }
      else if callsStdVecWrongShape raw then
        reject raw.name .outOfSubset
          s!"out-of-subset: function '{raw.name}' calls a known `std::vector` leaf but not with an admitted (name, arity, site-count) shape: admitted shapes are the `size` projection leaf (`vec_size`), the call-free `operator[]` fused leaf (`vec_index`), the 2-site `vec_read_sum` index-loop entry (`vec_read_sum`), and the N4d-iv-b1 growth leaves (ctor chain `vec_empty_ctor`, empty-effect `vec_unit`, dtor `vec_dtor`, destroy `vec_destroy_noop` / `vec_destroy_ptr`, allocator projection `vec_get_tp`, max-size `vec_diffmax`, `vec_max` / `vec_min`, `vec_check_len`, `vec_begin` / `vec_end` / `vec_back`, iterator identities `vec_iter_id`, `vec_minus_el` / `vec_minus`, allocate `vec_alloc`, deallocate `vec_dealloc` / `vec_dealloc_guard`, construct `vec_construct`, relocate `vec_reloc`) only (known vector leaves `{stdVecSizeName}` / `{stdVecIndexName}` + the b1 registry; see docs/SUBSET.md)"
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
          s!"out-of-subset: function '{raw.name}' uses function call outside the admitted call shapes (S1: calls into `add`/`sum_array` with the exact `add_caller`/`sum_caller` shapes only; N4a: single-site 2-`i32` calls into the known overload leaves `_Z3addii` / `_ZN2ns3addEii` only; N4c: single-site 2-`i32` / 2-`i64` calls into the known template-instantiation leaves `_Z4taddIiET_S0_S0_` / `_Z4taddIlET_S0_S0_` only; N4d-i: the single-site `operator[]` call into the `_S_ref` leaf and the 4-site `array_sum` entry into `operator[]` only; M2b/N4b: the exact `Acc` leaf/entry call multisets only), outside the Ownable-C subset (see docs/SUBSET.md)"
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
          s!"out-of-subset: function '{raw.name}' uses struct field access (`cir.get_member`) outside the admitted `translate` shape (S2: by-value `Point` + two `i32` deltas with `nsw` field adds only), the admitted M2a method shapes (M2a: single `this` / `const&` with the single-reference triple, `get_member` x/y + one `nsw` add in the leaf, exactly one mangled method call in the entry), the admitted M2b `Acc` leaf shapes (M2b: single `this` with the single-reference triple, `cxx_ctor` field-init / `add` one-`nsw`-add / `get` identity), the admitted N4d-i `operator[]` shape (N4d-i: single `const&` to `std::array<int, 4>` with the single-reference triple, one `_M_elems` `get_member` + exactly one call into the `_S_ref` leaf), and the admitted M2c `box_through` entry shape (M2c: `new` + `Box.x` field write/read + at most one sized `delete`; see docs/SUBSET.md)"
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
