/-
Circe.Validator.Features — rejection codes, raw-text predicates
(`callsFunc`, `opCount`, …), and heap-plumbing predicates; shape
catalogs live in `Shapes` / `GrowLeaves`, the gate in `Gate`.
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

