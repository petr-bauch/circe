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

/-- Arithmetic-op count for single-op leaf exactness (N6a): a leaf gate
    admits exactly one arithmetic op — a two-op function (e.g.
    `(a + b) + (a * b)`) must not validate to a single-op `Func`
    (in-subset divergence is P0). Covers the CIR integer arithmetic
    vocabulary (`cir.inc`/`cir.dec` are loop-step ops elsewhere, but a
    leaf containing one is not a single-op leaf). -/
def arithOpCount (text : String) : Nat :=
  opCount text "cir.add" + opCount text "cir.sub" +
  opCount text "cir.mul" + opCount text "cir.div" +
  opCount text "cir.rem" + opCount text "cir.minus" +
  opCount text "cir.inc" + opCount text "cir.dec" +
  opCount text "cir.shift" + opCount text "cir.and " +
  opCount text "cir.or " + opCount text "cir.xor "

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
    arithOpCount raw.text == 1 &&
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
    arithOpCount raw.text == 1 &&
    !hasNonHeapCall raw.text &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while"
  | _ => false

/-- Leaf skeleton shared by the arithmetic catalog (N6a-iii): the same
    control/call exclusions as the single-op leaf gates. -/
def arithLeafSkeleton (text : String) : Bool :=
  noBreakContinueSwitch text &&
  !hasNonHeapCall text &&
  !containsSubstr text "cir.ternary" &&
  !containsSubstr text "cir.for" &&
  !containsSubstr text "cir.if" &&
  !containsSubstr text "cir.while" &&
  !containsSubstr text "cir.cond_br" &&
  !containsSubstr text "cir.ptr_stride" &&
  !containsSubstr text "cir.get_member" &&
  !containsSubstr text "malloc" &&
  !containsSubstr text "realloc" &&
  !containsSubstr text "cir.call @free(" &&
  !containsSubstr text "_Znwm" &&
  !containsSubstr text "_ZdlPvm"

/-- Width/sign class of an int type (uniformity check below keeps
    width-mixed signatures on their existing routing). -/
def intClass (t : String) : Nat :=
  if isI32 t then 0 else if isU32 t then 1
  else if isI64 t then 2 else if isU64 t then 3 else 4

/-- Unadmitted arithmetic leaf (N6a-iii): leaf-shaped (one/two by-value
    int params of one width/sign class, same-class int return, leaf
    skeleton) with arithmetic ops, but not an admitted single-op leaf —
    multi-op bodies, unsigned div/rem, signed sub/mul, shifts, bitwise
    ops. Runs after every admission, so no exemptions are needed. -/
def isUnadmittedArithLeaf (raw : RawFunc) : Bool :=
  let intParam := fun (p : RawParam) =>
    !isPtrType p.ctype &&
    (isI32 p.ctype || isU32 p.ctype || isI64 p.ctype || isU64 p.ctype)
  let intRet := isI32 raw.ret || isU32 raw.ret || isI64 raw.ret || isU64 raw.ret
  let leaf := intRet && arithLeafSkeleton raw.text &&
    !callsFunc raw.text raw.name && 1 ≤ arithOpCount raw.text
  match raw.params with
  | [x] => intParam x && leaf && intClass x.ctype == intClass raw.ret
  | [a, b] => intParam a && intParam b && leaf &&
    intClass a.ctype == intClass b.ctype && intClass a.ctype == intClass raw.ret
  | _ => false

/-- Cause phrase for unadmitted arithmetic (N6a-iii): multi-op bodies
    first, then per-op spellings. -/
def arithRejectWhy (text : String) : String :=
  let lines := text.splitOn "\n"
  let hasOp := fun (op : String) =>
    lines.any (fun line => containsSubstr line op)
  let hasTyped := fun (op : String) (tys : List String) =>
    lines.any (fun line => containsSubstr line op &&
      tys.any (containsSubstr line ·))
  let unsignedTys := ["!u32i", "!u64i", "<u, 32>", "<u,32>", "<u, 64>", "<u,64>"]
  if 2 ≤ arithOpCount text then
    s!"combines {arithOpCount text} arithmetic ops in one function — single-op leaves admit exactly one (`add`/`incr`/`add64`/`addu64`/`neg`/`sdiv`/`xor_u32`/`and_u32`/`or_u32`/`shl_u32`/`shr_u32`)"
  else if hasTyped "cir.div " unsignedTys then
    "unsigned division (`cir.div` on unsigned) is not admitted — only signed `sdiv` on `!s32i`"
  else if hasTyped "cir.rem " unsignedTys then
    "unsigned remainder (`cir.rem` on unsigned) is not admitted"
  else if hasOp "cir.rem " then
    "signed remainder (`cir.rem`) is not admitted — only `sdiv`"
  else if hasOp "cir.sub " then
    "subtraction (`cir.sub`) is not admitted — neither the `nsw` signed nor the wrapping unsigned spelling has a leaf"
  else if hasOp "cir.mul " then
    "multiplication (`cir.mul`) is not admitted outside the unsigned wrapping leaves — neither the `nsw` signed spelling nor a standalone leaf exists"
  else if hasOp "cir.shift" then
    "shifts (`cir.shift`) outside the `u32` single-op `shl_u32`/`shr_u32` leaves are not admitted"
  else if hasOp "cir.and " || hasOp "cir.or " || hasOp "cir.xor " then
    "bitwise ops (`cir.and` / `cir.or` / `cir.xor`) outside the `u32` single-op leaves are not admitted"
  else if hasOp "cir.minus" then
    "unary minus without `nsw` (wrapping negation overflow is UB in C: mark the op `nsw` for the `neg` leaf)"
  else
    "unwired arithmetic op (no leaf admits this spelling)"

/-- Index of the first line satisfying `pred` (`none` if absent). -/
def findLineIdx (ls : List String) (pred : String → Bool) : Option Nat :=
  go ls 0
where go : List String → Nat → Option Nat
  | [], _ => none
  | l :: rest, i => if pred l then some i else go rest (i + 1)

/-- Lines of the `cir.case` region whose header line contains `header`:
    lines after the header up to (excluding) the next `cir.case(`
    header or the switch-closing `cir.yield`. `[]` when the header is
    absent — so `caseRegionEmpty` (an `all`) must always be paired with
    an explicit header-presence pin, while `caseRegionHas` (an `any`)
    fails closed. -/
def caseRegion (ls : List String) (header : String) : List String :=
  match findLineIdx ls (fun l => containsSubstr l header) with
  | none => []
  | some i =>
    let rest := ls.drop (i + 1)
    match findLineIdx rest (fun l =>
      containsSubstr l "cir.case(" || containsSubstr l "cir.yield") with
    | none => rest
    | some j => rest.take j

/-- The case region holds no CIR op except the fallthrough `cir.yield`
    (closing `}` lines hold none). Pair with a header-presence pin:
    on an absent header the region is `[]` and this passes vacuously. -/
def caseRegionEmpty (ls : List String) (header : String) : Bool :=
  (caseRegion ls header).all (fun l =>
    !containsSubstr l "cir." || containsSubstr l "cir.yield")

/-- The case region mentions `needle` (fails closed on absent header). -/
def caseRegionHas (ls : List String) (header needle : String) : Bool :=
  (caseRegion ls header).any (fun l => containsSubstr l needle)

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

