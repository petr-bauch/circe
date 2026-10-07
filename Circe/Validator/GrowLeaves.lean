/-
Circe.Validator.GrowLeaves — N4d-iv-b1 growth-leaf shapes, over
`Circe.Validator.Shapes`.
-/
import Circe.CoreIR
import Circe.Parser
import Circe.Oracle
import Circe.Emit
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose
import Circe.Validator.Shapes

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

/-- By-value const-iterator param (N7c): the exact
    `__normal_iterator<const int*, vector<int>>` record alias, passed
    by value with neither the single-reference triple nor `noalias`
    (same erasure rationale as `isVecGrowIterParam`: the value model
    erases it to a `u64` offset). -/
def isVecGrowConstIterParam (p : RawParam) : Bool :=
  p.ctype ==
    "!rec___gnu_cxx3A3A__normal_iterator3Cconst_int_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
  !p.singleRef && !p.noalias

/-- Single-reference const-iterator param (N7c): the exact
    `__normal_iterator<const int*, vector<int>>` record alias behind
    the borrowed-pointer triple (the `const&` / `this` spelling of the
    const-iterator leaves). -/
def isVecGrowConstIterRef (p : RawParam) : Bool :=
  isVecGrowRef
    "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cconst_int_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
    p

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
  [stdVecSizeName, stdVecCapacityName, stdVecIndexName,
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
   stdVecPlusElName, stdVecIterEqName, stdVecConstIterCtorName,
   stdVecConstIterConvCtorName, stdVecConstIterBaseName,
   stdVecConstMinusName, stdVecCBeginName, stdVecCEndName,
   stdVecMIterBaseName, stdVecNIterWrapName,
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
    field is the only begin/end difference (N7c: plus the `cbegin` /
    `cend` twins, which return the const-iterator record through the
    const-iterator ctor — same loads, same single call; both stamp
    the shared `begin` / `end` canonical `Func`). -/
def isStdVecBeginShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    ((raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      callsFunc raw.text stdVecIterCtorName) ||
     (raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cconst_int_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      callsFunc raw.text stdVecConstIterCtorName)) &&
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
    ((raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      callsFunc raw.text stdVecIterCtorName) ||
     (raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cconst_int_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      callsFunc raw.text stdVecConstIterCtorName)) &&
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
    `u64` identity (`stdVecIterIdFunc`). N7c: plus the const-iterator
    twins — const `base`, the const-iterator default ctor, the
    converting ctor (fused as the identity offset copy through the
    non-const `base`), and `__niter_wrap` (drops the iterator, keeps
    the pointer) — all stamping the shared identity canonical
    `Func`. -/
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
    (raw.ret == "" &&
      isVecGrowRef
        "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
        this &&
      isVecGrowRef "!cir.ptr<!cir.ptr<!s32i>>" pp &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 1 &&
      containsSubstr raw.text "_M_current") ||
    (raw.ret == "" &&
      isVecGrowConstIterRef this &&
      isVecGrowRef "!cir.ptr<!cir.ptr<!s32i>>" pp &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 1 &&
      containsSubstr raw.text "_M_current") ||
    (raw.ret == "" &&
      isVecGrowConstIterRef this &&
      isVecGrowRef
        "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
        pp &&
      callsFunc raw.text stdVecIterBaseName &&
      opCount raw.text ("cir.call @" ++ stdVecIterBaseName ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.get_member" == 1 &&
      containsSubstr raw.text "_M_current") ||
    (raw.ret == "!cir.ptr<!s32i>" &&
      isVecGrowRef "!cir.ptr<!cir.ptr<!s32i>>" this &&
      isErasedIntPtr pp &&
      opCount raw.text "cir.call @" == 0 &&
      !containsSubstr raw.text "cir.get_member" &&
      !containsSubstr raw.text "_M_current")
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
      containsSubstr raw.text "_M_current") ||
    (isVecGrowConstIterRef p &&
      raw.ret == "!cir.ptr<!cir.ptr<!s32i>>" &&
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
    → `stdVecMinusFunc` (N7c: plus the const-iterator twin, over the
    double const-`base` — same fuse, same stamp). -/
def isStdVecMinusShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [a, b] =>
    isI64 raw.ret &&
    ((isVecGrowRef
      "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
      a &&
      isVecGrowRef
        "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
        b &&
      callsFunc raw.text stdVecIterBaseName &&
      opCount raw.text ("cir.call @" ++ stdVecIterBaseName ++ "(") == 2) ||
     (isVecGrowConstIterRef a &&
      isVecGrowConstIterRef b &&
      callsFunc raw.text stdVecConstIterBaseName &&
      opCount raw.text ("cir.call @" ++ stdVecConstIterBaseName ++ "(") == 2)) &&
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

/-- N7c `plEl` (non-const `operator+`): the `miEl` twin — `base` +
    `ptr_stride` fuse to wrapping `uadd` (the `s64` step arrives as
    the same bits in a `u64`) → `stdVecPlusElFunc`. -/
def isStdVecPlusElShape (raw : RawFunc) : Bool :=
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
    opCount raw.text ("cir.call @" ++ stdVecIterCtorName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 1 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.get_member" == 1 &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.minus" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- N7c const-iterator `operator==`: the double const-`base` + `cmp`
    fuse to `ueq` over erased offsets → `stdVecIterEqFunc`. -/
def isStdVecIterEqShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [a, b] =>
    isVecGrowConstIterRef a &&
    isVecGrowConstIterRef b &&
    raw.ret == "!cir.bool" &&
    callsFunc raw.text stdVecConstIterBaseName &&
    opCount raw.text ("cir.call @" ++ stdVecConstIterBaseName ++ "(") == 2 &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.cmp" == 1 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
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

/-- N4d-iv-b2 `vec_push_sum` entry shape: the closed corpus def (no
    params, `!s32i` return; the default ctor, three `push_back`, three
    non-const `operator[]`, and one destructor call; two `add`s; one
    `cleanup` scope with the single normal-path dtor call and the
    trailing unreachable `trap`). -/
def isVecPushSumEntryShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  raw.ret == "!s32i" &&
  match raw.params with
  | [] =>
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecCtorName &&
    opCount raw.text ("cir.call @" ++ stdVecCtorName ++ "(") == 1 &&
    callsFunc raw.text stdVecPushBackName &&
    opCount raw.text ("cir.call @" ++ stdVecPushBackName ++ "(") == 3 &&
    callsFunc raw.text stdVecGrowIndexName &&
    opCount raw.text ("cir.call @" ++ stdVecGrowIndexName ++ "(") == 3 &&
    callsFunc raw.text stdVecDtorName &&
    opCount raw.text ("cir.call @" ++ stdVecDtorName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 8 &&
    opCount raw.text "cir.alloca" == 5 &&
    opCount raw.text "cir.store" == 4 &&
    opCount raw.text "cir.load" == 4 &&
    opCount raw.text "cir.const" == 9 &&
    opCount raw.text "cir.add" == 2 &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.cleanup.scope" == 1 &&
    opCount raw.text "cir.trap" == 1 &&
    containsSubstr raw.text "cleanup normal" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- N7b `reserve` composer shape: the 8-site corpus def (`this` +
    `u64` width, void return; the `max_size` throw guard fused from
    the `get_global` + `array_to_ptrdecay` + `throw_length_error`
    sites, the `capacity < n` guard over the `capacity` + `size`
    calls, then the inline allocate → relocate (over the stateless
    `_M_get_Tp_allocator` site) → deallocate + header re-pin). -/
def isStdVecReserveShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  raw.ret == "" &&
  match raw.params with
  | [this, n] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isU64 n.ctype && !isPtrType n.ctype &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecMaxSizeName &&
    opCount raw.text ("cir.call @" ++ stdVecMaxSizeName ++ "(") == 1 &&
    callsFunc raw.text "_ZSt20__throw_length_errorPKc" &&
    opCount raw.text "cir.call @_ZSt20__throw_length_errorPKc(" == 1 &&
    callsFunc raw.text stdVecCapacityName &&
    opCount raw.text ("cir.call @" ++ stdVecCapacityName ++ "(") == 1 &&
    callsFunc raw.text stdVecSizeName &&
    opCount raw.text ("cir.call @" ++ stdVecSizeName ++ "(") == 1 &&
    callsFunc raw.text stdVecAllocateName &&
    opCount raw.text ("cir.call @" ++ stdVecAllocateName ++ "(") == 1 &&
    callsFunc raw.text stdVecGetTpName &&
    opCount raw.text ("cir.call @" ++ stdVecGetTpName ++ "(") == 1 &&
    callsFunc raw.text stdVecRelocName &&
    opCount raw.text ("cir.call @" ++ stdVecRelocName ++ "(") == 1 &&
    callsFunc raw.text stdVecDeallocName &&
    opCount raw.text ("cir.call @" ++ stdVecDeallocName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 8 &&
    opCount raw.text "cir.cmp" == 2 &&
    opCount raw.text "cir.if" == 2 &&
    opCount raw.text "cir.get_global" == 1 &&
    opCount raw.text "cir.base_class_addr" == 21 &&
    opCount raw.text "cir.get_member" == 18 &&
    opCount raw.text "cir.ptr_diff" == 1 &&
    containsSubstr raw.text "cir.cast integral" &&
    opCount raw.text "cir.ptr_stride" == 2 &&
    opCount raw.text "cir.alloca" == 4 &&
    opCount raw.text "cir.store" == 7 &&
    opCount raw.text "cir.load" == 15 &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.scope" == 3 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_finish" &&
    containsSubstr raw.text "_M_start" &&
    containsSubstr raw.text "_M_end_of_storage" &&
    !containsSubstr raw.text "realloc" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.cleanup" &&
    !containsSubstr raw.text "cir.trap" &&
    !containsSubstr raw.text "cir.derived_class_addr"
  | _ => false

/-- N7b `vec_reserve_sum` entry shape: the closed corpus def (no
    params, `!s32i` return; the default ctor, one `reserve(10)`, two
    `push_back`, two non-const `operator[]`, and one destructor call;
    one `nsw` add; one `cleanup` scope with the single normal-path
    dtor call and the trailing unreachable `trap`). -/
def isVecReserveSumEntryShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  raw.ret == "!s32i" &&
  match raw.params with
  | [] =>
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecCtorName &&
    opCount raw.text ("cir.call @" ++ stdVecCtorName ++ "(") == 1 &&
    callsFunc raw.text stdVecReserveName &&
    opCount raw.text ("cir.call @" ++ stdVecReserveName ++ "(") == 1 &&
    callsFunc raw.text stdVecPushBackName &&
    opCount raw.text ("cir.call @" ++ stdVecPushBackName ++ "(") == 2 &&
    callsFunc raw.text stdVecGrowIndexName &&
    opCount raw.text ("cir.call @" ++ stdVecGrowIndexName ++ "(") == 2 &&
    callsFunc raw.text stdVecDtorName &&
    opCount raw.text ("cir.call @" ++ stdVecDtorName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 7 &&
    opCount raw.text "cir.alloca" == 4 &&
    opCount raw.text "cir.store" == 3 &&
    opCount raw.text "cir.load" == 3 &&
    opCount raw.text "cir.const" == 8 &&
    opCount raw.text "cir.add" == 1 &&
    containsSubstr raw.text "#cir.int<10>" &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.cleanup.scope" == 1 &&
    opCount raw.text "cir.trap" == 1 &&
    containsSubstr raw.text "cleanup normal" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- N7c backward-shift chain: `move_backward` (double
    `__miter_base` + `__copy_move_backward_a`), `_a` (triple
    `__niter_base` + `__niter_wrap` + `_a1`), `_a1` / `_a2`
    (single-call forwarders), and `__copy_move_b` (the guarded
    `memmove` terminal: one `if`, two strides, one diff, one const).
    All five layers erase to the descending blit
    (`stdVecShiftBackFunc`). -/
def isStdVecShiftBackShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  !containsSubstr raw.text "cir.call @malloc" &&
  !containsSubstr raw.text "cir.call @free(" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.for" &&
  !containsSubstr raw.text "cir.switch" &&
  !containsSubstr raw.text "cir.cond_br" &&
  !containsSubstr raw.text "cir.while" &&
  !containsSubstr raw.text "cir.do" &&
  !containsSubstr raw.text "cir.unreachable" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.derived_class_addr" &&
  match raw.params with
  | [f, l, r] =>
    isErasedIntPtr f && isErasedIntPtr l && isErasedIntPtr r &&
    raw.ret == "!cir.ptr<!s32i>" &&
    !callsFunc raw.text raw.name &&
    ((callsFunc raw.text stdVecMIterBaseName &&
      opCount raw.text ("cir.call @" ++ stdVecMIterBaseName ++ "(") == 2 &&
      callsFunc raw.text stdVecShiftBackAName &&
      opCount raw.text ("cir.call @" ++ stdVecShiftBackAName ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 3 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (callsFunc raw.text stdVecNIterBaseName &&
      opCount raw.text ("cir.call @" ++ stdVecNIterBaseName ++ "(") == 3 &&
      callsFunc raw.text stdVecNIterWrapName &&
      opCount raw.text ("cir.call @" ++ stdVecNIterWrapName ++ "(") == 1 &&
      callsFunc raw.text stdVecShiftBackA1Name &&
      opCount raw.text ("cir.call @" ++ stdVecShiftBackA1Name ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 5 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (callsFunc raw.text stdVecShiftBackA2Name &&
      opCount raw.text ("cir.call @" ++ stdVecShiftBackA2Name ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (callsFunc raw.text stdVecShiftBackBName &&
      opCount raw.text ("cir.call @" ++ stdVecShiftBackBName ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (callsFunc raw.text "memmove" &&
      opCount raw.text "cir.call @memmove(" == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      opCount raw.text "cir.if" == 1 &&
      opCount raw.text "cir.ptr_stride" == 2 &&
      opCount raw.text "cir.ptr_diff" == 1 &&
      opCount raw.text "cir.const" == 1 &&
      containsSubstr raw.text "cir.cast integral" &&
      opCount raw.text "cir.minus" == 2))
  | _ => false

/-- N7c `_M_insert_aux` composer: the 4-site corpus def (`this` +
    by-value position + `x`, void return; `base` + deref + traits
    `construct` (copy-last-to-finish) + `move_backward` (shift right
    by one); the final assign is inlined stores). -/
def isStdVecInsertAuxShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  raw.ret == "" &&
  match raw.params with
  | [this, pos, x] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowIterParam pos &&
    isVecGrowRef "!cir.ptr<!s32i>" x &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecIterBaseName &&
    opCount raw.text ("cir.call @" ++ stdVecIterBaseName ++ "(") == 1 &&
    callsFunc raw.text stdVecIterDerefName &&
    opCount raw.text ("cir.call @" ++ stdVecIterDerefName ++ "(") == 1 &&
    callsFunc raw.text stdVecTraitsConstructName &&
    opCount raw.text ("cir.call @" ++ stdVecTraitsConstructName ++ "(") == 1 &&
    callsFunc raw.text stdVecShiftBackName &&
    opCount raw.text ("cir.call @" ++ stdVecShiftBackName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 4 &&
    opCount raw.text "cir.get_member" == 11 &&
    opCount raw.text "cir.base_class_addr" == 12 &&
    opCount raw.text "cir.ptr_stride" == 4 &&
    opCount raw.text "cir.const" == 4 &&
    opCount raw.text "cir.minus" == 3 &&
    opCount raw.text "cir.store" == 5 &&
    opCount raw.text "cir.load" == 9 &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.alloca" == 3 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_finish" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.cleanup" &&
    !containsSubstr raw.text "cir.trap" &&
    !containsSubstr raw.text "cir.ptr_diff" &&
    !containsSubstr raw.text "cir.derived_class_addr"
  | _ => false

/-- N7c `_M_insert_rval` composer: the 12-site corpus def (`this` +
    by-value const position + `x`, iterator return; the `pos == len`
    fast path over traits `construct`, the `_M_insert_aux` slow
    path over `cbegin` / `cend` / `mi` / `plEl` / `eq` / `begin`, the
    full-capacity path over `_M_realloc_insert`). -/
def isStdVecInsertRvalShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this, pos, x] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowConstIterParam pos &&
    isVecGrowRef "!cir.ptr<!s32i>" x &&
    raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecIterCtorName &&
    opCount raw.text ("cir.call @" ++ stdVecIterCtorName ++ "(") == 1 &&
    callsFunc raw.text stdVecIterEqName &&
    opCount raw.text ("cir.call @" ++ stdVecIterEqName ++ "(") == 1 &&
    callsFunc raw.text stdVecConstMinusName &&
    opCount raw.text ("cir.call @" ++ stdVecConstMinusName ++ "(") == 1 &&
    callsFunc raw.text stdVecPlusElName &&
    opCount raw.text ("cir.call @" ++ stdVecPlusElName ++ "(") == 2 &&
    callsFunc raw.text stdVecCEndName &&
    opCount raw.text ("cir.call @" ++ stdVecCEndName ++ "(") == 1 &&
    callsFunc raw.text stdVecCBeginName &&
    opCount raw.text ("cir.call @" ++ stdVecCBeginName ++ "(") == 1 &&
    callsFunc raw.text stdVecTraitsConstructName &&
    opCount raw.text ("cir.call @" ++ stdVecTraitsConstructName ++ "(") == 1 &&
    callsFunc raw.text stdVecInsertAuxName &&
    opCount raw.text ("cir.call @" ++ stdVecInsertAuxName ++ "(") == 1 &&
    callsFunc raw.text stdVecGrowReallocName &&
    opCount raw.text ("cir.call @" ++ stdVecGrowReallocName ++ "(") == 1 &&
    callsFunc raw.text stdVecBeginName &&
    opCount raw.text ("cir.call @" ++ stdVecBeginName ++ "(") == 2 &&
    opCount raw.text "cir.call @" == 12 &&
    opCount raw.text "cir.cmp" == 1 &&
    opCount raw.text "cir.if" == 2 &&
    opCount raw.text "cir.get_member" == 11 &&
    opCount raw.text "cir.base_class_addr" == 12 &&
    opCount raw.text "cir.ptr_stride" == 2 &&
    opCount raw.text "cir.const" == 1 &&
    opCount raw.text "cir.scope" == 2 &&
    opCount raw.text "cir.alloca" == 12 &&
    opCount raw.text "cir.store" == 12 &&
    opCount raw.text "cir.load" == 15 &&
    opCount raw.text "cir.return" == 1 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_finish" &&
    containsSubstr raw.text "_M_start" &&
    containsSubstr raw.text "_M_end_of_storage" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.cleanup" &&
    !containsSubstr raw.text "cir.trap" &&
    !containsSubstr raw.text "cir.ptr_diff" &&
    !containsSubstr raw.text "cir.derived_class_addr"
  | _ => false

/-- N7c `insert` forwarder: the single-site corpus def (`this` +
    by-value const position + `x`, iterator return; delegates to
    `_M_insert_rval`, the iterator return drops). -/
def isStdVecInsertShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this, pos, x] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowConstIterParam pos &&
    isVecGrowRef "!cir.ptr<!s32i>" x &&
    raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecInsertRvalName &&
    opCount raw.text ("cir.call @" ++ stdVecInsertRvalName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 1 &&
    opCount raw.text "cir.store" == 4 &&
    opCount raw.text "cir.load" == 4 &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.alloca" == 5 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff"
  | _ => false

/-- N7c `vec_insert_sum` entry shape: the closed corpus def (no
    params, `!s32i` return; the default ctor, one `reserve(10)`, two
    `push_back` (`1`, `3`), `begin` + one `operator+` step, one
    `insert` (`2` at position `1`), three `operator[]`, two `nsw`
    adds, and one destructor call; one `cleanup` scope with the
    single normal-path dtor call and the trailing unreachable
    `trap`). -/
def isVecInsertSumEntryShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  raw.ret == "!s32i" &&
  match raw.params with
  | [] =>
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecCtorName &&
    opCount raw.text ("cir.call @" ++ stdVecCtorName ++ "(") == 1 &&
    callsFunc raw.text stdVecReserveName &&
    opCount raw.text ("cir.call @" ++ stdVecReserveName ++ "(") == 1 &&
    callsFunc raw.text stdVecPushBackName &&
    opCount raw.text ("cir.call @" ++ stdVecPushBackName ++ "(") == 2 &&
    callsFunc raw.text stdVecBeginName &&
    opCount raw.text ("cir.call @" ++ stdVecBeginName ++ "(") == 1 &&
    callsFunc raw.text stdVecPlusElName &&
    opCount raw.text ("cir.call @" ++ stdVecPlusElName ++ "(") == 1 &&
    callsFunc raw.text stdVecConstIterConvCtorName &&
    opCount raw.text ("cir.call @" ++ stdVecConstIterConvCtorName ++ "(") == 1 &&
    callsFunc raw.text stdVecInsertName &&
    opCount raw.text ("cir.call @" ++ stdVecInsertName ++ "(") == 1 &&
    callsFunc raw.text stdVecGrowIndexName &&
    opCount raw.text ("cir.call @" ++ stdVecGrowIndexName ++ "(") == 3 &&
    callsFunc raw.text stdVecDtorName &&
    opCount raw.text ("cir.call @" ++ stdVecDtorName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 12 &&
    opCount raw.text "cir.alloca" == 9 &&
    opCount raw.text "cir.store" == 7 &&
    opCount raw.text "cir.load" == 5 &&
    opCount raw.text "cir.const" == 13 &&
    opCount raw.text "cir.add" == 2 &&
    containsSubstr raw.text "#cir.int<10>" &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.cleanup.scope" == 1 &&
    opCount raw.text "cir.trap" == 1 &&
    containsSubstr raw.text "cleanup normal" &&
    !containsSubstr raw.text "cir.cmp" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.switch" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ptr_diff"
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
  isStdVecRelocShape raw || isStdVecShiftBackShape raw

/-- A param whose missing `llvm.noalias` needs no recovery: a borrowed
    erased-offset pointer inside a pinned b1 shape (cf.
    `isRecoveredParam`: same carve-out role, value-model erasure
    instead of reader recovery). -/
def isVecGrowErasedParam (raw : RawFunc) (p : RawParam) : Bool :=
  isVecGrowShape raw && isErasedIntPtr p

