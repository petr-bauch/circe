/-
Circe.Validator.GrowLeaves — N4d-iv-b1 growth-leaf shapes, over
`Circe.Validator.Shapes`.
-/
import Circe.CoreIR
import Circe.Parser
import Circe.Scope
import Circe.Oracle
import Circe.Emit
import Circe.Emit.VecGrow
import Circe.Emit.VecAt
import Circe.Emit.VecAtSet
import Circe.Emit.VecMarkCount
import Circe.Emit.VecCompose
import Circe.Emit.VecSegReverse
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

/-- `_M_range_check` `get_global` exemption: the throw-message
    materialization (`get_global` of the `.str` format array +
    `array_to_ptrdecay`) feeding exactly the noreturn
    `__throw_out_of_range_fmt` call, with the `ge` guard + `if` and
    exactly `2 × size + 1 × throw` calls. The message bytes are
    read-only format data consumed by a noreturn abort — no readable
    or writable global state. This is the `forbiddenOp` exemption
    gate (cf. `isVecDtorExemptText`); full admission additionally
    pins the signature (`isStdVecRangeCheckShape`). -/
def isVecRangeCheckExemptText (text : String) : Bool :=
  hasNonHeapGlobal text &&
  containsSubstr text "cir.get_global @\".str\"" &&
  containsSubstr text "array_to_ptrdecay" &&
  callsFunc text "_ZSt24__throw_out_of_range_fmtPKcz" &&
  opCount text "cir.call @" == 3 &&
  containsSubstr text "cir.cmp ge" &&
  opCount text "cir.if" == 1 &&
  !containsSubstr text "cir.call @malloc" &&
  !containsSubstr text "cir.call @free(" &&
  !containsSubstr text "cir.try" &&
  !containsSubstr text "cir.while"

/-- Known `std::vector<int32_t>` leaf callees (mangled): the `size`
    projection leaf and the fused `operator[]` leaf (N4d-iv-a), plus
    every N4d-iv-b1 growth leaf (the ctor/dtor/consume/max/iterator/
    allocate/deallocate/construct/relocate family). Entry gates
    admit calls into the (name, arity, site-count) pairs named in
    `validate` below; this registry names every known vector leaf
    for the wrong-shape rejection. -/
def stdVecLeafCallees : List String :=
  [stdVecSizeName, stdVecCapacityName, stdVecIndexName,
   stdVecIndexMutName, stdVecRangeCheckName, stdVecAtName, stdVecAtMutName,
   charVecSizeName, charVecIndexName, charVecIndexMutName,
   charVecRangeCheckName, charVecAtName, charVecAtMutName,
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
  match raw.params with
  | [this, pp] =>
    (raw.ret == "" &&
      isVecGrowRef
        "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
        this &&
      isVecGrowRef "!cir.ptr<!cir.ptr<!s32i>>" pp &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 1 &&
      !containsSubstr raw.text "cir.ptr_diff" &&
      containsSubstr raw.text "_M_current") ||
    (raw.ret == "" &&
      isVecGrowConstIterRef this &&
      isVecGrowRef "!cir.ptr<!cir.ptr<!s32i>>" pp &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 1 &&
      !containsSubstr raw.text "cir.ptr_diff" &&
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
      !containsSubstr raw.text "cir.ptr_diff" &&
      containsSubstr raw.text "_M_current") ||
    (raw.ret == "!cir.ptr<!s32i>" &&
      isVecGrowRef "!cir.ptr<!cir.ptr<!s32i>>" this &&
      isErasedIntPtr pp &&
      opCount raw.text "cir.call @" == 0 &&
      !containsSubstr raw.text "cir.get_member" &&
      !containsSubstr raw.text "cir.ptr_diff" &&
      !containsSubstr raw.text "_M_current") ||
    (isVecGrowIterParam this &&
      isErasedIntPtr pp &&
      raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      callsFunc raw.text stdVecNIterBaseMoveName &&
      opCount raw.text ("cir.call @" ++ stdVecNIterBaseMoveName ++ "(") == 1 &&
      callsFunc raw.text stdVecPlusElName &&
      opCount raw.text ("cir.call @" ++ stdVecPlusElName ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 2 &&
      !callsFunc raw.text raw.name &&
      opCount raw.text "cir.ptr_diff" == 1 &&
      !containsSubstr raw.text "cir.get_member")
  | [p] =>
    (isErasedIntPtr p && raw.ret == "!cir.ptr<!s32i>" &&
      opCount raw.text "cir.call @" == 0 &&
      !containsSubstr raw.text "cir.ptr_diff" &&
      !containsSubstr raw.text "cir.get_member") ||
    (isVecGrowRef
      "!cir.ptr<!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E>"
      p &&
      (raw.ret == "!cir.ptr<!cir.ptr<!s32i>>" ||
       raw.ret == "!cir.ptr<!s32i>") &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 1 &&
      !containsSubstr raw.text "cir.ptr_diff" &&
      containsSubstr raw.text "_M_current") ||
    (isVecGrowConstIterRef p &&
      raw.ret == "!cir.ptr<!cir.ptr<!s32i>>" &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.get_member" == 1 &&
      !containsSubstr raw.text "cir.ptr_diff" &&
      containsSubstr raw.text "_M_current") ||
    (isVecGrowIterParam p &&
      raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      opCount raw.text "cir.call @" == 0 &&
      opCount raw.text "cir.copy" == 1 &&
      !containsSubstr raw.text "cir.ptr_diff" &&
      !containsSubstr raw.text "cir.get_member") ||
    (isVecGrowIterParam p &&
      raw.ret == "!cir.ptr<!s32i>" &&
      callsFunc raw.text stdVecIterBaseName &&
      opCount raw.text ("cir.call @" ++ stdVecIterBaseName ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      !callsFunc raw.text raw.name &&
      !containsSubstr raw.text "cir.ptr_diff" &&
      !containsSubstr raw.text "cir.get_member")
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

/-- N7d non-const iterator `operator!=`: the double non-const
    `base` + `cmp ne` fuse to `une` over erased offsets →
    `stdVecIterNeFunc` (the `eq` twin over const iterators stays
    separate — different comparison, different canonical). -/
def isStdVecIterNeShape (raw : RawFunc) : Bool :=
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
    raw.ret == "!cir.bool" &&
    callsFunc raw.text stdVecIterBaseName &&
    opCount raw.text ("cir.call @" ++ stdVecIterBaseName ++ "(") == 2 &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.cmp" == 1 &&
    containsSubstr raw.text "cmp ne" &&
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

/-- N7d forward-shift chain: `std::move` (double `__miter_base` +
    `__copy_move_a`), `_a` (triple `__niter_base` + `__niter_wrap` +
    `_a1`), `_a1` / `_a2` (single-call forwarders), and `__copy_m`
    (the guarded `memmove` terminal: one `if`, one stride, one
    diff, one const, no `minus` — the erase `memmove` moves
    `[first, last)` to `result` directly). All five layers erase to
    the ascending blit (`stdVecShiftDownFunc`). -/
def isStdVecShiftDownShape (raw : RawFunc) : Bool :=
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
    !callsFunc raw.text raw.name &&
    ((isVecGrowIterParam f && isVecGrowIterParam l &&
      isVecGrowIterParam r &&
      raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      callsFunc raw.text stdVecMIterBaseMoveName &&
      opCount raw.text ("cir.call @" ++ stdVecMIterBaseMoveName ++ "(") == 2 &&
      callsFunc raw.text stdVecShiftDownAName &&
      opCount raw.text ("cir.call @" ++ stdVecShiftDownAName ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 3 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (isVecGrowIterParam f && isVecGrowIterParam l &&
      isVecGrowIterParam r &&
      raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
      callsFunc raw.text stdVecNIterBaseMoveName &&
      opCount raw.text ("cir.call @" ++ stdVecNIterBaseMoveName ++ "(") == 3 &&
      callsFunc raw.text stdVecNIterWrapMoveName &&
      opCount raw.text ("cir.call @" ++ stdVecNIterWrapMoveName ++ "(") == 1 &&
      callsFunc raw.text stdVecShiftDownA1Name &&
      opCount raw.text ("cir.call @" ++ stdVecShiftDownA1Name ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 5 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (isErasedIntPtr f && isErasedIntPtr l && isErasedIntPtr r &&
      raw.ret == "!cir.ptr<!s32i>" &&
      callsFunc raw.text stdVecShiftDownA2Name &&
      opCount raw.text ("cir.call @" ++ stdVecShiftDownA2Name ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (isErasedIntPtr f && isErasedIntPtr l && isErasedIntPtr r &&
      raw.ret == "!cir.ptr<!s32i>" &&
      callsFunc raw.text stdVecShiftDownBName &&
      opCount raw.text ("cir.call @" ++ stdVecShiftDownBName ++ "(") == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      !containsSubstr raw.text "cir.cmp" &&
      !containsSubstr raw.text "cir.if" &&
      !containsSubstr raw.text "cir.const" &&
      !containsSubstr raw.text "cir.ptr_stride") ||
     (isErasedIntPtr f && isErasedIntPtr l && isErasedIntPtr r &&
      raw.ret == "!cir.ptr<!s32i>" &&
      callsFunc raw.text "memmove" &&
      opCount raw.text "cir.call @memmove(" == 1 &&
      opCount raw.text "cir.call @" == 1 &&
      opCount raw.text "cir.if" == 1 &&
      opCount raw.text "cir.ptr_stride" == 1 &&
      opCount raw.text "cir.ptr_diff" == 1 &&
      opCount raw.text "cir.const" == 1 &&
      containsSubstr raw.text "cir.cast integral" &&
      !containsSubstr raw.text "cir.minus"))
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

/-- N7d `_M_erase` composer: the 7-site corpus def (`this` +
    by-value position, iterator return; `position + 1` vs `end`
    over `plEl` / `end` / `ne`, the guarded shift-down over
    `std::move`, `--finish` over one `ptr_stride`, one trivial
    `destroy`, `_M_impl` / `_M_finish` member traffic). -/
def isStdVecEraseCoreShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this, pos] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowIterParam pos &&
    raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecPlusElName &&
    opCount raw.text ("cir.call @" ++ stdVecPlusElName ++ "(") == 2 &&
    callsFunc raw.text stdVecEndName &&
    opCount raw.text ("cir.call @" ++ stdVecEndName ++ "(") == 2 &&
    callsFunc raw.text stdVecIterNeName &&
    opCount raw.text ("cir.call @" ++ stdVecIterNeName ++ "(") == 1 &&
    callsFunc raw.text stdVecShiftDownName &&
    opCount raw.text ("cir.call @" ++ stdVecShiftDownName ++ "(") == 1 &&
    callsFunc raw.text "_ZNSt16allocator_traitsISaIiEE7destroyIiEEvRS0_PT_" &&
    opCount raw.text "cir.call @_ZNSt16allocator_traitsISaIiEE7destroyIiEEvRS0_PT_(" == 1 &&
    opCount raw.text "cir.call @" == 7 &&
    opCount raw.text "cir.if" == 1 &&
    opCount raw.text "cir.const" == 5 &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    opCount raw.text "cir.get_member" == 5 &&
    opCount raw.text "cir.base_class_addr" == 6 &&
    opCount raw.text "cir.copy" == 2 &&
    opCount raw.text "cir.scope" == 1 &&
    opCount raw.text "cir.alloca" == 9 &&
    opCount raw.text "cir.store" == 8 &&
    opCount raw.text "cir.load" == 7 &&
    opCount raw.text "cir.return" == 1 &&
    containsSubstr raw.text "_M_impl" &&
    containsSubstr raw.text "_M_finish" &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.cmp" &&
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
    !containsSubstr raw.text "cir.minus" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.derived_class_addr"
  | _ => false

/-- N7d `erase` forwarder: the 5-site corpus def (`this` +
    by-value const position, iterator return; `begin` + `cbegin` +
    const-`mi` + `plEl` convert to the offset, then one
    `_M_erase` call, the iterator return drops). -/
def isStdVecEraseShape (raw : RawFunc) : Bool :=
  noBreakContinueSwitch raw.text &&
  !containsSubstr raw.text "realloc" &&
  !containsSubstr raw.text "cir.get_global" &&
  match raw.params with
  | [this, pos] =>
    isVecGrowRef
      "!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>"
      this &&
    isVecGrowConstIterParam pos &&
    raw.ret == "!rec___gnu_cxx3A3A__normal_iterator3Cint_2A2C_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E3E" &&
    !callsFunc raw.text raw.name &&
    callsFunc raw.text stdVecBeginName &&
    opCount raw.text ("cir.call @" ++ stdVecBeginName ++ "(") == 1 &&
    callsFunc raw.text stdVecCBeginName &&
    opCount raw.text ("cir.call @" ++ stdVecCBeginName ++ "(") == 1 &&
    callsFunc raw.text stdVecConstMinusName &&
    opCount raw.text ("cir.call @" ++ stdVecConstMinusName ++ "(") == 1 &&
    callsFunc raw.text stdVecPlusElName &&
    opCount raw.text ("cir.call @" ++ stdVecPlusElName ++ "(") == 1 &&
    callsFunc raw.text stdVecEraseCoreName &&
    opCount raw.text ("cir.call @" ++ stdVecEraseCoreName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 5 &&
    opCount raw.text "cir.store" == 6 &&
    opCount raw.text "cir.load" == 3 &&
    opCount raw.text "cir.return" == 1 &&
    opCount raw.text "cir.alloca" == 6 &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.const" &&
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
    !containsSubstr raw.text "cir.get_member" &&
    !containsSubstr raw.text "cir.base_class_addr" &&
    !containsSubstr raw.text "cir.ptr_stride" &&
    !containsSubstr raw.text "cir.ptr_diff" &&
    !containsSubstr raw.text "cir.minus" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.copy" &&
    !containsSubstr raw.text "cir.scope" &&
    !containsSubstr raw.text "cir.derived_class_addr"
  | _ => false

/-- N7d `vec_erase_sum` entry shape: the closed corpus def (no
    params, `!s32i` return; the default ctor, one `reserve(10)`,
    three `push_back` (`1`, `2`, `3`), `begin` + one `operator+`
    step, one `erase` (at position `1`), two `operator[]`, one
    `nsw` add, and one destructor call; one `cleanup` scope with
    the single normal-path dtor call and the trailing
    unreachable `trap`). -/
def isVecEraseSumEntryShape (raw : RawFunc) : Bool :=
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
    opCount raw.text ("cir.call @" ++ stdVecPushBackName ++ "(") == 3 &&
    callsFunc raw.text stdVecBeginName &&
    opCount raw.text ("cir.call @" ++ stdVecBeginName ++ "(") == 1 &&
    callsFunc raw.text stdVecPlusElName &&
    opCount raw.text ("cir.call @" ++ stdVecPlusElName ++ "(") == 1 &&
    callsFunc raw.text stdVecConstIterConvCtorName &&
    opCount raw.text ("cir.call @" ++ stdVecConstIterConvCtorName ++ "(") == 1 &&
    callsFunc raw.text stdVecEraseName &&
    opCount raw.text ("cir.call @" ++ stdVecEraseName ++ "(") == 1 &&
    callsFunc raw.text stdVecGrowIndexName &&
    opCount raw.text ("cir.call @" ++ stdVecGrowIndexName ++ "(") == 2 &&
    callsFunc raw.text stdVecDtorName &&
    opCount raw.text ("cir.call @" ++ stdVecDtorName ++ "(") == 1 &&
    opCount raw.text "cir.call @" == 12 &&
    opCount raw.text "cir.alloca" == 9 &&
    opCount raw.text "cir.store" == 7 &&
    opCount raw.text "cir.load" == 4 &&
    opCount raw.text "cir.const" == 11 &&
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
  isStdVecRelocShape raw || isStdVecShiftBackShape raw ||
  isStdVecShiftDownShape raw

/-- A param whose missing `llvm.noalias` needs no recovery: a borrowed
    erased-offset pointer inside a pinned b1 shape (cf.
    `isRecoveredParam`: same carve-out role, value-model erasure
    instead of reader recovery). -/
def isVecGrowErasedParam (raw : RawFunc) (p : RawParam) : Bool :=
  isVecGrowShape raw && isErasedIntPtr p

/-! ## L2-admission: sequential-writer-pair recognition (deferred) -/

/-- L2-ordered disjointness over scope locals: exactly three locals
    `[root, a, b]` in source order with the first writer's range
    observed and ending strictly before the second writer's begins.
    The `alias_reborrow` pair satisfies this (`r` ends before `s`
    begins); the overlapping `alias_cond` pair fails exactly this
    comparison, so it stays on the generic reject path. This is the
    admission predicate the L-track follow-up wires: `true` means the
    two derived references' RECORDED live ranges are disjoint in order
    (unresolvable mentions count conservatively, so recorded
    disjointness admits less, never more). -/
def hasSequentialWriterRanges (text : String) : Bool :=
  match (extractScopes text).locals with
  | [_, a, b] =>
    0 < a.firstUse && 0 < a.lastUse && a.firstUse ≤ a.lastUse &&
      a.lastUse < b.firstUse
  | _ => false

/-- Structural half of sequential-writer-pair recognition: `void`,
    one single-reference pointer root param, three writer-family
    allocas, no calls / comparisons / loops / cleanup / traps /
    globals / strided indexing. The L2 half
    (`hasSequentialWriterRanges`) is checked last, so the
    `extractScopes` fold runs only after the cheap pins pass. -/
def structuralSequentialReborrow (raw : RawFunc) : Bool :=
  raw.ret == "" &&
  opCount raw.text "cir.alloca" == 3 &&
  opCount raw.text "cir.call @" == 0 &&
  opCount raw.text "cir.cmp" == 0 &&
  opCount raw.text "cir.for" == 0 &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "get_global" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  (match raw.params with
   | [p] => p.singleRef && isPtrType p.ctype
   | _ => false)

/-- Sequential-writer-pair recognition: structural pins plus
    L2-ordered disjoint writer ranges. Recognized shapes are still
    REJECTED (mutable writers need Iris framing over `Mem` — there is
    no writer `Func` yet); the gate routes them to the deferred message
    instead of the generic fragment fallthrough. The branch sits after
    every admission, so no admitted shape can be shadowed. -/
def isSequentialReborrowShape (raw : RawFunc) : Bool :=
  structuralSequentialReborrow raw && hasSequentialWriterRanges raw.text

/-- The two `nsw` adds consume the `1`/`2` consts in order (first add
    reads the `1`-const, never the `2`-const, and vice versa) — the
    computation pin that makes the fused `x + 1 + 2` exact. The type
    suffix pins `!s32i` (so `#cir.int<1>` never matches `#cir.int<10>`
    and no other integer width slips in). -/
def reborrowConstUse (text : String) : Bool :=
  let ls := text.splitOn "\n"
  let ones := ls.filterMap fun ln =>
    if containsSubstr ln "cir.const #cir.int<1> : !s32i" then ssaDefOn ln
    else none
  let twos := ls.filterMap fun ln =>
    if containsSubstr ln "cir.const #cir.int<2> : !s32i" then ssaDefOn ln
    else none
  let adds := ls.filter (fun ln => containsSubstr ln "cir.add nsw")
  match ones, twos, adds with
  | [c1], [c2], [a1, a2] =>
    mentionsSSA (defRest a1) c1 && !mentionsSSA (defRest a1) c2 &&
    mentionsSSA (defRest a2) c2 && !mentionsSSA (defRest a2) c1
  | _, _, _ => false

/-- Both derived writers resolve to `param0` (positional: the second
    and third slots' ultimate roots) — the F0 same-address license
    for fusing the two phases into one `x + 1 + 2` through one cell. -/
def reborrowSameAddress (text : String) : Bool :=
  match contentRoots (text.splitOn "\n") with
  | [_, (_, _, u1), (_, _, u2)] =>
    showRoot u1 == "param0" && showRoot u2 == "param0"
  | _ => false

/-- Exact `alias_reborrow` admission shape (F1): the
    sequential-writer skeleton (L2-ordered disjoint ranges, one shared
    address) computing exactly `x + 1` then `x + 2` — two `nsw` adds,
    the `1`/`2` consts consumed in order, no other consts, calls,
    branches, or scopes. Everything else sequential-writer-shaped
    keeps the deferred message. -/
def isReborrowShape (raw : RawFunc) : Bool :=
  structuralSequentialReborrow raw &&
  opCount raw.text "cir.store" == 5 &&
  opCount raw.text "cir.load" == 6 &&
  opCount raw.text "cir.const" == 2 &&
  opCount raw.text "cir.add nsw" == 2 &&
  !containsSubstr raw.text "cir.if" &&
  !containsSubstr raw.text "cir.scope" &&
  reborrowConstUse raw.text &&
  hasSequentialWriterRanges raw.text &&
  reborrowSameAddress raw.text

/-- The two `nsw` adds consume the `3`/`4` consts in order (first add
    reads the `3`-const, never the `4`-const, and vice versa) — the
    computation pin that makes the fused `x + 3 + 4` exact. Same
    `!s32i` type-suffix discipline as `reborrowConstUse`. -/
def reborrow34ConstUse (text : String) : Bool :=
  let ls := text.splitOn "\n"
  let threes := ls.filterMap fun ln =>
    if containsSubstr ln "cir.const #cir.int<3> : !s32i" then ssaDefOn ln
    else none
  let fours := ls.filterMap fun ln =>
    if containsSubstr ln "cir.const #cir.int<4> : !s32i" then ssaDefOn ln
    else none
  let adds := ls.filter (fun ln => containsSubstr ln "cir.add nsw")
  match threes, fours, adds with
  | [c1], [c2], [a1, a2] =>
    mentionsSSA (defRest a1) c1 && !mentionsSSA (defRest a1) c2 &&
    mentionsSSA (defRest a2) c2 && !mentionsSSA (defRest a2) c1
  | _, _, _ => false

/-- Exact `alias_reborrow34` admission shape (L1b): the same
    sequential-writer skeleton with the `3`/`4` consts consumed in
    order. Mutually exclusive with `isReborrowShape` (the const-use
    pins disagree), so branch order between them is irrelevant. -/
def isReborrow34Shape (raw : RawFunc) : Bool :=
  structuralSequentialReborrow raw &&
  opCount raw.text "cir.store" == 5 &&
  opCount raw.text "cir.load" == 6 &&
  opCount raw.text "cir.const" == 2 &&
  opCount raw.text "cir.add nsw" == 2 &&
  !containsSubstr raw.text "cir.if" &&
  !containsSubstr raw.text "cir.scope" &&
  reborrow34ConstUse raw.text &&
  hasSequentialWriterRanges raw.text &&
  reborrowSameAddress raw.text

/-! ## G2-admission: disjoint writer-pair recognition (`wr_pair`) -/

/-- SSA operands in order: every `%N` token with a digit run and a
    non-alphanumeric boundary (`%5,` and `%6` count; `%arg0`,
    `#cir.int<1>`, `loc(#loc22)` never do). Tokens are
    space-separated, so no recursion is needed. -/
def tokSSA (tok : String) : Option Nat :=
  match tok.toList with
  | '%' :: d :: ds =>
    if d.isDigit then
      let digs := d :: ds.takeWhile (·.isDigit)
      let rest := ds.dropWhile (·.isDigit)
      if rest.all (fun c => !c.isDigit && !c.isAlpha) then
        some (String.toNat! (String.ofList digs))
      else none
    else none
  | _ => none

/-- Operand list of a line (definition prefix dropped, so the birth
    is never a use). -/
def ssaOperands (line : String) : List Nat :=
  ((defRest line).splitOn " ").filterMap tokSSA

/-- Load chain to an alloca (fuel-bounded, like `ultimateRoot`):
    `v` resolves when its definition is `cir.alloca`, otherwise a
    single-operand `cir.load` hops to its source. Multi-operand
    definitions (adds, consts) and loads of non-allocas resolve to
    nothing — elt reads cannot be addresses and addresses cannot be
    values. The corpus needs two hops (elt-load → addr-load →
    alloca); the store dest needs one (reloaded alloca). -/
def chaseLoadAlloca : List String → Nat → Nat → Option Nat
  | _, _, 0 => none
  | ls, v, fuel + 1 =>
    match ls.find? (fun ln => ssaDefOn ln == some v) with
    | none => none
    | some defLn =>
      if containsSubstr (defRest defLn) "cir.alloca" then some v
      else
        match ssaOperands defLn with
        | [src] => chaseLoadAlloca ls src fuel
        | _ => none

/-- The cell a writer store lands in: the dest operand chased to its
    alloca (the corpus reloads the param alloca; a direct alloca
    dest resolves too). -/
def storeCellAlloca (ls : List String) (storeLine : String) : Option Nat :=
  match ssaOperands storeLine with
  | [_, dest] => chaseLoadAlloca ls dest 8
  | _ => none

/-- Which `%argK` initializes an alloca (the `cir.store %argK, %M`
    init pattern; writer stores carry no `%arg`). -/
def allocaArgIdx (ls : List String) (m : Nat) : Option Nat :=
  match ls.find? (fun ln =>
      containsSubstr ln "cir.store %arg" && mentionsSSA (defRest ln) m) with
  | some ln =>
    match ln.splitOn "%arg" with
    | [_, rest] =>
      let digs := rest.toList.takeWhile (·.isDigit)
      if digs.isEmpty then none
      else some (String.toNat! (String.ofList digs))
    | _ => none
  | none => none

/-- Full dataflow pin for the writer pair (what op counts alone
    cannot say): the `1`-add feeds the first store into `%arg0`'s
    cell from that same cell, and the `2`-add feeds the second store
    into `%arg1`'s cell from that same cell. This rejects the three
    near-miss shapes with identical op counts: same-cell writers
    (`*p += 1; *p += 2` — cells equal), swapped writers
    (`*q += 1; *p += 2` — arg order flipped), and cross reads
    (`*q = *p + 1` — elt source is the other cell). -/
def wrPairDataflow (text : String) : Bool :=
  let ls := text.splitOn "\n"
  let const1 := ls.filter (fun ln =>
    containsSubstr ln "cir.const #cir.int<1> : !s32i")
  let const2 := ls.filter (fun ln =>
    containsSubstr ln "cir.const #cir.int<2> : !s32i")
  let stores := ls.filter (fun ln => containsSubstr ln "cir.store align(4)")
  let adds := ls.filter (fun ln => containsSubstr ln "cir.add nsw")
  match const1, const2, stores, adds with
  | [k1], [k2], [s1, s2], [a1, a2] =>
    match ssaDefOn k1, ssaDefOn k2, ssaDefOn a1, ssaDefOn a2 with
    | some c1, some c2, some d1, some d2 =>
      match ssaOperands a1, ssaOperands a2,
          ssaOperands s1, ssaOperands s2 with
      | [e1, k1'], [e2, k2'], [v1, _], [v2, _] =>
        k1' == c1 && k2' == c2 && v1 == d1 && v2 == d2 &&
        match storeCellAlloca ls s1, storeCellAlloca ls s2 with
        | some m1, some m2 =>
          m1 != m2 && allocaArgIdx ls m1 == some 0 &&
          allocaArgIdx ls m2 == some 1 &&
          chaseLoadAlloca ls e1 8 == some m1 &&
          chaseLoadAlloca ls e2 8 == some m2
        | _, _ => false
      | _, _, _, _ => false
    | _, _, _, _ => false
  | _, _, _, _ => false

/-- Structural half of writer-pair recognition: `void`, two
    non-single-reference `i32` pointer params (C `__restrict__`, never
    the C++ triple), two allocas, four stores, six loads, exactly the
    `1`/`2` consts and two `nsw` adds, no calls / comparisons / loops /
    branches / scopes / cleanup / traps / globals / strides / members. -/
def structuralWrPair (raw : RawFunc) : Bool :=
  raw.ret == "" &&
  opCount raw.text "cir.alloca" == 2 &&
  opCount raw.text "cir.store" == 4 &&
  opCount raw.text "cir.load" == 6 &&
  opCount raw.text "cir.const" == 2 &&
  opCount raw.text "cir.add nsw" == 2 &&
  arithOpCount raw.text == 2 &&
  opCount raw.text "cir.call @" == 0 &&
  opCount raw.text "cir.cmp" == 0 &&
  opCount raw.text "cir.for" == 0 &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "get_global" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.get_member" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.if" &&
  !containsSubstr raw.text "cir.while" &&
  !containsSubstr raw.text "cir.scope" &&
  noBreakContinueSwitch raw.text &&
  !hasNonHeapCall raw.text &&
  (match raw.params with
   | [p, q] =>
    !p.singleRef && !q.singleRef &&
    isPtrType p.ctype && isPtrType q.ctype &&
    (match ptrInner p.ctype, ptrInner q.ctype with
     | some i, some j => isI32 i && isI32 j
     | _, _ => false)
   | _ => false)

/-- Exact `wr_pair` admission shape (G2): the structural skeleton plus
    the dataflow pin (each add feeds its in-order store into its
    in-order param cell from that same cell). Disjoint writes commute,
    so no L2 sequencing license is needed (unlike F1); the `noalias`
    verdict gate below still demands the explicit verdict — attrs are
    claims, the verdict confirms. -/
def isWrPairShape (raw : RawFunc) : Bool :=
  structuralWrPair raw && wrPairDataflow raw.text

/-! ## G2b-admission: branch-writer recognition (`cond_pair`) -/

/-- The branch condition reads the `bool` param: the single `cir.if`
    line's operand chases to the `%arg2`-initialized alloca. -/
def condBranchPin (ls : List String) : Bool :=
  match ls.filter (fun ln => containsSubstr ln "cir.if") with
  | [ifl] =>
    match ssaOperands ifl with
    | [v] =>
      match chaseLoadAlloca ls v 8 with
      | some m => allocaArgIdx ls m == some 2
      | none => false
    | _ => false
  | _ => false

/-- Region path of a text line (`none` when the line is absent). -/
def linePath (ls : List String) (paths : List (List Nat))
    (ln : String) : Option (List Nat) :=
  let i := ls.idxOf ln
  if i < ls.length then paths[i]? else none

/-- Strict region containment via paths (the `if` line's path is a
    proper prefix of the inner line's). -/
def insideIf (pIf p : List Nat) : Bool :=
  pIf.isPrefixOf p && pIf.length < p.length

/-- Branch placement: the first writer run lies strictly inside the
    `cir.if` region, the second outside it (an unconditional second
    run would make the functionalized `q + 2` wrong; a fully
    conditional pair is a different, unadmitted shape). -/
def condBranchPlacement (ls : List String) (a1 s1 a2 s2 : String) : Bool :=
  let paths := regionPaths ls
  match ls.filter (fun ln => containsSubstr ln "cir.if") with
  | [ifl] =>
    match linePath ls paths ifl, linePath ls paths a1,
        linePath ls paths s1, linePath ls paths a2,
        linePath ls paths s2 with
    | some pIf, some pA1, some pS1, some pA2, some pS2 =>
      insideIf pIf pA1 && insideIf pIf pS1 &&
      !insideIf pIf pA2 && !insideIf pIf pS2
    | _, _, _, _, _ => false
  | _ => false

/-- Full dataflow pin for the branch-writer pair: the G2 in-order
    add→store→cell linkage (each run into its in-order param cell
    from that same cell) plus the branch pins (condition reads the
    `bool` param; first run inside the branch, second outside).
    Same-cell, swapped, cross-read, unbranched, and fully-conditional
    shapes keep their op counts but fail exactly one conjunct. -/
def condPairDataflow (text : String) : Bool :=
  let ls := text.splitOn "\n"
  let const1 := ls.filter (fun ln =>
    containsSubstr ln "cir.const #cir.int<1> : !s32i")
  let const2 := ls.filter (fun ln =>
    containsSubstr ln "cir.const #cir.int<2> : !s32i")
  let stores := ls.filter (fun ln => containsSubstr ln "cir.store align(4)")
  let adds := ls.filter (fun ln => containsSubstr ln "cir.add nsw")
  match const1, const2, stores, adds with
  | [k1], [k2], [s1, s2], [a1, a2] =>
    match ssaDefOn k1, ssaDefOn k2, ssaDefOn a1, ssaDefOn a2 with
    | some c1, some c2, some d1, some d2 =>
      match ssaOperands a1, ssaOperands a2,
          ssaOperands s1, ssaOperands s2 with
      | [e1, k1'], [e2, k2'], [v1, _], [v2, _] =>
        k1' == c1 && k2' == c2 && v1 == d1 && v2 == d2 &&
        match storeCellAlloca ls s1, storeCellAlloca ls s2 with
        | some m1, some m2 =>
          m1 != m2 && allocaArgIdx ls m1 == some 0 &&
          allocaArgIdx ls m2 == some 1 &&
          chaseLoadAlloca ls e1 8 == some m1 &&
          chaseLoadAlloca ls e2 8 == some m2 &&
          condBranchPin ls && condBranchPlacement ls a1 s1 a2 s2
        | _, _ => false
      | _, _, _, _ => false
    | _, _, _, _ => false
  | _, _, _, _ => false

/-- Structural half of branch-writer recognition: `void`, two
    non-single-reference `i32` pointer params plus a `bool`, three
    allocas, five stores (three arg inits), seven loads, exactly the
    `1`/`2` consts and two `nsw` adds, one scope-wrapped `cir.if`,
    no calls / comparisons / loops / switches / strides / members /
    cleanup / traps / globals. -/
def structuralCondPair (raw : RawFunc) : Bool :=
  raw.ret == "" &&
  opCount raw.text "cir.alloca" == 3 &&
  opCount raw.text "cir.store" == 5 &&
  opCount raw.text "cir.store %arg" == 3 &&
  opCount raw.text "cir.load" == 7 &&
  opCount raw.text "cir.const" == 2 &&
  opCount raw.text "cir.add nsw" == 2 &&
  arithOpCount raw.text == 2 &&
  opCount raw.text "cir.call @" == 0 &&
  opCount raw.text "cir.cmp" == 0 &&
  opCount raw.text "cir.for" == 0 &&
  opCount raw.text "cir.if" == 1 &&
  opCount raw.text "cir.scope" == 1 &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "get_global" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.get_member" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.while" &&
  !containsSubstr raw.text "cir.switch" &&
  !containsSubstr raw.text "cir.cond_br" &&
  noBreakContinueSwitch raw.text &&
  !hasNonHeapCall raw.text &&
  (match raw.params with
   | [p, q, c] =>
    !p.singleRef && !q.singleRef && !c.singleRef &&
    isPtrType p.ctype && isPtrType q.ctype && !isPtrType c.ctype &&
    isBoolType c.ctype &&
    (match ptrInner p.ctype, ptrInner q.ctype with
     | some i, some j => isI32 i && isI32 j
     | _, _ => false)
   | _ => false)

/-- Exact `cond_pair` admission shape (G2b): the structural skeleton
    plus the dataflow pin (in-order cells plus branch placement).
    The `noalias` verdict gate below still demands the explicit
    verdict — attrs are claims, the verdict confirms. -/
def isCondPairShape (raw : RawFunc) : Bool :=
  structuralCondPair raw && condPairDataflow raw.text

/-- Structural half of unknown-verdict branch-writer recognition
    (G3/S3): the `alias_cond` skeleton — same `void` + 3-alloca +
    5-store + `1`/`2` consts + two `nsw` adds + one scope-wrapped
    `cir.if` shape as `cond_pair`, but FIVE loads (C++ refs fuse
    the deref chain) and the C++ single-reference triple
    (`nonnull + dereferenceable + noundef`) on both writers instead
    of `noalias`. Disjoint from `structuralCondPair` on both counts
    (7 loads, triple absent there). -/
def structuralAliasCond (raw : RawFunc) : Bool :=
  raw.ret == "" &&
  opCount raw.text "cir.alloca" == 3 &&
  opCount raw.text "cir.store" == 5 &&
  opCount raw.text "cir.store %arg" == 3 &&
  opCount raw.text "cir.load" == 5 &&
  opCount raw.text "cir.const" == 2 &&
  opCount raw.text "cir.add nsw" == 2 &&
  arithOpCount raw.text == 2 &&
  opCount raw.text "cir.call @" == 0 &&
  opCount raw.text "cir.cmp" == 0 &&
  opCount raw.text "cir.for" == 0 &&
  opCount raw.text "cir.if" == 1 &&
  opCount raw.text "cir.scope" == 1 &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "get_global" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.get_member" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.while" &&
  !containsSubstr raw.text "cir.switch" &&
  !containsSubstr raw.text "cir.cond_br" &&
  noBreakContinueSwitch raw.text &&
  !hasNonHeapCall raw.text &&
  (match raw.params with
   | [p, q, c] =>
    p.singleRef && q.singleRef && !c.singleRef &&
    isPtrType p.ctype && isPtrType q.ctype && !isPtrType c.ctype &&
    isBoolType c.ctype &&
    (match ptrInner p.ctype, ptrInner q.ctype with
     | some i, some j => isI32 i && isI32 j
     | _, _ => false)
   | _ => false)

/-- Exact `alias_cond` admission shape (G3/S3): the structural twin
    above plus the SHARED dataflow pin (`condPairDataflow` already
    holds on the `alias_cond` text — same in-order cells and branch
    placement). No verdict is demanded: transfer case-splits on
    `decide (a = b)`, covering `unknown` and `mayAlias` alike. -/
def isAliasCondShape (raw : RawFunc) : Bool :=
  structuralAliasCond raw && condPairDataflow raw.text

/-! ## R1-admission: countdown reverse recognition (`vec_reverse`) -/

/-- Line indices matching a predicate (file order). -/
def linesIdxOf (ls : List String) (pred : String → Bool) : List Nat :=
  (List.range ls.length).filter (fun k => match ls[k]? with
    | some ln => pred ln | none => false)

/-- The unique line matching a predicate (`none` unless exactly one). -/
def theLineIdx (ls : List String) (pred : String → Bool) : Option Nat :=
  match linesIdxOf ls pred with
  | [k] => some k
  | _ => none

/-- Nearest preceding definition of an SSA value before a use line.
    Scope-structured CIR reuses numbers across `cir.scope` regions
    (the reverse body redefines the condition's `%7/%8/%9`), so the
    whole-text first match (`List.find?`) is unsound here: the
    correct definition is the nearest one strictly above the use. -/
def prevDefIdx (ls : List String) (useIdx v : Nat) : Option Nat :=
  (List.range useIdx).reverse.find? (fun k => match ls[k]? with
    | some ln => ssaDefOn ln == some v | none => false)

/-- Chase a use to its alloca line through single-operand definitions,
    resolving every step by nearest-preceding-definition (shadow
    sound). Multi-operand definitions resolve to nothing. -/
def chaseIdxToAlloca : List String → Nat → Nat → Nat → Option Nat
  | _, _, _, 0 => none
  | ls, useIdx, v, fuel + 1 =>
    match prevDefIdx ls useIdx v with
    | none => none
    | some d =>
      match ls[d]? with
      | none => none
      | some dln =>
        if containsSubstr dln "cir.alloca" then some d
        else match ssaOperands dln with
          | [w] => chaseIdxToAlloca ls d w fuel
          | _ => none

/-- Operands of a line by index (`[]` off the end). -/
def lineOps (ls : List String) (k : Nat) : List Nat :=
  match ls[k]? with
  | some ln => ssaOperands ln
  | none => []

/-- Call-site argument operands: the callee name glues to the first
    argument (`...2atEm(%10,`), defeating whitespace tokenization, so
    the parenthesized argument list is cut out first and split on
    commas (the `:` return annotation follows the first `)`, and CIR
    types carry no parens). -/
def callArgOps (ln : String) : List Nat :=
  let args := String.ofList
    (((ln.toList.dropWhile (· != '(')).drop 1).takeWhile (· != ')'))
  (args.splitOn ",").filterMap (fun t =>
    tokSSA (String.ofList ((t.toList.dropWhile (· == ' ')))))

/-- Call-site argument operands by line index (`[]` off the end). -/
def lineCallOps (ls : List String) (k : Nat) : List Nat :=
  match ls[k]? with
  | some ln => callArgOps ln
  | none => []

/-- The swap dataflow pin (what op counts alone cannot say): the four
    checked-`at()` sites read `(i, j, i, j)` off the vector alloca in
    file order; the first two results load into the `t` spill and the
    second read; the last two sites are stored through with the
    crossed words (`b` at `i`, reloaded `t` at `j`). Every step is
    resolved by nearest-preceding-definition, so scope renumbering
    cannot reroute a use. This rejects the near-miss shapes with
    identical op counts: same-index double writes, swapped
    read/write roles, and spill bypasses. -/
def vecReverseSwapPin (ls : List String) : Bool :=
  match theLineIdx ls (containsSubstr · "cir.alloca \"v\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"i\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"j\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"t\"") with
  | some vA, some iA, some jA, some tA =>
    match linesIdxOf ls (containsSubstr · "cir.call @_ZNSt6vectorIiSaIiEE2atEm(%"),
        linesIdxOf ls (containsSubstr · "cir.load align(4)"),
        linesIdxOf ls (containsSubstr · "cir.store align(4)") with
    | [a1, a2, a3, a4], [l1, l2, l3], [s1, s2, s3] =>
      a1 < l1 && l1 < s1 && s1 < a2 && a2 < l2 && l2 < a3 && a3 < s2 &&
        s2 < l3 && l3 < a4 && a4 < s3 &&
      match lineCallOps ls a1, lineCallOps ls a2, lineCallOps ls a3,
          lineCallOps ls a4 with
      | [v1, i1], [v2, i2], [v3, i3], [v4, i4] =>
        chaseIdxToAlloca ls a1 v1 8 == some vA &&
        chaseIdxToAlloca ls a2 v2 8 == some vA &&
        chaseIdxToAlloca ls a3 v3 8 == some vA &&
        chaseIdxToAlloca ls a4 v4 8 == some vA &&
        chaseIdxToAlloca ls a1 i1 8 == some iA &&
        chaseIdxToAlloca ls a2 i2 8 == some jA &&
        chaseIdxToAlloca ls a3 i3 8 == some iA &&
        chaseIdxToAlloca ls a4 i4 8 == some jA &&
        match lineOps ls l1, lineOps ls l2, lineOps ls l3 with
        | [w1], [w2], [w3] =>
          prevDefIdx ls l1 w1 == some a1 &&
          prevDefIdx ls l2 w2 == some a2 &&
          prevDefIdx ls l3 w3 == some tA &&
          match lineOps ls s1, lineOps ls s2, lineOps ls s3 with
          | [u1, p1], [u2, p2], [u3, p3] =>
            prevDefIdx ls s1 u1 == some l1 &&
            prevDefIdx ls s1 p1 == some tA &&
            prevDefIdx ls s2 u2 == some l2 &&
            prevDefIdx ls s2 p2 == some a3 &&
            prevDefIdx ls s3 u3 == some l3 &&
            prevDefIdx ls s3 p3 == some a4
          | _, _, _ => false
        | _, _, _ => false
      | _, _, _, _ => false
    | _, _, _ => false
  | _, _, _, _ => false

/-- Index-skeleton pin: the `lt` guard compares the `i` cell against
    the `j` cell (in order); `inc` feeds `i`, `dec` feeds `j`; the
    `i` cell is zero-initialized and `inc`-updated, the `j` cell is
    size-initialized and `dec`-updated (file order: init before
    writeback). -/
def vecReverseIndexPin (ls : List String) : Bool :=
  match theLineIdx ls (containsSubstr · "cir.cmp lt"),
      theLineIdx ls (containsSubstr · "cir.inc "),
      theLineIdx ls (containsSubstr · "cir.dec "),
      theLineIdx ls (containsSubstr · "cir.alloca \"i\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"j\""),
      theLineIdx ls (containsSubstr · "cir.const #cir.int<0> : !u64i"),
      theLineIdx ls (containsSubstr · "cir.call @_ZNKSt6vectorIiSaIiEE4sizeEv(%") with
  | some ci, some ni, some di, some iA, some jA, some zA, some sA =>
    match lineOps ls ci, lineOps ls ni, lineOps ls di with
    | [a, b], [x], [y] =>
      chaseIdxToAlloca ls ci a 8 == some iA &&
      chaseIdxToAlloca ls ci b 8 == some jA &&
      chaseIdxToAlloca ls ni x 8 == some iA &&
      chaseIdxToAlloca ls di y 8 == some jA &&
      match (linesIdxOf ls (containsSubstr · "cir.store align(8)")).filter
          (fun k => match lineOps ls k with | [_, d] => d == 1 | _ => false),
        (linesIdxOf ls (containsSubstr · "cir.store align(8)")).filter
          (fun k => match lineOps ls k with | [_, d] => d == 2 | _ => false) with
      | [si0, si1], [sj0, sj1] =>
        match lineOps ls si0, lineOps ls si1,
            lineOps ls sj0, lineOps ls sj1 with
        | [vi0, _], [vi1, _], [vj0, _], [vj1, _] =>
          prevDefIdx ls si0 vi0 == some zA &&
          prevDefIdx ls si1 vi1 == some ni &&
          prevDefIdx ls sj0 vj0 == some sA &&
          prevDefIdx ls sj1 vj1 == some di
        | _, _, _, _ => false
      | _, _ => false
    | _, _, _ => false
  | _, _, _, _, _, _, _ => false

/-- Structural half of reverse recognition: `void`, single
    single-reference vector param, one `size` + four checked-`at()`
    calls, one `while` (`lt` guard, `inc`/`dec` updates, `t` spill),
    no branches/switches/EH/division/traps/globals. -/
def structuralVecReverse (raw : RawFunc) : Bool :=
  raw.ret == "" &&
  opCount raw.text "cir.call @" == 5 &&
  callsFunc raw.text stdVecSizeName &&
  opCount raw.text "cir.call @_ZNSt6vectorIiSaIiEE2atEm(" == 4 &&
  opCount raw.text "cir.while" == 1 &&
  opCount raw.text "cir.cmp" == 1 &&
  opCount raw.text "cir.cmp lt" == 1 &&
  opCount raw.text "cir.condition" == 1 &&
  opCount raw.text "cir.const" == 2 &&
  containsSubstr raw.text "#cir.int<0>" &&
  opCount raw.text "cir.alloca" == 4 &&
  opCount raw.text "cir.load" == 16 &&
  opCount raw.text "cir.store" == 8 &&
  opCount raw.text "cir.load align(4)" == 3 &&
  opCount raw.text "cir.store align(4)" == 3 &&
  opCount raw.text "cir.store align(8)" == 4 &&
  opCount raw.text "cir.return" == 1 &&
  opCount raw.text "cir.inc" == 1 &&
  opCount raw.text "cir.dec" == 1 &&
  opCount raw.text "cir.scope" == 2 &&
  opCount raw.text "cir.yield" == 1 &&
  !callsFunc raw.text raw.name &&
  !callsFunc raw.text stdVecIndexName &&
  !callsFunc raw.text stdVecRangeCheckName &&
  !callsFunc raw.text stdVecRangeCheckThrowName &&
  !containsSubstr raw.text "cir.if" &&
  !containsSubstr raw.text "cir.for" &&
  !containsSubstr raw.text "cir.switch" &&
  !containsSubstr raw.text "cir.try" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "cir.div" &&
  !containsSubstr raw.text "cir.unreachable" &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.get_member" &&
  !containsSubstr raw.text "cir.get_global" &&
  !containsSubstr raw.text "cir.get_element" &&
  !containsSubstr raw.text "cir.cast" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.do" &&
  !containsSubstr raw.text "cir.cond_br" &&
  !containsSubstr raw.text "cir.sub " &&
  !containsSubstr raw.text "cir.add " &&
  !containsSubstr raw.text "cir.shift" &&
  !containsSubstr raw.text "cir.cmp eq" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.ptr_diff" &&
  noBreakContinueSwitch raw.text &&
  (match raw.params with
   | [v] =>
    isPtrType v.ctype && v.singleRef && isStdVectorType v.ctype
   | _ => false)

/-- Index-skeleton pin, segment variant: the `lt` guard compares
    the `i` cell against the `j` cell (in order); `inc` feeds `i`,
    `dec` feeds `j`; the `i` cell is `lo`-initialized (copy chain
    through the `lo` alloca) and `inc`-updated, the `j` cell is
    `hi`-initialized (copy chain through the `hi` alloca) and
    `dec`-updated. Store lines are classified by chasing the
    destination to its alloca (no SSA literals — scope renumbering
    cannot reroute a use). -/
def vecSegReverseIndexPin (ls : List String) : Bool :=
  match theLineIdx ls (containsSubstr · "cir.cmp lt"),
      theLineIdx ls (containsSubstr · "cir.inc "),
      theLineIdx ls (containsSubstr · "cir.dec "),
      theLineIdx ls (containsSubstr · "cir.alloca \"i\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"j\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"lo\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"hi\"") with
  | some ci, some ni, some di, some iA, some jA, some loA, some hiA =>
    match lineOps ls ci, lineOps ls ni, lineOps ls di with
    | [a, b], [x], [y] =>
      chaseIdxToAlloca ls ci a 8 == some iA &&
      chaseIdxToAlloca ls ci b 8 == some jA &&
      chaseIdxToAlloca ls ni x 8 == some iA &&
      chaseIdxToAlloca ls di y 8 == some jA &&
      match ((linesIdxOf ls (containsSubstr · "cir.store align(8)")).filter
          (fun k => match lineOps ls k with
            | [_, d] => chaseIdxToAlloca ls k d 8 == some iA
            | _ => false)),
          ((linesIdxOf ls (containsSubstr · "cir.store align(8)")).filter
          (fun k => match lineOps ls k with
            | [_, d] => chaseIdxToAlloca ls k d 8 == some jA
            | _ => false)) with
      | [si0, si1], [sj0, sj1] =>
        match lineOps ls si0, lineOps ls si1,
            lineOps ls sj0, lineOps ls sj1 with
        | [vi0, _], [vi1, _], [vj0, _], [vj1, _] =>
          chaseIdxToAlloca ls si0 vi0 8 == some loA &&
          prevDefIdx ls si1 vi1 == some ni &&
          chaseIdxToAlloca ls sj0 vj0 8 == some hiA &&
          prevDefIdx ls sj1 vj1 == some di
        | _, _, _, _ => false
      | _, _ => false
    | _, _, _ => false
  | _, _, _, _, _, _, _ => false

/-- Structural half of segment-reverse recognition: `void`, one
    single-reference vector + two owned `u64` params, four
    checked-`at()` calls and no `size` call, one `while` (`lt`
    guard, `inc`/`dec` updates, `t` spill), no materialized
    constants (the prelude copies `lo`/`hi`), no
    branches/switches/EH/division/traps/globals. -/
def structuralVecSegReverse (raw : RawFunc) : Bool :=
  raw.ret == "" &&
  opCount raw.text "cir.call @" == 4 &&
  callsFunc raw.text stdVecAtMutName &&
  opCount raw.text "cir.call @_ZNSt6vectorIiSaIiEE2atEm(" == 4 &&
  !callsFunc raw.text stdVecSizeName &&
  opCount raw.text "cir.while" == 1 &&
  opCount raw.text "cir.cmp" == 1 &&
  opCount raw.text "cir.cmp lt" == 1 &&
  opCount raw.text "cir.condition" == 1 &&
  !containsSubstr raw.text "cir.const" &&
  opCount raw.text "cir.alloca" == 6 &&
  opCount raw.text "cir.load" == 17 &&
  opCount raw.text "cir.store" == 10 &&
  opCount raw.text "cir.load align(4)" == 3 &&
  opCount raw.text "cir.store align(4)" == 3 &&
  opCount raw.text "cir.store align(8)" == 4 &&
  opCount raw.text "cir.return" == 1 &&
  opCount raw.text "cir.inc" == 1 &&
  opCount raw.text "cir.dec" == 1 &&
  opCount raw.text "cir.scope" == 2 &&
  opCount raw.text "cir.yield" == 1 &&
  !callsFunc raw.text raw.name &&
  !callsFunc raw.text stdVecIndexName &&
  !callsFunc raw.text stdVecRangeCheckName &&
  !callsFunc raw.text stdVecRangeCheckThrowName &&
  !containsSubstr raw.text "cir.if" &&
  !containsSubstr raw.text "cir.for" &&
  !containsSubstr raw.text "cir.switch" &&
  !containsSubstr raw.text "cir.try" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "cir.div" &&
  !containsSubstr raw.text "cir.unreachable" &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.get_member" &&
  !containsSubstr raw.text "cir.get_global" &&
  !containsSubstr raw.text "cir.get_element" &&
  !containsSubstr raw.text "cir.cast" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.do" &&
  !containsSubstr raw.text "cir.cond_br" &&
  !containsSubstr raw.text "cir.sub " &&
  !containsSubstr raw.text "cir.add " &&
  !containsSubstr raw.text "cir.shift" &&
  !containsSubstr raw.text "cir.cmp eq" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.ptr_diff" &&
  noBreakContinueSwitch raw.text &&
  (match raw.params with
   | [v, lo, hi] =>
    isPtrType v.ctype && v.singleRef && isStdVectorType v.ctype &&
    isU64 lo.ctype && isU64 hi.ctype
   | _ => false)

/-- Exact `vec_seg_reverse` admission shape (S1): the structural
    skeleton (window opened by owned `lo`/`hi` params — no `size`
    call, no materialized constants) plus the shared swap dataflow
    pin (the loop body is line-identical to the whole-range
    reverse) plus the segment index-skeleton pin (`i` up from
    `lo`, `j` down from `hi`). Verdict honestly `unknown`
    (single-ref). -/
def isVecSegReverseShape (raw : RawFunc) : Bool :=
  structuralVecSegReverse raw &&
  vecReverseSwapPin (raw.text.splitOn "\n") &&
  vecSegReverseIndexPin (raw.text.splitOn "\n")

/-- The SSA value is defined by a `u64` zero constant (nearest-
    preceding-definition resolves to the materialized `cir.const`
    `#cir.int<0> : !u64i` line). -/
def isU64ZeroDef (ls : List String) (useIdx v : Nat) : Bool :=
  match prevDefIdx ls useIdx v with
  | some d => match ls[d]? with
    | some dln => containsSubstr dln "cir.const" &&
      containsSubstr dln "!u64i" && containsSubstr dln "<0>"
    | none => false
  | none => false

/-- The SSA value is defined by a load whose single operand chases
    to the expected alloca (nearest-preceding-definition + the
    scope-safe alloca chase). -/
def isAllocaLoadDef (ls : List String) (useIdx v alloca : Nat) : Bool :=
  match prevDefIdx ls useIdx v with
  | some d => match ls[d]? with
    | some dln => containsSubstr dln "cir.load" &&
      match ssaOperands dln with
      | [w] => chaseIdxToAlloca ls d w 8 == some alloca
      | _ => false
    | none => false
  | none => false

/-- The call-wiring pin (what op counts alone cannot say): one
    `size` call off the vector alloca whose result is stored to the
    `n` alloca (the unique `align(8)` store), then three
    `vec_seg_reverse` calls in file order with `(v, 0, k)`,
    `(v, k, n)`, `(v, 0, n)` wiring — zero args resolve to the
    materialized `u64` constants, every other arg to an alloca
    load. Every step is resolved by nearest-preceding-definition,
    so scope renumbering cannot reroute a use. This rejects the
    near-miss shapes with identical op counts: permuted call
    order, swapped bounds, and size-bypassed windows. -/
def vecRotateCallPin (ls : List String) : Bool :=
  match theLineIdx ls (containsSubstr · "cir.alloca \"v\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"k\""),
      theLineIdx ls (containsSubstr · "cir.alloca \"n\""),
      theLineIdx ls
        (containsSubstr · "cir.call @_ZNKSt6vectorIiSaIiEE4sizeEv(%") with
  | some vA, some kA, some nA, some sZ =>
    match linesIdxOf ls
        (containsSubstr · "cir.call @_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm(%") with
    | [c1, c2, c3] =>
      sZ < c1 && c1 < c2 && c2 < c3 &&
      match lineCallOps ls sZ with
      | [sv] =>
        chaseIdxToAlloca ls sZ sv 8 == some vA &&
        match theLineIdx ls (containsSubstr · "cir.store align(8)") with
        | some st =>
          match lineOps ls st with
          | [r, d] =>
            prevDefIdx ls st r == some sZ &&
            chaseIdxToAlloca ls st d 8 == some nA &&
            match lineCallOps ls c1, lineCallOps ls c2,
                lineCallOps ls c3 with
            | [v1, a1, b1], [v2, k1, n1], [v3, a2, b2] =>
              chaseIdxToAlloca ls c1 v1 8 == some vA &&
              chaseIdxToAlloca ls c2 v2 8 == some vA &&
              chaseIdxToAlloca ls c3 v3 8 == some vA &&
              isU64ZeroDef ls c1 a1 &&
              isU64ZeroDef ls c3 a2 &&
              isAllocaLoadDef ls c1 b1 kA &&
              isAllocaLoadDef ls c2 k1 kA &&
              isAllocaLoadDef ls c2 n1 nA &&
              isAllocaLoadDef ls c3 b2 nA
            | _, _, _ => false
          | _ => false
        | none => false
      | _ => false
    | _ => false
  | _, _, _, _ => false

/-- Structural half of rotate recognition: `void`, one
    single-reference vector + one owned `u64` param, one `size`
    call + three `vec_seg_reverse` calls (no direct `at()` calls —
    all words flow through the admitted callee), the two
    materialized zero constants, no loop, no branches/EH/
    arithmetic/traps/globals. -/
def structuralVecRotate (raw : RawFunc) : Bool :=
  raw.ret == "" &&
  opCount raw.text "cir.call @" == 4 &&
  callsFunc raw.text stdVecSizeName &&
  opCount raw.text "cir.call @_ZNKSt6vectorIiSaIiEE4sizeEv(" == 1 &&
  callsFunc raw.text vecSegReverseName &&
  opCount raw.text "cir.call @_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm(" == 3 &&
  !callsFunc raw.text stdVecAtMutName &&
  !callsFunc raw.text raw.name &&
  !callsFunc raw.text stdVecIndexName &&
  !callsFunc raw.text stdVecRangeCheckName &&
  !callsFunc raw.text stdVecRangeCheckThrowName &&
  opCount raw.text "cir.while" == 0 &&
  opCount raw.text "cir.const" == 4 &&
  opCount raw.text "cir.alloca" == 3 &&
  opCount raw.text "cir.load" == 8 &&
  opCount raw.text "cir.store" == 3 &&
  opCount raw.text "cir.load align(8)" == 4 &&
  opCount raw.text "cir.store align(8)" == 1 &&
  opCount raw.text "cir.return" == 1 &&
  !containsSubstr raw.text "cir.if" &&
  !containsSubstr raw.text "cir.for" &&
  !containsSubstr raw.text "cir.switch" &&
  !containsSubstr raw.text "cir.try" &&
  !containsSubstr raw.text "cir.trap" &&
  !containsSubstr raw.text "cir.div" &&
  !containsSubstr raw.text "cir.unreachable" &&
  !containsSubstr raw.text "cir.cleanup" &&
  !containsSubstr raw.text "cir.get_member" &&
  !containsSubstr raw.text "cir.get_global" &&
  !containsSubstr raw.text "cir.get_element" &&
  !containsSubstr raw.text "cir.cast" &&
  !containsSubstr raw.text "cir.ternary" &&
  !containsSubstr raw.text "cir.do" &&
  !containsSubstr raw.text "cir.cond_br" &&
  !containsSubstr raw.text "cir.sub " &&
  !containsSubstr raw.text "cir.add " &&
  !containsSubstr raw.text "cir.shift" &&
  !containsSubstr raw.text "cir.cmp" &&
  !containsSubstr raw.text "cir.condition" &&
  !containsSubstr raw.text "cir.inc" &&
  !containsSubstr raw.text "cir.dec" &&
  !containsSubstr raw.text "cir.scope" &&
  !containsSubstr raw.text "cir.yield" &&
  !containsSubstr raw.text "cir.ptr_stride" &&
  !containsSubstr raw.text "cir.ptr_diff" &&
  noBreakContinueSwitch raw.text &&
  (match raw.params with
   | [v, k] =>
    isPtrType v.ctype && v.singleRef && isStdVectorType v.ctype &&
    isU64 k.ctype
   | _ => false)

/-- Exact `vec_rotate` admission shape (R1): the structural skeleton
    (one `size` call, three `vec_seg_reverse` calls, two
    materialized zeros, no loop) plus the call-wiring dataflow pin
    (`(v, 0, k)`, `(v, k, n)`, `(v, 0, n)` in order off the right
    allocas). Verdict honestly `unknown` (single-ref). -/
def isVecRotateShape (raw : RawFunc) : Bool :=
  structuralVecRotate raw &&
  vecRotateCallPin (raw.text.splitOn "\n")

/-- Exact `vec_reverse` admission shape (R1): the structural skeleton
    plus the swap dataflow pin (in-order checked sites with crossed
    words) plus the index-skeleton pin (`i` up from zero, `j` down
    from size). The single `mutBorrow`ed vector is the only pointer
    param, so no verdict beyond the triple is demanded (the
    `vec_at_set` precedent: oracle governance vacuous, verdict
    honestly `unknown`). -/
def isVecReverseShape (raw : RawFunc) : Bool :=
  structuralVecReverse raw &&
  vecReverseSwapPin (raw.text.splitOn "\n") &&
  vecReverseIndexPin (raw.text.splitOn "\n")

/-- Soundness of the L2 admission predicate: `true` yields the three
    recorded locals with the first writer's range ending strictly
    before the second writer's begins. Admission will consume exactly
    this fact. -/
theorem hasSequentialWriterRanges_disjoint (text : String)
    (h : hasSequentialWriterRanges text = true) :
    ∃ r a b : LocalDecl, (extractScopes text).locals = [r, a, b] ∧
      0 < a.lastUse ∧ a.lastUse < b.firstUse := by
  -- Case on the locals BEFORE unfolding: `h` mentions `text` only, so
  -- no dependent motive over the scrutinee (casing after `unfold`
  -- fails dependent elimination on the `decide` match arms).
  cases hl : (extractScopes text).locals with
  | nil =>
    have h2 : hasSequentialWriterRanges text = true := h
    unfold hasSequentialWriterRanges at h2
    rw [hl] at h2
    simp at h2
  | cons r rest =>
    cases rest with
    | nil =>
      have h2 : hasSequentialWriterRanges text = true := h
      unfold hasSequentialWriterRanges at h2
      rw [hl] at h2
      simp at h2
    | cons a rest₂ =>
      cases rest₂ with
      | nil =>
        have h2 : hasSequentialWriterRanges text = true := h
        unfold hasSequentialWriterRanges at h2
        rw [hl] at h2
        simp at h2
      | cons b rest₃ =>
        cases rest₃ with
        | cons _ _ =>
          have h2 : hasSequentialWriterRanges text = true := h
          unfold hasSequentialWriterRanges at h2
          rw [hl] at h2
          simp at h2
        | nil =>
          have h2 : hasSequentialWriterRanges text = true := h
          unfold hasSequentialWriterRanges at h2
          rw [hl] at h2
          simp at h2
          -- `simp_all`: robust to the exact normal form — `hl` rewrites
          -- the locals equation, `h2`'s split conjuncts supply the two
          -- range facts (casing or projecting the `Nat.le` conjunct
          -- trips dependent elimination over the `Nat` indices).
          refine ⟨r, a, b, ?_, ?_, ?_⟩ <;> simp_all

/-- The full recognition shape carries the disjointness fact: anything
    the gate routes to the deferred message satisfies the admission
    predicate. -/
theorem isSequentialReborrowShape_disjoint (raw : RawFunc)
    (h : isSequentialReborrowShape raw = true) :
    ∃ r a b : LocalDecl, (extractScopes raw.text).locals = [r, a, b] ∧
      0 < a.lastUse ∧ a.lastUse < b.firstUse := by
  -- Project the trailing L2 conjunct (one projection, robust to the
  -- structural chain's length: casing the chain trips dependent
  -- elimination against the nested matches).
  have hr : hasSequentialWriterRanges raw.text = true := by
    have h2 := h
    unfold isSequentialReborrowShape at h2
    simp only [Bool.and_eq_true] at h2
    exact h2.2
  exact hasSequentialWriterRanges_disjoint _ hr

