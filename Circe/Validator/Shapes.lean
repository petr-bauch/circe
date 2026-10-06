/-
Circe.Validator.Shapes — S2/M2a/N4a/N4c/N4d-i/ii/iii admitted shapes,
over `Circe.Validator.Features`.
-/
import Circe.CoreIR
import Circe.Parser
import Circe.Oracle
import Circe.Emit
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose
import Circe.Validator.Features

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

/-! ## N7a: `std::string_view` range-for sum shapes -/

/-- Canonical signed-8 spellings (`!s8i` alias or long form) — the
    viewed byte type (cf. `isI32`). -/
def isS8 (t : String) : Bool :=
  t == "!s8i" || t == "!cir.int<s, 8>" || t == "!cir.int<s,8>"

/-- The `std::string_view` object type (CIRGen's
    `!rec_std3A3Abasic_string_view…` alias; the `char` /
    `char_traits<char>` instantiation is part of the admitted
    monomorph, the N4c monomorphization precedent). -/
def isViewType (t : String) : Bool :=
  containsSubstr t "string_view"

/-- The `begin` iterator leaf: single `const&` to the view object
    with the single-reference triple, pointer-to-`s8` return, the
    single `get_member` (`_M_str`) projection with the base load,
    no calls, no control flow, no stride. -/
def isViewBeginShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef && isViewType this.ctype &&
    (match ptrInner raw.ret with | some inner => isS8 inner | none => false) &&
    opCount raw.text "cir.get_member" == 1 &&
    containsSubstr raw.text "_M_str" &&
    opCount raw.text "cir.load" == 3 &&
    opCount raw.text "cir.call @" == 0 &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable" &&
    !containsSubstr raw.text "cir.ptr_stride"
  | _ => false

/-- The `end` iterator leaf: single `const&` with the
    single-reference triple, pointer-to-`s8` return, the two
    `get_member` projections (`_M_str` + `_M_len`) with the base /
    length loads fused by the single `u64`-stride `ptr_stride`,
    no calls, no control flow. -/
def isViewEndShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [this] =>
    noBreakContinueSwitch raw.text &&
    isPtrType this.ctype && this.singleRef && isViewType this.ctype &&
    (match ptrInner raw.ret with | some inner => isS8 inner | none => false) &&
    opCount raw.text "cir.get_member" == 2 &&
    containsSubstr raw.text "_M_str" &&
    containsSubstr raw.text "_M_len" &&
    opCount raw.text "cir.load" == 4 &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    containsSubstr raw.text "(!cir.ptr<!s8i>, !u64i)" &&
    opCount raw.text "cir.call @" == 0 &&
    !callsFunc raw.text raw.name &&
    !containsSubstr raw.text "cir.call @malloc" &&
    !containsSubstr raw.text "cir.call @free(" &&
    !containsSubstr raw.text "cir.add nsw" &&
    !containsSubstr raw.text "cir.cast" &&
    !containsSubstr raw.text "cir.ternary" &&
    !containsSubstr raw.text "cir.for" &&
    !containsSubstr raw.text "cir.if" &&
    !containsSubstr raw.text "cir.while" &&
    !containsSubstr raw.text "cir.cond_br" &&
    !containsSubstr raw.text "cir.do" &&
    !containsSubstr raw.text "cir.unreachable"
  | _ => false

/-- The `view_sum` range-for entry: the view **by value** (no
    pointer, no aliasing question on the object itself — the viewed
    bytes are a `sharedBorrow` snapshot downstream), `i32` return,
    exactly two call sites (`begin` + `end`), the single `cir.for`
    with the pointer `ne` comparison, the `s32`-stride advance, the
    `s8i` element load + integral `s8i -> s32i` sext, and the one
    `nsw` accumulation add. Two `cir.const` (the `0` init + the
    stray `1` stride, both live), no projections of its own. -/
def isViewSumShape (raw : RawFunc) : Bool :=
  match raw.params with
  | [s] =>
    noBreakContinueSwitch raw.text &&
    !isPtrType s.ctype && isViewType s.ctype &&
    isI32 raw.ret &&
    callsFunc raw.text viewBeginName &&
    callsFunc raw.text viewEndName &&
    opCount raw.text "cir.call @" == 2 &&
    !callsFunc raw.text raw.name &&
    opCount raw.text "cir.for" == 1 &&
    opCount raw.text "cir.cmp" == 1 &&
    containsSubstr raw.text "cir.cmp ne" &&
    containsSubstr raw.text "!cir.ptr<!s8i>" &&
    opCount raw.text "cir.condition" == 1 &&
    opCount raw.text "cir.ptr_stride" == 1 &&
    containsSubstr raw.text "(!cir.ptr<!s8i>, !s32i)" &&
    opCount raw.text "cir.load align(1)" == 2 &&
    opCount raw.text "cir.cast" == 1 &&
    containsSubstr raw.text "!s8i -> !s32i" &&
    opCount raw.text "cir.add nsw" == 1 &&
    opCount raw.text "cir.const" == 2 &&
    containsSubstr raw.text "#cir.int<0>" &&
    containsSubstr raw.text "#cir.int<1>" &&
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
    !containsSubstr raw.text "cir.base_class_addr"
  | _ => false

/-- Known `std::string_view` leaf callees (mangled): the `begin` /
    `end` iterator leaves. Entry gates admit calls into the
    (name, arity, site-count) pairs named in `validate` below; this
    registry names every known view leaf for the wrong-shape
    rejection. -/
def viewLeafCallees : List String :=
  [viewBeginName, viewEndName]

/-- Calls a known `std::string_view` leaf but not with an admitted
    (name, arity, site-count) shape: dedicated rejection naming the
    admitted shapes. -/
def callsViewWrongShape (raw : RawFunc) : Bool :=
  viewLeafCallees.any (callsFunc raw.text)

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

