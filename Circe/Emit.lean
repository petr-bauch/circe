/-
Circe.Emit — verified emitter `CoreIR → Lean` (facade).

Fragment definitions and proofs live in `Circe.Emit.*` (`Fragment`, `Add`,
`Choose`, `Sum`, `Vec`, `Vec64`, `Vec2`, `VecRealloc`, `Calls`, `Struct`,
`Method`, `Acc`, `Move`, `Flow`, `VecGrow`); shape
recognition in `Circe.Emit.Match`; file-text and spec-stub rendering in
`Circe.Emit.Render` / `Circe.Emit.SpecStubs`. This module wires them
together (`emitSpec`, `emitFunc`, `emitFunc_rejects`) and holds the golden
linkage. Everything downstream (`Circe.Validator`, `Circe.Tactics`,
`Circe.Specs`, `tools/GenOut.lean`) keeps importing `Circe.Emit` and sees
the whole fragment closure transitively.

Trust note: the *rendering* (Value-tag erasure to `BitVec` text) is
trusted, like the parser; what is verified is that the rendered
definitions have exactly the semantics of `evalFunc` on the fragment.
`tools/check.sh` regenerates the outputs and `diff`s them against
the checked-in goldens (`tests/golden/*.lean`, also spot-checked by the
`native_decide` examples below on clean builds), and `lake env lean`
typechecks the rendered files.
-/
import Circe.Emit.Match
import Circe.Emit.Render
import Circe.Emit.SpecStubs

/-- The spec emitter: accepted fragment renders to stub text; everything
    else is rejected loudly (never silently modeled). -/
def emitSpec (f : Func) : Except EmitError String :=
  match matchFrag f with
  | some .add => .ok (emitAddSpecText f.name)
  | some .add64 => .ok (emitAdd64SpecText f.name)
  | some .addu64 => .ok (emitAddu64SpecText f.name)
  | some .neg => .ok (emitNegSpecText f.name)
  | some .sdiv => .ok (emitSdivSpecText f.name)
  | some .incr => .ok (emitIncrSpecText f.name)
  | some .choose => .ok (emitChooseSpecText f.name)
  | some .sum => .ok (emitSumSpecText f.name)
  | some .vec => .ok (emitVecSpecText f.name)
  | some .vec64 => .ok (emitVec64SpecText f.name)
  | some .vec2 => .ok (emitVec2SpecText f.name)
  | some .vecRealloc => .ok (emitVecReallocSpecText f.name)
  | some .addCall => .ok (emitAddCallerSpecText f.name)
  | some .add3 => .ok (emitAdd3SpecText f.name)
  | some .useAdd => .ok (emitUseAddSpecText f.name)
  | some .useNsAdd => .ok (emitUseNsAddSpecText f.name)
  | some .useTadd32 => .ok (emitUseTadd32SpecText f.name)
  | some .useTadd64 => .ok (emitUseTadd64SpecText f.name)
  | some .arrayRef => .ok (emitArrayRefSpecText f.name)
  | some .arrayAt => .ok (emitArrayAtSpecText f.name)
  | some .arraySum => .ok (emitArraySumSpecText f.name)
  | some .optHas => .ok (emitOptHasSpecText f.name)
  | some .optHasValue => .ok (emitOptHasValueSpecText f.name)
  | some .optGet => .ok (emitOptGetSpecText f.name)
  | some .optImplGet => .ok (emitOptImplGetSpecText f.name)
  | some .optDerefOp => .ok (emitOptDerefOpSpecText f.name)
  | some .optDeref => .ok (emitOptDerefSpecText f.name)
  | some .spanExtent => .ok (emitSpanExtentSpecText f.name)
  | some .spanSize => .ok (emitSpanSizeSpecText f.name)
  | some .spanIndex => .ok (emitSpanIndexSpecText f.name)
  | some .spanSum => .ok (emitSpanSumSpecText f.name)
  | some .vecSize => .ok (emitStdVecSizeSpecText f.name)
  | some .vecIndex => .ok (emitStdVecIndexSpecText f.name)
  | some .vecReadSum => .ok (emitStdVecReadSumSpecText f.name)
  | some .vecEmptyCtor => .ok (emitStdVecEmptyCtorSpecText f.name)
  | some .vecUnit => .ok (emitStdVecUnitSpecText f.name)
  | some .vecDtor => .ok (emitStdVecDtorSpecText f.name)
  | some .vecDestroyNoop => .ok (emitStdVecDestroyNoopSpecText f.name)
  | some .vecDestroyPtr => .ok (emitStdVecDestroyPtrSpecText f.name)
  | some .vecGetTp => .ok (emitStdVecGetTpSpecText f.name)
  | some .vecDiffMax => .ok (emitStdVecDiffMaxSpecText f.name)
  | some .vecMax => .ok (emitStdVecMaxSpecText f.name)
  | some .vecMin => .ok (emitStdVecMinSpecText f.name)
  | some .vecCheckLen => .ok (emitStdVecCheckLenSpecText f.name)
  | some .vecBegin => .ok (emitStdVecBeginSpecText f.name)
  | some .vecEnd => .ok (emitStdVecEndSpecText f.name)
  | some .vecBack => .ok (emitStdVecBackSpecText f.name)
  | some .vecIterId => .ok (emitStdVecIterIdSpecText f.name)
  | some .vecMinusEl => .ok (emitStdVecMinusElSpecText f.name)
  | some .vecMinus => .ok (emitStdVecMinusSpecText f.name)
  | some .vecAlloc => .ok (emitStdVecAllocSpecText f.name)
  | some .vecDealloc => .ok (emitStdVecDeallocSpecText f.name)
  | some .vecDeallocGuard => .ok (emitStdVecDeallocGuardSpecText f.name)
  | some .vecConstruct => .ok (emitStdVecConstructSpecText f.name)
  | some .vecReloc => .ok (emitStdVecRelocSpecText f.name)
  | some .vecGrowRealloc => .ok (emitStdVecGrowReallocSpecText f.name)
  | some .vecEmplaceBack => .ok (emitStdVecEmplaceBackSpecText f.name)
  | some .vecPushBack => .ok (emitStdVecPushBackSpecText f.name)
  | some .vecPushSumEntry => .ok (emitVecPushSumEntrySpecText f.name)
  | some .sumCall => .ok (emitSumCallerSpecText f.name)
  | some .translate => .ok (emitTranslateSpecText f.name)
  | some .methodSum => .ok (emitMethodSumSpecText f.name)
  | some .pointSumRef => .ok (emitPointSumRefSpecText f.name)
  | some .accCtor => .ok (emitAccCtorSpecText f.name)
  | some .accAdd => .ok (emitAccAddSpecText f.name)
  | some .accGet => .ok (emitAccGetSpecText f.name)
  | some .accDtor => .ok (emitAccDtorSpecText f.name)
  | some .accTwo => .ok (emitAccTwoSpecText f.name)
  | some .accMoveCtor => .ok (emitAccMoveCtorSpecText f.name)
  | some .moveAcc => .ok (emitMoveAccSpecText f.name)
  | some .scopeEarly => .ok (emitScopeEarlySpecText f.name)
  | some .boxThrough => .ok (emitBoxThroughSpecText f.name)
  | some .nested => .ok (emitNestedSpecText f.name)
  | some .skip => .ok (emitSkipSpecText f.name)
  | some .findEq => .ok (emitFindEqSpecText f.name)
  | some .cls => .ok (emitClsSpecText f.name)
  | some .clsFall => .ok (emitClsFallSpecText f.name)
  | some .clsDense => .ok (emitClsDenseSpecText f.name)
  | some .clsBreak => .ok (emitClsBreakSpecText f.name)
  | none => .error (.notFragment s!"not in the admitted fragment: {f.name}")

/-- The emitter: accepted fragment renders to file text; everything else
    is rejected loudly (never silently modeled). -/
def emitFunc (f : Func) : Except EmitError EmittedFunc :=
  match matchFrag f with
  | some .add => .ok ⟨emitAddText f.name, none⟩
  | some .add64 => .ok ⟨emitAdd64Text f.name, none⟩
  | some .addu64 => .ok ⟨emitAddu64Text f.name, none⟩
  | some .neg => .ok ⟨emitNegText f.name, none⟩
  | some .sdiv => .ok ⟨emitSdivText f.name, none⟩
  | some .incr => .ok ⟨emitIncrText f.name, none⟩
  | some .choose =>
    .ok ⟨emitChooseFwdText f.name, some (emitChooseBackText f.name)⟩
  | some .sum => .ok ⟨emitSumText f.name, none⟩
  | some .vec => .ok ⟨emitVecText f.name, none⟩
  | some .vec64 => .ok ⟨emitVec64Text f.name, none⟩
  | some .vec2 => .ok ⟨emitVec2Text f.name, none⟩
  | some .vecRealloc => .ok ⟨emitVecReallocText f.name, none⟩
  | some .addCall => .ok ⟨emitAddCallerText f.name, none⟩
  | some .add3 => .ok ⟨emitAdd3Text f.name, none⟩
  | some .useAdd => .ok ⟨emitUseAddText f.name, none⟩
  | some .useNsAdd => .ok ⟨emitUseNsAddText f.name, none⟩
  | some .useTadd32 => .ok ⟨emitUseTadd32Text f.name, none⟩
  | some .useTadd64 => .ok ⟨emitUseTadd64Text f.name, none⟩
  | some .arrayRef => .ok ⟨emitArrayRefText f.name, none⟩
  | some .arrayAt => .ok ⟨emitArrayAtText f.name, none⟩
  | some .arraySum => .ok ⟨emitArraySumText f.name, none⟩
  | some .optHas => .ok ⟨emitOptHasText f.name, none⟩
  | some .optHasValue => .ok ⟨emitOptHasValueText f.name, none⟩
  | some .optGet => .ok ⟨emitOptGetText f.name, none⟩
  | some .optImplGet => .ok ⟨emitOptImplGetText f.name, none⟩
  | some .optDerefOp => .ok ⟨emitOptDerefOpText f.name, none⟩
  | some .optDeref => .ok ⟨emitOptDerefText f.name, none⟩
  | some .spanExtent => .ok ⟨emitSpanExtentText f.name, none⟩
  | some .spanSize => .ok ⟨emitSpanSizeText f.name, none⟩
  | some .spanIndex => .ok ⟨emitSpanIndexText f.name, none⟩
  | some .spanSum => .ok ⟨emitSpanSumText f.name, none⟩
  | some .vecSize => .ok ⟨emitStdVecSizeText f.name, none⟩
  | some .vecIndex => .ok ⟨emitStdVecIndexText f.name, none⟩
  | some .vecReadSum => .ok ⟨emitStdVecReadSumText f.name, none⟩
  | some .vecEmptyCtor => .ok ⟨emitStdVecEmptyCtorText f.name, none⟩
  | some .vecUnit => .ok ⟨emitStdVecUnitText f.name, none⟩
  | some .vecDtor => .ok ⟨emitStdVecDtorText f.name, none⟩
  | some .vecDestroyNoop => .ok ⟨emitStdVecDestroyNoopText f.name, none⟩
  | some .vecDestroyPtr => .ok ⟨emitStdVecDestroyPtrText f.name, none⟩
  | some .vecGetTp => .ok ⟨emitStdVecGetTpText f.name, none⟩
  | some .vecDiffMax => .ok ⟨emitStdVecDiffMaxText f.name, none⟩
  | some .vecMax => .ok ⟨emitStdVecMaxText f.name, none⟩
  | some .vecMin => .ok ⟨emitStdVecMinText f.name, none⟩
  | some .vecCheckLen => .ok ⟨emitStdVecCheckLenText f.name, none⟩
  | some .vecBegin => .ok ⟨emitStdVecBeginText f.name, none⟩
  | some .vecEnd => .ok ⟨emitStdVecEndText f.name, none⟩
  | some .vecBack => .ok ⟨emitStdVecBackText f.name, none⟩
  | some .vecIterId => .ok ⟨emitStdVecIterIdText f.name, none⟩
  | some .vecMinusEl => .ok ⟨emitStdVecMinusElText f.name, none⟩
  | some .vecMinus => .ok ⟨emitStdVecMinusText f.name, none⟩
  | some .vecAlloc => .ok ⟨emitStdVecAllocText f.name, none⟩
  | some .vecDealloc => .ok ⟨emitStdVecDeallocText f.name, none⟩
  | some .vecDeallocGuard => .ok ⟨emitStdVecDeallocGuardText f.name, none⟩
  | some .vecConstruct => .ok ⟨emitStdVecConstructText f.name, none⟩
  | some .vecReloc => .ok ⟨emitStdVecRelocText f.name, none⟩
  | some .vecGrowRealloc => .ok ⟨emitStdVecGrowReallocText f.name, none⟩
  | some .vecEmplaceBack => .ok ⟨emitStdVecEmplaceBackText f.name, none⟩
  | some .vecPushBack => .ok ⟨emitStdVecPushBackText f.name, none⟩
  | some .vecPushSumEntry => .ok ⟨emitVecPushSumEntryText f.name, none⟩
  | some .sumCall => .ok ⟨emitSumCallerText f.name, none⟩
  | some .translate => .ok ⟨emitTranslateText f.name, none⟩
  | some .methodSum => .ok ⟨emitMethodSumText f.name, none⟩
  | some .pointSumRef => .ok ⟨emitPointSumRefText f.name, none⟩
  | some .accCtor => .ok ⟨emitAccCtorText f.name, none⟩
  | some .accAdd => .ok ⟨emitAccAddText f.name, none⟩
  | some .accGet => .ok ⟨emitAccGetText f.name, none⟩
  | some .accDtor => .ok ⟨emitAccDtorText f.name, none⟩
  | some .accTwo => .ok ⟨emitAccTwoText f.name, none⟩
  | some .accMoveCtor => .ok ⟨emitAccMoveCtorText f.name, none⟩
  | some .moveAcc => .ok ⟨emitMoveAccText f.name, none⟩
  | some .scopeEarly => .ok ⟨emitScopeEarlyText f.name, none⟩
  | some .boxThrough => .ok ⟨emitBoxThroughText f.name, none⟩
  | some .nested => .ok ⟨emitNestedText f.name, none⟩
  | some .skip => .ok ⟨emitSkipText f.name, none⟩
  | some .findEq => .ok ⟨emitFindEqText f.name, none⟩
  | some .cls => .ok ⟨emitClsText f.name, none⟩
  | some .clsFall => .ok ⟨emitClsFallText f.name, none⟩
  | some .clsDense => .ok ⟨emitClsDenseText f.name, none⟩
  | some .clsBreak => .ok ⟨emitClsBreakText f.name, none⟩
  | none => .error (.notFragment s!"not in the admitted fragment: {f.name}")

/-- Rejection is loud and names the function. -/
theorem emitFunc_rejects (f : Func) (h : matchFrag f = none) :
    ∃ msg, emitFunc f = .error (.notFragment msg) := by
  simp [emitFunc, h]

/-! ## Golden linkage (machine-checked) -/

/-- The emitter output for `addFunc` is byte-identical to the checked-in
    golden. Verified on (re)elaboration (clean and CI builds); incremental
    local drift is caught by the `diff` in `tools/check-phase3.sh`, since
    `lake` does not track `include_str` dependencies. -/
example : emitForwardText (emitFunc addFunc) =
    include_str "../tests/golden/Add.lean" := by native_decide

/-- The emitter output for `incrFunc` is byte-identical to the checked-in
    golden. -/
example : emitForwardText (emitFunc incrFunc) =
    include_str "../tests/golden/Incr.lean" := by native_decide

/-- The emitter output for `chooseFunc` (forward + backward) is
    byte-identical to the checked-in golden. -/
example : emitFileText (emitFunc chooseFunc) =
    include_str "../tests/golden/Choose.lean" := by native_decide

/-- The emitter output for `sumFunc` is byte-identical to the checked-in
    golden. -/
example : emitFileText (emitFunc sumFunc) =
    include_str "../tests/golden/SumArray.lean" := by native_decide

/-- The emitter output for `vecFunc` is byte-identical to the checked-in
    golden. -/
example : emitFileText (emitFunc vecFunc) =
    include_str "../tests/golden/VecAlloc.lean" := by native_decide

/-- The emitter output for `vec2Func` is byte-identical to the checked-in
    two-block golden. -/
example : emitFileText (emitFunc vec2Func) =
    include_str "../tests/golden/VecCopySum.lean" := by native_decide

/-- The emitter output for `vec64Func` is byte-identical to the checked-in
    `u64` golden. -/
example : emitFileText (emitFunc vec64Func) =
    include_str "../tests/golden/VecAllocU64.lean" := by native_decide

/-- The emitter output for `vecReallocFunc` is byte-identical to the
    checked-in grown-block golden. -/
example : emitFileText (emitFunc vecReallocFunc) =
    include_str "../tests/golden/VecRealloc.lean" := by native_decide

/-- The emitter output for `addCallerFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc addCallerFunc) =
    include_str "../tests/golden/AddCaller.lean" := by native_decide

/-- The emitter output for `sumCallerFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc sumCallerFunc) =
    include_str "../tests/golden/SumCaller.lean" := by native_decide

/-- The emitter output for the renamed `add` leaf is byte-identical to
    the checked-in overload golden (same body as `Add.lean`, mangled
    name). -/
example : emitFileText (emitFunc { addFunc with name := "_Z3addii" }) =
    include_str "../tests/golden/OverloadAdd.lean" := by native_decide

/-- The emitter output for `add3Func` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc add3Func) =
    include_str "../tests/golden/Add3.lean" := by native_decide

/-- The emitter output for `useAddFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc useAddFunc) =
    include_str "../tests/golden/UseAdd.lean" := by native_decide

/-- The emitter output for the namespaced `add` leaf is byte-identical
    to the checked-in golden. -/
example : emitFileText (emitFunc { addFunc with name := "_ZN2ns3addEii" }) =
    include_str "../tests/golden/NsAdd.lean" := by native_decide

/-- The emitter output for `useNsAddFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc useNsAddFunc) =
    include_str "../tests/golden/UseNsAdd.lean" := by native_decide

/-- The emitter output for `translateFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc translateFunc) =
    include_str "../tests/golden/StructByValue.lean" := by native_decide

/-- The emitter output for `methodSumFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc methodSumFunc) =
    include_str "../tests/golden/MethodSum.lean" := by native_decide

/-- The emitter output for `pointSumRefFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc pointSumRefFunc) =
    include_str "../tests/golden/PointSumRef.lean" := by native_decide

/-- The emitter output for `accCtorFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc accCtorFunc) =
    include_str "../tests/golden/AccCtor.lean" := by native_decide

/-- The emitter output for `accAddFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc accAddFunc) =
    include_str "../tests/golden/AccAdd.lean" := by native_decide

/-- The emitter output for `accGetFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc accGetFunc) =
    include_str "../tests/golden/AccGet.lean" := by native_decide

/-- The emitter output for `accDtorFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc accDtorFunc) =
    include_str "../tests/golden/AccDtor.lean" := by native_decide

/-- The emitter output for `accTwoFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc accTwoFunc) =
    include_str "../tests/golden/AccTwo.lean" := by native_decide

/-- The emitter output for `accMoveCtorFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc accMoveCtorFunc) =
    include_str "../tests/golden/MoveCtor.lean" := by native_decide

/-- The emitter output for `moveAccFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc moveAccFunc) =
    include_str "../tests/golden/MoveAcc.lean" := by native_decide

/-- The emitter output for `scopeEarlyFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc scopeEarlyFunc) =
    include_str "../tests/golden/ScopeEarly.lean" := by native_decide

/-- The emitter output for `boxThroughFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc boxThroughFunc) =
    include_str "../tests/golden/BoxThrough.lean" := by native_decide


