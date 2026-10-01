/-
Circe.Emit — verified emitter `CoreIR → Lean` (facade).

Fragment definitions and proofs live in `Circe.Emit.*` (`Fragment`, `Add`,
`Choose`, `Sum`, `Vec`, `Vec64`, `Vec2`, `VecRealloc`, `Calls`, `Struct`,
`Method`, `Acc`, `Flow`); shape
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
  | some .incr => .ok (emitIncrSpecText f.name)
  | some .choose => .ok (emitChooseSpecText f.name)
  | some .sum => .ok (emitSumSpecText f.name)
  | some .vec => .ok (emitVecSpecText f.name)
  | some .vec64 => .ok (emitVec64SpecText f.name)
  | some .vec2 => .ok (emitVec2SpecText f.name)
  | some .vecRealloc => .ok (emitVecReallocSpecText f.name)
  | some .addCall => .ok (emitAddCallerSpecText f.name)
  | some .sumCall => .ok (emitSumCallerSpecText f.name)
  | some .translate => .ok (emitTranslateSpecText f.name)
  | some .methodSum => .ok (emitMethodSumSpecText f.name)
  | some .pointSumRef => .ok (emitPointSumRefSpecText f.name)
  | some .accCtor => .ok (emitAccCtorSpecText f.name)
  | some .accAdd => .ok (emitAccAddSpecText f.name)
  | some .accGet => .ok (emitAccGetSpecText f.name)
  | some .accDtor => .ok (emitAccDtorSpecText f.name)
  | some .accTwo => .ok (emitAccTwoSpecText f.name)
  | some .boxThrough => .ok (emitBoxThroughSpecText f.name)
  | some .nested => .ok (emitNestedSpecText f.name)
  | some .skip => .ok (emitSkipSpecText f.name)
  | some .findEq => .ok (emitFindEqSpecText f.name)
  | some .cls => .ok (emitClsSpecText f.name)
  | none => .error (.notFragment s!"not in the admitted fragment: {f.name}")

/-- The emitter: accepted fragment renders to file text; everything else
    is rejected loudly (never silently modeled). -/
def emitFunc (f : Func) : Except EmitError EmittedFunc :=
  match matchFrag f with
  | some .add => .ok ⟨emitAddText f.name, none⟩
  | some .add64 => .ok ⟨emitAdd64Text f.name, none⟩
  | some .addu64 => .ok ⟨emitAddu64Text f.name, none⟩
  | some .incr => .ok ⟨emitIncrText f.name, none⟩
  | some .choose =>
    .ok ⟨emitChooseFwdText f.name, some (emitChooseBackText f.name)⟩
  | some .sum => .ok ⟨emitSumText f.name, none⟩
  | some .vec => .ok ⟨emitVecText f.name, none⟩
  | some .vec64 => .ok ⟨emitVec64Text f.name, none⟩
  | some .vec2 => .ok ⟨emitVec2Text f.name, none⟩
  | some .vecRealloc => .ok ⟨emitVecReallocText f.name, none⟩
  | some .addCall => .ok ⟨emitAddCallerText f.name, none⟩
  | some .sumCall => .ok ⟨emitSumCallerText f.name, none⟩
  | some .translate => .ok ⟨emitTranslateText f.name, none⟩
  | some .methodSum => .ok ⟨emitMethodSumText f.name, none⟩
  | some .pointSumRef => .ok ⟨emitPointSumRefText f.name, none⟩
  | some .accCtor => .ok ⟨emitAccCtorText f.name, none⟩
  | some .accAdd => .ok ⟨emitAccAddText f.name, none⟩
  | some .accGet => .ok ⟨emitAccGetText f.name, none⟩
  | some .accDtor => .ok ⟨emitAccDtorText f.name, none⟩
  | some .accTwo => .ok ⟨emitAccTwoText f.name, none⟩
  | some .boxThrough => .ok ⟨emitBoxThroughText f.name, none⟩
  | some .nested => .ok ⟨emitNestedText f.name, none⟩
  | some .skip => .ok ⟨emitSkipText f.name, none⟩
  | some .findEq => .ok ⟨emitFindEqText f.name, none⟩
  | some .cls => .ok ⟨emitClsText f.name, none⟩
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

/-- The emitter output for `boxThroughFunc` is byte-identical to the
    checked-in golden. -/
example : emitFileText (emitFunc boxThroughFunc) =
    include_str "../tests/golden/BoxThrough.lean" := by native_decide


