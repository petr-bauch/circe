/-
Circe.Emit.Box — M2c `new` / `delete` as ownership ops: `box_through(x)`.

`box_through(x)` is int-only (the box never crosses the boundary), so the
heap box is a single `i32` value plus an affine `freed` token threaded
functionally (Vec32 precedent at one word): `new` is the init
(`boxNew x`), the read is `boxGet`, `delete` consumes the token
(`boxFree`; double-`delete` / use-after-`delete` are `AssertFail`). The
null-guarded `cir.if` in the corpus is dead (`_Znwm` returns `nonnull`)
and erased at validation, as is the `cleanup` scope (the sized
`_ZdlPvm` inside it becomes `boxFree`); the shape gate pins the guard,
the size const, and the call multiset instead.
-/
import Circe.Emit.Fragment

/-! ## M2c: `new` / `delete` as ownership ops (`box_through`) -/

/-- Canonical CoreIR for the `_Z11box_throughi` entry in
    `tests/cpp/box_through.cpp`: `new` (`boxNew x` fusing
    `cir.call @_Znwm` + bitcast + field store), read (`boxGet p` fusing
    `cir.get_member` + `cir.load`), `delete` (`boxFree p` for the
    `cleanup`-scoped sized `cir.call @_ZdlPvm`), return. -/
def boxThroughFunc : Func :=
  ⟨"_Z11box_throughi",
   [{ name := "x", ty := .i 32, role := .owned }],
   .i 32,
   .seq (.let_ "p" (.struct "Box" [.i 32]) (.boxNew (.var "x")))
   (.seq (.let_ "r" (.i 32) (.boxGet "p"))
   (.seq (.boxFree "p")
         (.return_ (.var "r"))))⟩

/-- Value-level forward for the entry: direct delegation to `boxThrough`
    (cf. rendered `_Z11box_throughi_fwd`). -/
def boxThroughFwd (x : BitVec 32) : Result Value :=
  .i32 <$> boxThrough x

theorem boxThroughFwd_is_boxThrough (x : BitVec 32) :
    boxThroughFwd x = .i32 <$> boxThrough x := rfl

/-- `emit_correct` for the entry (loop-free, every fuel agrees). -/
theorem evalFuncFuel_boxThrough (F : Nat) (x : BitVec 32) :
    evalFuncFuel F boxThroughFunc [.i32 x] = boxThroughFwd x := by
  have hbind : bindArgs boxThroughFunc.args [.i32 x] =
      some [("x", .i32 x)] := rfl
  have hbody : boxThroughFunc.body =
      .seq (.let_ "p" (.struct "Box" [.i 32]) (.boxNew (.var "x")))
      (.seq (.let_ "r" (.i 32) (.boxGet "p"))
      (.seq (.boxFree "p")
            (.return_ (.var "r")))) := rfl
  have hvar : evalExpr (.var "x") ([("x", .i32 x)] : Env) =
      .ok (.i32 x) := rfl
  have hnew : evalExpr (.boxNew (.var "x")) ([("x", .i32 x)] : Env) =
      .ok (.boxVal ⟨x, false⟩) :=
    evalExpr_boxNew_ok (.var "x") _ x hvar
  have hstep0 := evalStmtFuel_let_ F "p" (.struct "Box" [.i 32])
    (.boxNew (.var "x")) ([("x", .i32 x)] : Env) (.boxVal ⟨x, false⟩) hnew
  have hget : evalExpr (.boxGet "p")
      (envExtend ([("x", .i32 x)] : Env) "p" (.boxVal ⟨x, false⟩)) =
      .ok (.i32 x) := by
    have harr : envLookup
        (envExtend ([("x", .i32 x)] : Env) "p" (.boxVal ⟨x, false⟩)) "p" =
        some (.boxVal ⟨x, false⟩) := rfl
    have hread : boxGet (⟨x, false⟩ : Box32) = .ok x :=
      boxGet_ok _ rfl
    exact evalExpr_boxGet_hit "p" _ _ x harr hread
  have hstep1 := evalStmtFuel_let_ F "r" (.i 32) (.boxGet "p")
    (envExtend ([("x", .i32 x)] : Env) "p" (.boxVal ⟨x, false⟩))
    (.i32 x) hget
  have hfreeArr : envLookup
      (envExtend (envExtend ([("x", .i32 x)] : Env)
        "p" (.boxVal ⟨x, false⟩)) "r" (.i32 x)) "p" =
      some (.boxVal ⟨x, false⟩) := by
    simp [envExtend, envLookup,
      show ("p" : String) ≠ "r" by decide]
  have hfreeOp : boxFree (⟨x, false⟩ : Box32) =
      .ok ⟨x, true⟩ :=
    boxFree_ok _ rfl
  have hfreeUp : envUpdate
      (envExtend (envExtend ([("x", .i32 x)] : Env)
        "p" (.boxVal ⟨x, false⟩)) "r" (.i32 x))
      "p" (.boxVal ⟨x, true⟩) =
      some (envExtend (envExtend ([("x", .i32 x)] : Env)
        "p" (.boxVal ⟨x, true⟩)) "r" (.i32 x)) := rfl
  have hstep2 := evalStmtFuel_boxFree F "p"
    (envExtend (envExtend ([("x", .i32 x)] : Env)
      "p" (.boxVal ⟨x, false⟩)) "r" (.i32 x))
    (⟨x, false⟩ : Box32) (⟨x, true⟩ : Box32)
    (envExtend (envExtend ([("x", .i32 x)] : Env)
      "p" (.boxVal ⟨x, true⟩)) "r" (.i32 x))
    hfreeArr hfreeOp hfreeUp
  have hret : evalStmtFuel F (.return_ (.var "r"))
      (envExtend (envExtend ([("x", .i32 x)] : Env)
        "p" (.boxVal ⟨x, true⟩)) "r" (.i32 x)) =
      .ok (envExtend (envExtend ([("x", .i32 x)] : Env)
        "p" (.boxVal ⟨x, true⟩)) "r" (.i32 x), .returned (.i32 x)) := by
    have hv : evalExpr (.var "r")
        (envExtend (envExtend ([("x", .i32 x)] : Env)
          "p" (.boxVal ⟨x, true⟩)) "r" (.i32 x)) =
        .ok (.i32 x) := rfl
    exact evalStmtFuel_return _ _ _ _ hv
  simp only [evalFuncFuel, hbind, hbody]
  rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hstep0,
    evalStmtFuel_seq_fallthrough _ _ _ _ _ hstep1,
    evalStmtFuel_seq_fallthrough _ _ _ _ _ hstep2, hret]
  have hok : boxThroughFwd x = .ok (.i32 x) := by
    simp only [boxThroughFwd_is_boxThrough, boxThrough_ok, i32_map_ok]
  simp [hok]
