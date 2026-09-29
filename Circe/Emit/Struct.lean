/-
Circe.Emit.Struct — S2 struct-by-value `translate`: field projection + `nsw`
field adds, with ok/err bridges.
-/
import Circe.Emit.Fragment

/-! ## S2: struct-by-value (`translate`) -/

/-- Canonical CoreIR for `tests/c/struct_by_value.c`: project both
    fields, checked-add the deltas, build the result `Point`
    (field-wise update functionalized; `cir.get_member` + `cir.load`
    fused into `fget`, stores + return fused into `pmk`). -/
def translateFunc : Func :=
  ⟨"translate",
   [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
    { name := "dx", ty := .i 32, role := .owned },
    { name := "dy", ty := .i 32, role := .owned }],
   .struct "Point" [.i 32, .i 32],
   .seq (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
   (.seq (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
         (.return_ (.pmk (.var "qx") (.var "qy"))))⟩


/-- Value-level forward for `translate`: field-wise checked addition
    (cf. rendered `translate_fwd`, which delegates to `pointTranslate`). -/
def translateFwd (px py dx dy : BitVec 32) : Result Value :=
  match checkedAddI32 px dx, checkedAddI32 py dy with
  | .ok x', .ok y' => .ok (.structVal "Point" [("x", x'), ("y", y')])
  | .error e, _ => .error e
  | _, .error e => .error e

/-- Bridge: forward ok-path equals `pointTranslate` ok-path. -/
theorem translateFwd_ok_bridge (px py dx dy x' y' : BitVec 32)
    (hx : checkedAddI32 px dx = .ok x')
    (hy : checkedAddI32 py dy = .ok y') :
    translateFwd px py dx dy =
      .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
  simp [translateFwd, hx, hy]

theorem translateFwd_err_x (px py dx dy : BitVec 32) (e : Panic)
    (hx : checkedAddI32 px dx = .error e) :
    translateFwd px py dx dy = .error e := by
  simp [translateFwd, hx]

theorem translateFwd_err_y (px py dx dy : BitVec 32) (x' : BitVec 32)
    (e : Panic)
    (hx : checkedAddI32 px dx = .ok x')
    (hy : checkedAddI32 py dy = .error e) :
    translateFwd px py dx dy = .error e := by
  simp [translateFwd, hx, hy]

/-- Env facts for the `translate` shape. -/
theorem envLookup_translate_p (px py dx dy : BitVec 32) :
    envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "p" =
      some (.structVal "Point" [("x", px), ("y", py)]) := by
  simp [envLookup]

theorem envLookup_translate_dx (px py dx dy : BitVec 32) :
    envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dx" = some (.i32 dx) := by
  simp [envLookup, show ("dx" : String) ≠ "p" by decide]

theorem envLookup_translate_dy (px py dx dy : BitVec 32) :
    envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dy" = some (.i32 dy) := by
  simp [envLookup, show ("dy" : String) ≠ "p" by decide,
    show ("dy" : String) ≠ "dx" by decide]

/-- Field facts for the bound `Point` value. -/
theorem fieldLookup_translate_x (px py : BitVec 32) :
    fieldLookup [("x", px), ("y", py)] "x" = some px :=
  fieldLookup_hit "x" px _

theorem fieldLookup_translate_y (px py : BitVec 32) :
    fieldLookup [("x", px), ("y", py)] "y" = some py := by
  rw [fieldLookup_miss "x" "y" px _ (by decide)]
  exact fieldLookup_hit "y" py _

/-- `emit_correct` for `translate`: evaluation agrees with the forward
    on all inputs (ok and both error paths). Loop-free body, so every
    fuel agrees. -/
theorem evalFuncFuel_translate (F : Nat) (px py dx dy : BitVec 32) :
    evalFuncFuel F translateFunc
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
      translateFwd px py dx dy := by
  have hbind : bindArgs translateFunc.args
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
      some [("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)] := rfl
  have hbody : translateFunc.body =
      .seq (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
      (.seq (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
            (.return_ (.pmk (.var "qx") (.var "qy")))) := rfl
  have hp := envLookup_translate_p px py dx dy
  have hdx := envLookup_translate_dx px py dx dy
  have hdy := envLookup_translate_dy px py dx dy
  have hfx : fieldLookup [("x", px), ("y", py)] "x" = some px :=
    fieldLookup_translate_x px py
  have hfy : fieldLookup [("x", px), ("y", py)] "y" = some py :=
    fieldLookup_translate_y px py
  have haddx : evalExpr (.add (.fget "p" "x") (.var "dx"))
      [("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)] =
      (checkedAddI32 px dx).map .i32 :=
    evalExpr_add_fget_var _ _ _ _ _ _ _ _ hp hfx hdx
  cases hx : checkedAddI32 px dx with
  | error e =>
    have haddx' : evalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] = .error e := by
      rw [haddx, hx]
      exact i32_map_error e
    have hlet : evalStmtFuel F
        (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] = .error e := by
      cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddx']
    simp only [evalFuncFuel, hbind, hbody]
    rw [evalStmtFuel_seq_err _ _ _ _ _ hlet]
    simp [translateFwd, hx]
  | ok x' =>
    have haddx' : evalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] = .ok (.i32 x') := by
      rw [haddx, hx]
      exact i32_map_ok x'
    have hletx : evalStmtFuel F
        (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] =
        .ok (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x'),
          .fellThrough) := by
      cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddx']
    have hobj2 : envLookup (envExtend [("p", .structVal "Point"
        [("x", px), ("y", py)]), ("dx", .i32 dx), ("dy", .i32 dy)]
        "qx" (.i32 x')) "p" =
        some (.structVal "Point" [("x", px), ("y", py)]) := by
      simp [envExtend, envLookup, show ("p" : String) ≠ "qx" by decide]
    have hvar2 : envLookup (envExtend [("p", .structVal "Point"
        [("x", px), ("y", py)]), ("dx", .i32 dx), ("dy", .i32 dy)]
        "qx" (.i32 x')) "dy" = some (.i32 dy) := by
      simp [envExtend, envLookup, show ("dy" : String) ≠ "qx" by decide]
    have haddy : evalExpr (.add (.fget "p" "y") (.var "dy"))
        (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
        (checkedAddI32 py dy).map .i32 :=
      evalExpr_add_fget_var _ _ _ _ _ _ _ _ hobj2 hfy hvar2
    cases hy : checkedAddI32 py dy with
    | error e =>
      have haddy' : evalExpr (.add (.fget "p" "y") (.var "dy"))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .error e := by
        rw [haddy, hy]
        exact i32_map_error e
      have hlety : evalStmtFuel F
          (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .error e := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddy']
      simp only [evalFuncFuel, hbind, hbody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hletx,
        evalStmtFuel_seq_err _ _ _ _ _ hlety]
      simp [translateFwd, hx, hy]
    | ok y' =>
      have haddy' : evalExpr (.add (.fget "p" "y") (.var "dy"))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .ok (.i32 y') := by
        rw [haddy, hy]
        exact i32_map_ok y'
      have hlety : evalStmtFuel F
          (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
          (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) =
          .ok (envExtend (envExtend [("p", .structVal "Point"
            [("x", px), ("y", py)]), ("dx", .i32 dx), ("dy", .i32 dy)]
            "qx" (.i32 x')) "qy" (.i32 y'), .fellThrough) := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddy']
      have hqx : evalExpr (.var "qx")
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (.i32 x') :=
        evalExpr_var_hit _ _ _
          (by simp [envExtend, envLookup,
            show ("qx" : String) ≠ "qy" by decide])
      have hqy : evalExpr (.var "qy")
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (.i32 y') :=
        evalExpr_var_hit _ _ _ (envExtend_hit _ _ _)
      have hmk : evalExpr (.pmk (.var "qx") (.var "qy"))
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) :=
        evalExpr_pmk_ok _ _ _ _ _ hqx hqy
      have hret : evalStmtFuel F
          (.return_ (.pmk (.var "qx") (.var "qy")))
          (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y')) =
          .ok (envExtend (envExtend [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)] "qx" (.i32 x')) "qy" (.i32 y'),
            .returned (.structVal "Point" [("x", x'), ("y", y')])) :=
        evalStmtFuel_return _ _ _ _ hmk
      simp only [evalFuncFuel, hbind, hbody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hletx,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ hlety, hret]
      simp [translateFwd, hx, hy]
