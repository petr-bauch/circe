/-
Out-of-place filter (`std::copy_if` idiom) over `std::vector<int>` —
the P2-M9 compaction scan writing into a caller-sized output
(pillar-2 proposed goal, P2-M12).

Corpus: `tests/cpp/vec_copy_if.cpp` →
`tests/cir/vec_copy_if.cir` (entry
`_Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i`: read-only `a` +
caller-sized `out` + owned `i32` value, `u64` count out; a
single `cir.while` scan with a conditional `out.at()` store).

Model: the read cursor `r` scans `a`; the keep test
`a.at(r) != x` is the fused `at()` read (`.une`, total on
`i32`); a kept element stores into `out` at the write cursor
`w` through the non-const `at()` checked path (M2 `vec_at_set`
precedent: inner `ult` guard with `.fail`, so short `out` is
loud `AssertFail`), then both cursors advance; dropped
elements advance only `r`. The endpoint returns the survivor
count `w`; `out` past `w` is untouched — the caller-sized
output discipline.
-/
import Circe.Emit.VecTransformAdd

/-- Function name (Itanium mangling of a `vec_copy_if` free
    function taking `const vector<int>&` + `vector<int>&` +
    `int`, returning `unsigned long`). -/
def vecCopyIfName : String :=
  "_Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i"

/-- Loop body: keep `a[r]` iff it differs from `x` — the checked
    `out.at(w)` store (loud on short `out`) and both cursors
    advance; the read cursor always advances. -/
def vecCopyIfBody : CStmt :=
  (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w") (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
            .fail)
          .skip)
    (.assign "r" (.uadd (.var "r") (.lit (.u64 1)))))

/-- Loop `while (r < n) body`. -/
def vecCopyIfLoop : CStmt :=
  (.while_ (.ult (.var "r") (.stdVecLen "a")) vecCopyIfBody)

/-- Whole function: `let_`-prelude binds `r` and `w`, the loop,
    then the survivor count returns. -/
def vecCopyIfFunc : Func :=
  ⟨vecCopyIfName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "x", ty := .i 32, role := .owned }],
   .u 64,
   (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq vecCopyIfLoop
         (.return_ (.var "w")))))⟩

/-- Loop environment (read words + output words + owned value +
    `u64` cursors), in prelude `let_` cons order (`w` over `r`
    over `[a, out, x]`, so the entry bridge is `rfl`). -/
def mkCopyIfEnv (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : BitVec 64) : Env :=
  [("w", .u64 w), ("r", .u64 r), ("x", .i32 x),
   ("a", .stdVecVal la), ("out", .stdVecVal lo)]

theorem mkCopyIfEnv_a (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : BitVec 64) :
    envLookup (mkCopyIfEnv la lo x r w) "a" =
      some (.stdVecVal la) := by
  simp [mkCopyIfEnv, envLookup, show ("a" : String) ≠ "r" by decide,
    show ("a" : String) ≠ "w" by decide,
    show ("a" : String) ≠ "x" by decide]

theorem mkCopyIfEnv_out (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : BitVec 64) :
    envLookup (mkCopyIfEnv la lo x r w) "out" =
      some (.stdVecVal lo) := by
  simp [mkCopyIfEnv, envLookup, show ("out" : String) ≠ "r" by decide,
    show ("out" : String) ≠ "w" by decide,
    show ("out" : String) ≠ "x" by decide,
    show ("out" : String) ≠ "a" by decide]

theorem mkCopyIfEnv_x (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : BitVec 64) :
    envLookup (mkCopyIfEnv la lo x r w) "x" = some (.i32 x) := by
  simp [mkCopyIfEnv, envLookup, show ("x" : String) ≠ "r" by decide,
    show ("x" : String) ≠ "w" by decide]

theorem mkCopyIfEnv_r (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : BitVec 64) :
    envLookup (mkCopyIfEnv la lo x r w) "r" = some (.u64 r) := by
  simp [mkCopyIfEnv, envLookup, show ("r" : String) ≠ "w" by decide]

theorem mkCopyIfEnv_w (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : BitVec 64) :
    envLookup (mkCopyIfEnv la lo x r w) "w" = some (.u64 w) := by
  simp [mkCopyIfEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + input words + output words + read cursor +
    write cursor. Fuel 0 returns the state so far (the V1
    miss-default idiom); the `none` arms are unreachable
    in-invariant (every read is guard-justified; every write is
    justified until the short-`out` leg fires). -/
def copyIfFwd (x : BitVec 32) :
    List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat →
      Result (Nat × Nat × List (BitVec 32))
  | la, lo, 0, r, w => .ok (r, w, lo)
  | la, lo, fuel + 1, r, w =>
    if _ : r < la.length then
      match la[r]? with
      | none => .error .AssertFail
      | some y =>
        if (y != x) then
          match lo[w]? with
          | none => .error .AssertFail
          | some _ => copyIfFwd x la (lo.set w y) fuel (r + 1) (w + 1)
        else copyIfFwd x la lo fuel (r + 1) w
    else .ok (r, w, lo)

/-- Whole-function forward: the loop at measure-exact fuel, then
    the survivor count. -/
def vecCopyIfFwd (la lo : List (BitVec 32)) (x : BitVec 32) :
    Result Value :=
  match copyIfFwd x la lo la.length 0 0 with
  | .error e => .error e
  | .ok (_, w', _) => .ok (.u64 (BitVec.ofNat 64 w'))

/-- Program over which the entry evaluates (no callees: the body
    is straight-line `if` / `vecSet` / `assign` / `fail`). -/
abbrev vecCopyIfProg : Prog := [vecCopyIfFunc]

/-! ## Value loop (bridges `evalProgStmt` to `copyIfFwd`) -/

/-- One body iteration (value level), keep branch: the `une`
    test fires, the `out` guard holds, the kept element stores
    at `w`, both cursors advance. -/
theorem valCopyIfBody_copy (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y wOld : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y) (hwget : lo[w]? = some wOld)
    (hkeep : (y != x) = true) :
    ∃ ρ', evalProgStmt prog F vecCopyIfBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
      envLookup ρ' "x" = some (.i32 x) := by
  have hwlt : w < lo.length := transformRead_lt lo w wOld hwget
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : lo[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have hune : evalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      (.var "x") ρ y x hatR hxV
    rwa [hkeep] at h
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardT : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ wB
      (BitVec.ofNat 64 lo.length) hwVar
      (evalExpr_stdVecLen_some _ _ _ hout)
    have htb : (wB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hsetB : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout
  have hstep_set := revVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "r")) ρ wB y lo wOld ρ₁ hwVar hatR hout
    hgetW hu₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "out" _ ρ₁
      (show ("a" : String) ≠ "out" by decide) hu₁
    rw [h]; exact ha
  have hx₁ : envLookup ρ₁ "x" = some (.i32 x) := by
    have h := envLookup_update_miss ρ "x" "out" _ ρ₁
      (show ("x" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hx
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "out" _ ρ₁
      (show ("r" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hr
  have hwVar₁ : evalExpr (.var "w") ρ₁ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _
      (by rw [envLookup_update_miss _ _ _ _ _
        (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw)
  have hevW : evalExpr (.uadd (.var "w") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hwVar₁ (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "w"
    (.u64 wB) (.u64 (wB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw)
  have hstep_w := revAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 1))) ρ₁ (.u64 (wB + 1)) ρ₂ hevW hu₂
  have hr₂ : envLookup ρ₂ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "w" by decide) hu₂]
    exact hr₁
  have hx₂ : envLookup ρ₂ "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "w" by decide) hu₂]
    exact hx₁
  have ha₂ : envLookup ρ₂ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₂]
    exact ha₁
  have hrVar₂ : evalExpr (.var "r") ρ₂ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr₂
  have hevR : evalExpr (.uadd (.var "r") (.lit (.u64 1))) ρ₂ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hrVar₂ (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) hr₂
  have hstep_r := revAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 1))) ρ₂ (.u64 (rB + 1)) ρ₃ hevR hu₃
  have hout₃ : envLookup ρ₃ "out" =
      some (.stdVecVal (lo.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu₃]
    exact ha₂
  have hx₃ : envLookup ρ₃ "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "r" by decide) hu₃]
    exact hx₂
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ₃ "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hw₂ : envLookup ρ₂ "w" = some (.u64 (wB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hw' : envLookup ρ₃ "w" = some (.u64 (wB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "r" by decide) hu₃]
    exact hw₂
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w") (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        .fail) ρ = .ok (ρ₂, .fellThrough) := by
    have hthen : evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w") (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        ρ = .ok (ρ₂, .fellThrough) := by
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
        hstep_w]
    exact (evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hthen
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .fail)
        .skip) ρ = .ok (ρ₂, .fellThrough) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hune).trans hinner
  have hbody : vecCopyIfBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
              (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecCopyIfBody ρ =
      .ok (ρ₃, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, heval, ha₃, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩, hx₃⟩

/-- One body iteration (value level), short-`out` branch: the
    `une` test fires but `w` is past the output, so the inner
    guard fails and the loud `.fail` leg fires. -/
theorem valCopyIfBody_short (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hmiss : lo[w]? = none)
    (hkeep : (y != x) = true) :
    evalProgStmt prog F vecCopyIfBody ρ = .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have hune : evalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      (.var "x") ρ y x hatR hxV
    rwa [hkeep] at h
  have hnl : ¬ w < lo.length := by
    intro h
    have hsome : lo[w]? = some lo[w] := List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardF : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ =
      .ok (.b false) := by
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ wB
      (BitVec.ofNat 64 lo.length) hwVar
      (evalExpr_stdVecLen_some _ _ _ hout)
    have hfb : (wB.ult (BitVec.ofNat 64 lo.length)) = false := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hfail : evalProgStmt prog F .fail ρ = .error .AssertFail := by
    simpa [evalProgStmt] using (evalStmtFuel_fail F ρ)
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w") (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        .fail) ρ = .error .AssertFail :=
    (evalProgStmt_if_false _ _ _ _ _ _ hguardF).trans hfail
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .fail)
        .skip) ρ = .error .AssertFail :=
    (evalProgStmt_if_true _ _ _ _ _ _ hune).trans hinner
  have hbody : vecCopyIfBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
              (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have herr : evalProgStmt prog F vecCopyIfBody ρ =
      .error .AssertFail := by
    rw [hbody]
    exact evalProgStmt_seq_err _ _ _ _ _ _ hif
  exact herr

/-- One body iteration (value level), drop branch: the `une`
    test fails, the state threads untouched, only `r` advances. -/
theorem valCopyIfBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hdrop : (y != x) = false) :
    ∃ ρ', evalProgStmt prog F vecCopyIfBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) ∧
      envLookup ρ' "x" = some (.i32 x) := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have hune : evalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ =
      .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      (.var "x") ρ y x hatR hxV
    rwa [hdrop] at h
  have hskipV : evalProgStmt prog F .skip ρ =
      .ok (ρ, .fellThrough) := by
    simpa [evalProgStmt] using
      (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .fail)
        .skip) ρ = .ok (ρ, .fellThrough) :=
    (evalProgStmt_if_false _ _ _ _ _ _ hune).trans hskipV
  have hevR : evalExpr (.uadd (.var "r") (.lit (.u64 1))) ρ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hrVar (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "r"
    (.u64 rB) (.u64 (rB + 1)) hr
  have hstep_r := revAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 1))) ρ (.u64 (rB + 1)) ρ' hevR hu
  have hout' : envLookup ρ' "out" = some (.stdVecVal lo) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "r" by decide) hu]
    exact hout
  have ha' : envLookup ρ' "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu]
    exact ha
  have hw' : envLookup ρ' "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "r" by decide) hu]
    exact hw
  have hx' : envLookup ρ' "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "r" by decide) hu]
    exact hx
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ' "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : vecCopyIfBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
              (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecCopyIfBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', heval, ha', hout', ⟨(rB + 1), hr', hrN'⟩, ⟨wB, hw', hwN⟩,
    hx'⟩

/-- Keeps before `r + 1` extend keeps before `r` when `la[r]`
    is kept (the take-succ step for the count invariant). -/
theorem copyIfFilter_take_succ (x : BitVec 32) (la : List (BitVec 32))
    (r : Nat) (y : BitVec 32)
    (hy : la[r]? = some y)
    (hkeep : (y != x) = true) :
    ((la.take (r + 1)).filter (fun z => (z != x))).length =
      ((la.take r).filter (fun z => (z != x))).length + 1 := by
  have htake : la.take (r + 1) = la.take r ++ [y] := by
    have h0 : la.take (r + 1) = la.take r ++ la[r]?.toList :=
      List.take_add_one
    have h1 : la[r]?.toList = [y] := by rw [hy]; rfl
    rwa [h1] at h0
  have hfilter : ((la.take (r + 1)).filter (fun z => (z != x))) =
      (la.take r).filter (fun z => (z != x)) ++ [y] := by
    rw [htake, List.filter_append]
    simp [hkeep]
  rw [hfilter, List.length_append, List.length_singleton]

/-- Keeps before `r + 1` equal keeps before `r` when `la[r]`
    is dropped (the take-succ step for the count invariant). -/
theorem copyIfFilter_take_succ_drop (x : BitVec 32)
    (la : List (BitVec 32)) (r : Nat) (y : BitVec 32)
    (hy : la[r]? = some y)
    (hdrop : (y != x) = false) :
    ((la.take (r + 1)).filter (fun z => (z != x))) =
      (la.take r).filter (fun z => (z != x)) := by
  have htake : la.take (r + 1) = la.take r ++ [y] := by
    have h0 : la.take (r + 1) = la.take r ++ la[r]?.toList :=
      List.take_add_one
    have h1 : la[r]?.toList = [y] := by rw [hy]; rfl
    rwa [h1] at h0
  rw [htake, List.filter_append]
  simp [hdrop]

/-- Keeps split at `r + 1`: total keeps = keeps before +
    keeps from (the capacity argument for the next write). -/
theorem copyIfFilter_split (x : BitVec 32) (la : List (BitVec 32))
    (r : Nat) (hle : r + 1 ≤ la.length) :
    (la.filter (fun y => (y != x))).length =
      ((la.take (r + 1)).filter (fun y => (y != x))).length +
        ((la.drop (r + 1)).filter (fun y => (y != x))).length := by
  have h : la.take (r + 1) ++ la.drop (r + 1) = la :=
    List.take_append_drop (r + 1) la
  have hfilter : (((la.take (r + 1) ++ la.drop (r + 1)).filter
      (fun y => (y != x))).length =
      ((la.take (r + 1)).filter (fun y => (y != x))).length +
        ((la.drop (r + 1)).filter (fun y => (y != x))).length) := by
    rw [List.filter_append, List.length_append]
  rw [h] at hfilter
  exact hfilter

/-- Value loop, ok leg: the scan runs to `la.length` and the
    output words are the forward-model result (fuel induction
    threading the keep count and the capacity bound; the
    forward equation unfolds one step per iteration). -/
theorem valCopyIfLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64)
    (lo' : List (BitVec 32)) (r' w' : Nat)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcnt : ((la.take r).filter (fun y => (y != x))).length = w)
    (hcap : (la.filter (fun y => (y != x))).length ≤ lo.length)
    (hfwd : copyIfFwd x la lo G r w = .ok (r', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecCopyIfLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') := by
  induction F generalizing G ρ lo r w rB wB with
  | zero =>
    have him : r = la.length := by omega
    have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hguardF : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
        (BitVec.ofNat 64 la.length)
        (evalExpr_var_hit _ _ _ hr)
        (evalExpr_stdVecLen_some _ _ _ ha)
      have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt prog 0 vecCopyIfLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (r, w, lo) = (r', w', lo') := by
      cases G with
      | zero => simpa [copyIfFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < la.length := by omega
        simpa [copyIfFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hout, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩⟩
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardT : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != x) = true
      · have hkeeps1 : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := by
          rw [copyIfFilter_take_succ x la r y hy hkeep, hwcnt]
        have hwlt : w < lo.length := by
          have hsplit := copyIfFilter_split x la r (by omega)
          omega
        obtain ⟨wOld, hwget⟩ : ∃ z, lo[w]? = some z :=
          ⟨lo[w], List.getElem?_eq_getElem hwlt⟩
        have hF'' : la.length - (r + 1) ≤ F := by omega
        have hG'' : la.length - (r + 1) ≤ G' := by omega
        have hlo64' : (lo.set w y).length < 2 ^ 64 := by
          have hlen : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          rw [hlen]; exact hlo64
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := hkeeps1
        have hcap' : (la.filter (fun y => (y != x))).length ≤
            (lo.set w y).length := by
          have hlen : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          rw [hlen]; exact hcap
        have hfwd' : copyIfFwd x la (lo.set w y) G' (r + 1) (w + 1) =
            .ok (r', w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁⟩ :=
          valCopyIfBody_copy prog F ρ la lo x r w rB wB y wOld
            hrN hwN hla64 hlo64 ha hout hx hr hw hlt hy hwget hkeep
        obtain ⟨ρ', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (lo := lo.set w y)
            (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64')
            (ha := ha₁) (hout := hout₁) (hx := hx₁)
            (hr := hrB₁) (hw := hwB₁)
            (hle := by omega)
            (hF := hF'') (hG := hG'')
            (hwcnt := hwcnt') (hcap := hcap')
            (hfwd := hfwd')
        refine ⟨ρ', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecCopyIfLoop ρ =
            evalProgStmt prog F vecCopyIfLoop ρ₁ := by
          cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w) := by
          rw [copyIfFilter_take_succ_drop x la r y hy hdrop, hwcnt]
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : copyIfFwd x la lo G' (r + 1) w =
            .ok (r', w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁⟩ :=
          valCopyIfBody_drop prog F ρ la lo x r w rB wB y
            hrN hwN hla64 ha hout hx hr hw hlt hy hdrop
        obtain ⟨ρ', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁) (hx := hx₁)
            (hr := hrB₁) (hw := hwB₁)
            (hle := by omega)
            (hF := hF') (hG := hG')
            (hwcnt := hwcnt') (hcap := hcap)
            (hfwd := hfwd')
        refine ⟨ρ', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecCopyIfLoop ρ =
            evalProgStmt prog F vecCopyIfLoop ρ₁ := by
          cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : r = la.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardF : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt prog (F + 1) vecCopyIfLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (la.length, w, lo) = (r', w', lo') := by
        cases G with
        | zero => simpa [copyIfFwd] using hfwd
        | succ G =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [copyIfFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hout, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩⟩

/-- Value loop, short-`out` error leg: the first overflowing
    keep aborts loudly (fuel induction; the forward equation
    threads). -/
theorem valCopyIfLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : copyIfFwd x la lo G r w = .error .AssertFail) :
    evalProgStmt prog F vecCopyIfLoop ρ = .error .AssertFail := by
  induction F generalizing G ρ lo r w rB wB with
  | zero =>
    have him : r = la.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [copyIfFwd])
    | succ _ =>
      have hneg : ¬ la.length < la.length := by omega
      have hcon := hfwd
      simp only [copyIfFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardT : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != x) = true
      · by_cases hmiss : lo[w]? = none
        · have hshort := valCopyIfBody_short prog F ρ la lo x r w
            rB wB y hrN hwN hlo64 ha hout hx hr hw hlt hy hmiss hkeep
          have hwhile : evalProgStmt prog (F + 1) vecCopyIfLoop ρ =
              .error .AssertFail := by
            have hloop : vecCopyIfLoop =
                (.while_ (.ult (.var "r") (.stdVecLen "a"))
                  vecCopyIfBody) := rfl
            rw [hloop, evalProgStmt_while_true prog F _ _ _ hguardT,
              hshort]
          exact hwhile
        · have hsome : ∃ z, lo[w]? = some z := by
            match h : lo[w]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hlo64' : (lo.set w y).length < 2 ^ 64 := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hlo64
          have hfwd' : copyIfFwd x la (lo.set w y) G' (r + 1) (w + 1) =
              .error .AssertFail := by
            have h := hfwd
            simp only [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
              ⟨wB₁, hwB₁, hwN₁⟩, hx₁⟩ :=
            valCopyIfBody_copy prog F ρ la lo x r w rB wB y wOld
              hrN hwN hla64 hlo64 ha hout hx hr hw hlt hy hwget hkeep
          have hloop : evalProgStmt prog F vecCopyIfLoop ρ₁ =
              .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (lo := lo.set w y)
              (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
              (hrN := hrN₁) (hwN := hwN₁)
              (hlo64 := hlo64')
              (ha := ha₁) (hout := hout₁) (hx := hx₁)
              (hr := hrB₁) (hw := hwB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hfwd := hfwd')
          have hwhile : evalProgStmt prog (F + 1) vecCopyIfLoop ρ =
              .error .AssertFail := by
            cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
            exact hloop
          exact hwhile
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : copyIfFwd x la lo G' (r + 1) w =
            .error .AssertFail := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁⟩ :=
          valCopyIfBody_drop prog F ρ la lo x r w rB wB y
            hrN hwN hla64 ha hout hx hr hw hlt hy hdrop
        have hloop : evalProgStmt prog F vecCopyIfLoop ρ₁ =
            .error .AssertFail :=
          ih (G := G') (ρ := ρ₁) (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁) (hx := hx₁)
            (hr := hrB₁) (hw := hwB₁)
            (hle := by omega)
            (hF := hF') (hG := hG')
            (hfwd := hfwd')
        have hwhile : evalProgStmt prog (F + 1) vecCopyIfLoop ρ =
            .error .AssertFail := by
          cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
    · have him : r = la.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [copyIfFwd])
      | succ _ =>
        have hneg : ¬ la.length < la.length := by omega
        have hcon := hfwd
        simp only [copyIfFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)
