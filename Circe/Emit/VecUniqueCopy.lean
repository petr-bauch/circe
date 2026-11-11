/-
Caller-record squeeze (`std::unique_copy` idiom) over
`std::vector<int>` — the P2-M13 predecessor-kept scan writing
into a caller-sized output (pillar-2 proposed goal, P2-M16).

Corpus: `tests/cpp/vec_unique_copy.cpp` →
`tests/cir/vec_unique_copy.cir` (entry
`_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1_`: read-only `a` +
caller-sized `out`, `u64` survivor count out; the empty-check
early exit, the `out.at(0) = a.at(0)` seed store, then the
single `cir.while` squeeze scan with a conditional `out.at()`
store).

Model: the empty input returns 0 up front; otherwise the seed
store plants the first survivor (loud `AssertFail` when `out`
is empty — the M12 short-`out` discipline at index 0), `w` and
`r` seed at 1, and the loop keeps `a[r]` iff it differs from
the last recorded survivor `out[w - 1]` (the P2-M13 squeeze
test against the record, read through the direct `stdVecAt`
path — `1 ≤ w` plus the squeezed-prefix invariant keeps it in
bounds, the unique precedent); a kept element stores into
`out` at `w` through the checked `at()` path (inner `ult`
guard with `.fail`, so a short `out` is a loud `AssertFail`,
the copy_if precedent), then both cursors advance; dropped
elements advance only `r`. The endpoint returns the survivor
count `w`; the input `a` and the `out` suffix past `w` are
untouched — the caller owes `dedupAdj(a).length ≤ out.length`.
-/
import Circe.Emit.VecUnique
import Circe.Lemmas.TwoCursor

/-- Function name (Itanium mangling of a `vec_unique_copy` free
    function taking `const vector<int>&` + `vector<int>&`,
    returning `unsigned long`). -/
def vecUniqueCopyName : String :=
  "_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1_"

/-- Seed store: `out.at(0) = a.at(0)` through the checked `at()`
    path (the `ult` guard with `.fail`, so an empty `out` is a
    loud `AssertFail`); the `a` read is direct (the entry
    early exit guarantees `a` is nonempty). -/
def vecUniqueCopySeed : CStmt :=
  (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "out"))
    (.vecSet "out" (.lit (.u64 (BitVec.ofNat 64 0)))
      (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))))
    .fail)

/-- Previous-survivor read shared by the keep test (the
    `w - 1` predecessor index into the record). -/
def vecUniqueCopyPrev : CExpr :=
  (.stdVecAt "out" (.usub (.var "w") (.lit (.u64 (1 : BitVec 64)))))

/-- Loop body: keep `a[r]` iff it differs from the last
    recorded survivor `out[w - 1]` — the checked `out.at(w)`
    store (loud on short `out`) and both cursors advance; the
    read cursor always advances. -/
def vecUniqueCopyBody : CStmt :=
  (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
                      (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          .skip)
    (.assign "r" (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- Loop `while (r < n) body`. -/
def vecUniqueCopyLoop : CStmt :=
  (.while_ (.ult (.var "r") (.stdVecLen "a")) vecUniqueCopyBody)

/-- Whole function: the empty-check early exit, the seed store,
    the `let_` prelude binding `w` and `r` at 1, the loop, and
    the survivor count returns. -/
def vecUniqueCopyFunc : Func :=
  ⟨vecUniqueCopyName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 }],
   .u 64,
   (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
     (.seq vecUniqueCopySeed
       (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
         (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
           (.seq vecUniqueCopyLoop
             (.return_ (.var "w")))))))⟩

/-- Loop environment (input words + record words + `u64`
    cursors), in prelude `let_` cons order (`r` over `w` over
    `[a, out]`, so the entry bridge is `rfl`). -/
def mkUniqueCopyEnv (la lo : List (BitVec 32))
    (r w : BitVec 64) : Env :=
  [("r", .u64 r), ("w", .u64 w),
   ("a", .stdVecVal la), ("out", .stdVecVal lo)]

theorem mkUniqueCopyEnv_a (la lo : List (BitVec 32))
    (r w : BitVec 64) :
    envLookup (mkUniqueCopyEnv la lo r w) "a" =
      some (.stdVecVal la) := by
  simp [mkUniqueCopyEnv, envLookup, show ("a" : String) ≠ "r" by decide,
    show ("a" : String) ≠ "w" by decide]

theorem mkUniqueCopyEnv_out (la lo : List (BitVec 32))
    (r w : BitVec 64) :
    envLookup (mkUniqueCopyEnv la lo r w) "out" =
      some (.stdVecVal lo) := by
  simp [mkUniqueCopyEnv, envLookup, show ("out" : String) ≠ "r" by decide,
    show ("out" : String) ≠ "w" by decide,
    show ("out" : String) ≠ "a" by decide]

theorem mkUniqueCopyEnv_r (la lo : List (BitVec 32))
    (r w : BitVec 64) :
    envLookup (mkUniqueCopyEnv la lo r w) "r" = some (.u64 r) := by
  simp [mkUniqueCopyEnv, envLookup, show ("r" : String) ≠ "w" by decide]

theorem mkUniqueCopyEnv_w (la lo : List (BitVec 32))
    (r w : BitVec 64) :
    envLookup (mkUniqueCopyEnv la lo r w) "w" = some (.u64 w) := by
  simp [mkUniqueCopyEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: input words (fixed) + record words + fuel +
    read cursor + write cursor. Fuel 0 returns the state so far
    (the V1 miss-default idiom); the `none` arms are
    unreachable in-invariant (the `a` reads are guard-justified,
    the `out` predecessor read rides the squeezed-prefix
    invariant, the keep-store miss is the loud short-`out`
    leg). -/
def uniqueCopyFwd (la : List (BitVec 32)) :
    List (BitVec 32) → Nat → Nat → Nat →
      Result (Nat × Nat × List (BitVec 32))
  | lo, 0, r, w => .ok (r, w, lo)
  | lo, fuel + 1, r, w =>
    if _ : r < la.length then
      match la[r]?, lo[w - 1]? with
      | some y, some p =>
        if (y != p) then
          match lo[w]? with
          | none => .error .AssertFail
          | some _ => uniqueCopyFwd la (lo.set w y) fuel (r + 1) (w + 1)
        else uniqueCopyFwd la lo fuel (r + 1) w
      | _, _ => .error .AssertFail
    else .ok (r, w, lo)

/-- Whole-function forward: the empty input returns 0 (the
    entry early exit); a nonempty input with an empty record
    fails loud at the seed; otherwise the loop at measure-exact
    fuel from the (1, 1) seed over the seeded record, then the
    survivor count. -/
def vecUniqueCopyFwd (la lo : List (BitVec 32)) : Result Value :=
  match la with
  | [] => .ok (.u64 (BitVec.ofNat 64 0))
  | a0 :: _ =>
    match lo[0]? with
    | none => .error .AssertFail
    | some _ =>
      match uniqueCopyFwd la (lo.set 0 a0) la.length 1 1 with
      | .error e => .error e
      | .ok (_, w', _) => .ok (.u64 (BitVec.ofNat 64 w'))

/-- Program over which the entry evaluates (no callees: the
    body is straight-line `if` / `vecSet` / `assign` /
    `fail`). -/
abbrev vecUniqueCopyProg : Prog := [vecUniqueCopyFunc]

/-! ## Seed store (bridges the prelude to `uniqueCopyFwd`) -/

/-- Seed store, hit branch: `out` is nonempty, so the checked
    seed store plants `a[0]` at record index 0. -/
theorem valUniqueCopySeed_hit (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32)) (a0 o0 : BitVec 32)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (ha0 : la[0]? = some a0) (ho0 : lo[0]? = some o0) :
    ∃ ρ', evalProgStmt prog F vecUniqueCopySeed ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set 0 a0)) := by
  have h0lt : 0 < lo.length := transformRead_lt lo 0 o0 ho0
  have h0N : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardT :
      evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
        (.stdVecLen "out")) ρ = .ok (.b true) := by
    have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 lo.length) (.stdVecLen "out") ρ
      (evalExpr_stdVecLen_some _ _ _ hout)
    have htb : ((BitVec.ofNat 64 0).ult
        (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide, h0N, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hatA : evalExpr
      (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
      .ok (.i32 a0) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hlit (by rw [h0N]; exact ha0)
  have hgetO : lo[(BitVec.ofNat 64 0).toNat]? = some o0 := by
    rw [h0N]; exact ho0
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo)
    (.stdVecVal (lo.set (BitVec.ofNat 64 0).toNat a0)) hout
  have hstep_set := revVecSet prog F "out"
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0))))
    ρ (BitVec.ofNat 64 0) a0 lo o0 ρ₁ hlit hatA hout hgetO hu₁
  have hsetB : lo.set (BitVec.ofNat 64 0).toNat a0
      = lo.set 0 a0 := by rw [h0N]
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "out" by decide) hu₁]
    exact ha
  have hupd := envLookup_update_hit _ _ _ _ hu₁
  have hout₁ : envLookup ρ₁ "out"
      = some (.stdVecVal (lo.set 0 a0)) := by
    rwa [hsetB] at hupd
  have hif : evalProgStmt prog F
      (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
              (.stdVecLen "out"))
        (.vecSet "out" (.lit (.u64 (BitVec.ofNat 64 0)))
          (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail) ρ = .ok (ρ₁, .fellThrough) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hstep_set
  have hseed : vecUniqueCopySeed =
      (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
              (.stdVecLen "out"))
        (.vecSet "out" (.lit (.u64 (BitVec.ofNat 64 0)))
          (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail) := rfl
  have heval : evalProgStmt prog F vecUniqueCopySeed ρ =
      .ok (ρ₁, .fellThrough) := by
    rw [hseed]; exact hif
  exact ⟨ρ₁, heval, ha₁, hout₁⟩

/-- Seed store, short branch: `out` is empty, so the checked
    seed store fails loud. -/
theorem valUniqueCopySeed_short (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32)) (a0 : BitVec 32)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (ha0 : la[0]? = some a0) (hmiss : lo[0]? = none) :
    evalProgStmt prog F vecUniqueCopySeed ρ = .error .AssertFail := by
  have hnl : ¬ 0 < lo.length := by
    intro h
    have hsome : lo[0]? = some lo[0] := List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have h0N : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardF :
      evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
        (.stdVecLen "out")) ρ = .ok (.b false) := by
    have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 lo.length) (.stdVecLen "out") ρ
      (evalExpr_stdVecLen_some _ _ _ hout)
    have hfb : ((BitVec.ofNat 64 0).ult
        (BitVec.ofNat 64 lo.length)) = false := by
      rw [BitVec.ult_eq_decide, h0N, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hfail : evalProgStmt prog F .fail ρ = .error .AssertFail := by
    simpa [evalProgStmt] using (evalStmtFuel_fail F ρ)
  have hseed : vecUniqueCopySeed =
      (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
              (.stdVecLen "out"))
        (.vecSet "out" (.lit (.u64 (BitVec.ofNat 64 0)))
          (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail) := rfl
  rw [hseed]
  exact (evalProgStmt_if_false _ _ _ _ _ _ hguardF).trans hfail

/-! ## Loop body (bridges `evalProgStmt` to `uniqueCopyFwd`) -/

/-- One body iteration (value level), keep branch: the `une`
    test against the last recorded survivor fires, the `out`
    guard holds, the survivor stores at `w`, both cursors
    advance. -/
theorem valUniqueCopyBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p wOld : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length) (hw1 : 1 ≤ w)
    (hy : la[r]? = some y) (hp : lo[w - 1]? = some p)
    (hwget : lo[w]? = some wOld)
    (hkeep : (y != p) = true) :
    ∃ ρ', evalProgStmt prog F vecUniqueCopyBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) := by
  have hwlt : w < lo.length := transformRead_lt lo w wOld hwget
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hwN, h1]
  have hgetP : lo[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hatP : evalExpr vecUniqueCopyPrev ρ = .ok (.i32 p) := by
    show evalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = _
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hout hsub hgetP
  have hune : evalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ y p hatR hatP
    rwa [hkeep] at h
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardT : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ wB
      (BitVec.ofNat 64 lo.length)
      (evalExpr_var_hit _ _ _ hw)
      (evalExpr_stdVecLen_some _ _ _ hout)
    have htb : (wB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hsetB : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  have hgetW : lo[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout
  have hstep_set := revVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "r")) ρ wB y lo wOld ρ₁ hwVar hatR hout
    hgetW hu₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "out" _ ρ₁
      (show ("a" : String) ≠ "out" by decide) hu₁
    rw [h]; exact ha
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "out" _ ρ₁
      (show ("r" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hr
  have hwVar₁ : evalExpr (.var "w") ρ₁ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _
      (by rw [envLookup_update_miss _ _ _ _ _
        (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw)
  have hevW : evalExpr (.uadd (.var "w")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hwVar₁ (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "w"
    (.u64 wB) (.u64 (wB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw)
  have hstep_w := revAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (wB + 1)) ρ₂ hevW hu₂
  have hr₂ : envLookup ρ₂ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "w" by decide) hu₂]
    exact hr₁
  have ha₂ : envLookup ρ₂ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₂]
    exact ha₁
  have hrVar₂ : evalExpr (.var "r") ρ₂ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr₂
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hrVar₂ (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) hr₂
  have hstep_r := revAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂
    (.u64 (rB + 1)) ρ₃ hevR hu₃
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
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ = .ok (ρ₂, .fellThrough) := by
    have hthen : evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ = .ok (ρ₂, .fellThrough) := by
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
        hstep_w]
    exact (evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hthen
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        .skip) ρ = .ok (ρ₂, .fellThrough) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hune).trans hinner
  have hbody : vecUniqueCopyBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
                    (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : evalProgStmt prog F vecUniqueCopyBody ρ =
      .ok (ρ₃, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, heval, ha₃, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩⟩

/-- One body iteration (value level), short-`out` branch: the
    `une` test fires but `w` is past the record, so the inner
    guard fails and the loud `.fail` leg fires. -/
theorem valUniqueCopyBody_short (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length) (hw1 : 1 ≤ w)
    (hy : la[r]? = some y) (hp : lo[w - 1]? = some p)
    (hmiss : lo[w]? = none)
    (hkeep : (y != p) = true) :
    evalProgStmt prog F vecUniqueCopyBody ρ = .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hwN, h1]
  have hgetP : lo[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hatP : evalExpr vecUniqueCopyPrev ρ = .ok (.i32 p) := by
    show evalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = _
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hout hsub hgetP
  have hune : evalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ y p hatR hatP
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
      rw [BitVec.ult_eq_decide, hwN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hfail : evalProgStmt prog F .fail ρ = .error .AssertFail := by
    simpa [evalProgStmt] using (evalStmtFuel_fail F ρ)
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ = .error .AssertFail :=
    (evalProgStmt_if_false _ _ _ _ _ _ hguardF).trans hfail
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        .skip) ρ = .error .AssertFail :=
    (evalProgStmt_if_true _ _ _ _ _ _ hune).trans hinner
  have hbody : vecUniqueCopyBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
                    (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  exact evalProgStmt_seq_err _ _ _ _ _ _ hif

/-- One body iteration (value level), drop branch: the `une`
    test against the last recorded survivor fails, the state
    threads untouched, only `r` advances. -/
theorem valUniqueCopyBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length) (hw1 : 1 ≤ w)
    (hy : la[r]? = some y) (hp : lo[w - 1]? = some p)
    (hdrop : (y != p) = false) :
    ∃ ρ', evalProgStmt prog F vecUniqueCopyBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hwN, h1]
  have hgetP : lo[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hatP : evalExpr vecUniqueCopyPrev ρ = .ok (.i32 p) := by
    show evalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = _
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hout hsub hgetP
  have hune : evalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ =
      .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ y p hatR hatP
    rwa [hdrop] at h
  have hskipV : evalProgStmt prog F .skip ρ =
      .ok (ρ, .fellThrough) := by
    simpa [evalProgStmt] using
      (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        .skip) ρ = .ok (ρ, .fellThrough) :=
    (evalProgStmt_if_false _ _ _ _ _ _ hune).trans hskipV
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hrVar (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "r"
    (.u64 rB) (.u64 (rB + 1)) hr
  have hstep_r := revAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ
    (.u64 (rB + 1)) ρ' hevR hu
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
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ' "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : vecUniqueCopyBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
                    (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : evalProgStmt prog F vecUniqueCopyBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', heval, ha', hout', ⟨(rB + 1), hr', hrN'⟩, ⟨wB, hw', hwN⟩⟩

/-! ## Value loop (bridges `evalProgStmt` to `uniqueCopyFwd`) -/

/-- Take-set at the write head: storing at `w` then taking
    `w + 1` is the old `w`-prefix with the new word snocced.
    (No core lemma packages both steps; the two rewrites below
    are the only use.) -/
theorem take_set_succ_self (lo : List (BitVec 32)) (w : Nat)
    (y : BitVec 32) (hwlt : w < lo.length) :
    (lo.set w y).take (w + 1) = (lo.take w) ++ [y] := by
  have h1 : (lo.set w y).take w = lo.take w :=
    List.take_set_of_le (Nat.le_refl w)
  have h2 : ((lo.set w y)[w]?.toList) = [y] :=
    congrArg Option.toList (List.getElem?_set_self hwlt)
  have h3 : (lo.set w y).take (w + 1)
      = (lo.set w y).take w ++ ((lo.set w y)[w]?.toList) :=
    List.take_add_one
  rw [h3, h1, h2]

/-- Value loop, ok leg: the scan runs to `la.length` and the
    record is the forward-model result (fuel induction threading
    the body hits; the forward equation unfolds one step per
    iteration; the squeezed-prefix invariant plus `1 ≤ w`
    justifies every predecessor read, and the short-`out` leg is
    vacuous against the `ok` forward equation). -/
theorem valUniqueCopyLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (la : List (BitVec 32)) (lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64)
    (lo' : List (BitVec 32)) (r' w' : Nat)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ la.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hwlo : w ≤ lo.length)
    (hpre : lo.take w = dedupAdj (la.take r))
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hfwd : uniqueCopyFwd la lo G r w = .ok (r', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecUniqueCopyLoop ρ =
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
    have hexit : evalProgStmt prog 0 vecUniqueCopyLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (r, w, lo) = (r', w', lo') := by
      cases G with
      | zero => simpa [uniqueCopyFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < la.length := by omega
        simpa [uniqueCopyFwd, dite_eq_right hneg] using hfwd
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
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      have hlast : (dedupAdj (la.take r)).getLast? = some p := by
        rw [← hpre]
        exact take_getLast_of_getElem? lo w p hw1 hwlo hpred
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != p) = true
      · by_cases hmiss : lo[w]? = none
        · have hcon := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hkeep, hmiss] at hcon
          exact absurd hcon (by simp)
        · have hsome : ∃ z, lo[w]? = some z := by
            match h : lo[w]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : w < lo.length :=
            transformRead_lt lo w wOld hwget
          have htake_set : (lo.set w y).take (w + 1)
              = (lo.take w) ++ [y] :=
            take_set_succ_self lo w y hwlt
          have hpre' : (lo.set w y).take (w + 1)
              = dedupAdj (la.take (r + 1)) := by
            rw [htake_set, hpre,
              dedupAdj_take_succ_keep la r y p hy hlast hkeep]
          have hlo64' : (lo.set w y).length < 2 ^ 64 := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hlo64
          have hwlo' : w + 1 ≤ (lo.set w y).length := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            omega
          have hreadLo' : ∀ p, p < (lo.set w y).length →
              ∃ z, ((lo.set w y)[p]? = some z) := by
            intro p hp
            have hplen : p < lo.length := by
              have hlen : (lo.set w y).length = lo.length := by
                simp [List.length_set]
              omega
            by_cases hpw : p = w
            · rw [hpw]
              exact ⟨y, List.getElem?_set_self hwlt⟩
            · obtain ⟨z, hz⟩ := hreadLo p hplen
              exact ⟨z, by
                rw [List.getElem?_set_ne (show w ≠ p by omega)]
                exact hz⟩
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : uniqueCopyFwd la (lo.set w y) G' (r + 1)
              (w + 1) = .ok (r', w', lo') := by
            have h := hfwd
            simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
              hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
              ⟨wB₁, hwB₁, hwN₁⟩⟩ :=
            valUniqueCopyBody_keep prog F ρ la lo r w rB wB y p wOld
              hrN hwN hla64 hlo64 ha hout hr hw hlt hw1 hy hpred
              hwget hkeep
          obtain ⟨ρ', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
              ⟨wB', hwB', hwN'⟩⟩ :=
            ih (G := G') (ρ := ρ₁) (lo := lo.set w y)
              (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
              (hrN := hrN₁) (hwN := hwN₁) (hlo64 := hlo64')
              (ha := ha₁) (hout := hout₁)
              (hr := hrB₁) (hw := hwB₁)
              (hle := by omega) (hwle := by omega) (hw1 := by omega)
              (hwlo := hwlo') (hpre := hpre')
              (hF := hF'') (hG := hG'')
              (hreadLo := hreadLo')
              (hfwd := hfwd')
          refine ⟨ρ', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩⟩
          have hwhile : evalProgStmt prog (F + 1) vecUniqueCopyLoop ρ =
              evalProgStmt prog F vecUniqueCopyLoop ρ₁ := by
            cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
          rw [hwhile]
          exact hloop
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hpre' : lo.take w = dedupAdj (la.take (r + 1)) := by
          rw [dedupAdj_take_succ_drop la r y p hy hlast hdrop, hpre]
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : uniqueCopyFwd la lo G' (r + 1) w =
            .ok (r', w', lo') := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hdrop] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩⟩ :=
          valUniqueCopyBody_drop prog F ρ la lo r w rB wB y p
            hrN hwN hla64 ha hout hr hw hlt hw1 hy hpred hdrop
        obtain ⟨ρ', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁)
            (hr := hrB₁) (hw := hwB₁)
            (hle := by omega) (hwle := by omega) (hw1 := hw1)
            (hwlo := hwlo) (hpre := hpre')
            (hF := hF') (hG := hG')
            (hreadLo := hreadLo)
            (hfwd := hfwd')
        refine ⟨ρ', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecUniqueCopyLoop ρ =
            evalProgStmt prog F vecUniqueCopyLoop ρ₁ := by
          cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
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
      have hexit : evalProgStmt prog (F + 1) vecUniqueCopyLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (la.length, w, lo) = (r', w', lo') := by
        cases G with
        | zero => simpa [uniqueCopyFwd] using hfwd
        | succ G =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [uniqueCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hout, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩⟩

/-- Value loop, short-`out` error leg: the first overflowing
    keep aborts loudly (fuel induction; the forward equation
    threads). -/
theorem valUniqueCopyLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (la : List (BitVec 32)) (lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ la.length) (hw1 : 1 ≤ w) (hwlo : w ≤ lo.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hfwd : uniqueCopyFwd la lo G r w = .error .AssertFail) :
    evalProgStmt prog F vecUniqueCopyLoop ρ = .error .AssertFail := by
  induction F generalizing G ρ lo r w rB wB with
  | zero =>
    have him : r = la.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [uniqueCopyFwd])
    | succ _ =>
      have hneg : ¬ la.length < la.length := by omega
      have hcon := hfwd
      simp only [uniqueCopyFwd, dite_eq_right hneg] at hcon
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
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != p) = true
      · by_cases hmiss : lo[w]? = none
        · have hshort := valUniqueCopyBody_short prog F ρ la lo r w
            rB wB y p hrN hwN hlo64 ha hout hr hw hlt hw1 hy hpred
            hmiss hkeep
          have hwhile : evalProgStmt prog (F + 1) vecUniqueCopyLoop ρ =
              .error .AssertFail := by
            have hloop : vecUniqueCopyLoop =
                (.while_ (.ult (.var "r") (.stdVecLen "a"))
                  vecUniqueCopyBody) := rfl
            rw [hloop, evalProgStmt_while_true prog F _ _ _ hguardT,
              hshort]
          exact hwhile
        · have hsome : ∃ z, lo[w]? = some z := by
            match h : lo[w]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : w < lo.length :=
            transformRead_lt lo w wOld hwget
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hlo64' : (lo.set w y).length < 2 ^ 64 := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hlo64
          have hreadLo' : ∀ p, p < (lo.set w y).length →
              ∃ z, ((lo.set w y)[p]? = some z) := by
            intro p hp
            have hplen : p < lo.length := by
              have hlen : (lo.set w y).length = lo.length := by
                simp [List.length_set]
              omega
            by_cases hpw : p = w
            · rw [hpw]
              exact ⟨y, List.getElem?_set_self hwlt⟩
            · obtain ⟨z, hz⟩ := hreadLo p hplen
              exact ⟨z, by
                rw [List.getElem?_set_ne (show w ≠ p by omega)]
                exact hz⟩
          have hfwd' : uniqueCopyFwd la (lo.set w y) G' (r + 1)
              (w + 1) = .error .AssertFail := by
            have h := hfwd
            simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
              hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
              ⟨wB₁, hwB₁, hwN₁⟩⟩ :=
            valUniqueCopyBody_keep prog F ρ la lo r w rB wB y p wOld
              hrN hwN hla64 hlo64 ha hout hr hw hlt hw1 hy hpred
              hwget hkeep
          have hloop : evalProgStmt prog F vecUniqueCopyLoop ρ₁ =
              .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (lo := lo.set w y)
              (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
              (hrN := hrN₁) (hwN := hwN₁) (hlo64 := hlo64')
              (ha := ha₁) (hout := hout₁)
              (hr := hrB₁) (hw := hwB₁)
              (hle := by omega) (hw1 := by omega)
              (hwlo := by
                have hlen : (lo.set w y).length = lo.length := by
                  simp [List.length_set]
                omega)
              (hF := hF'') (hG := hG'')
              (hreadLo := hreadLo')
              (hfwd := hfwd')
          have hwhile : evalProgStmt prog (F + 1) vecUniqueCopyLoop ρ =
              .error .AssertFail := by
            cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
            exact hloop
          exact hwhile
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : uniqueCopyFwd la lo G' (r + 1) w =
            .error .AssertFail := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hdrop] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩⟩ :=
          valUniqueCopyBody_drop prog F ρ la lo r w rB wB y p
            hrN hwN hla64 ha hout hr hw hlt hw1 hy hpred hdrop
        have hloop : evalProgStmt prog F vecUniqueCopyLoop ρ₁ =
            .error .AssertFail :=
          ih (G := G') (ρ := ρ₁) (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁)
            (hr := hrB₁) (hw := hwB₁)
            (hle := by omega) (hw1 := hw1)
            (hwlo := hwlo)
            (hF := hF') (hG := hG')
            (hreadLo := hreadLo)
            (hfwd := hfwd')
        have hwhile : evalProgStmt prog (F + 1) vecUniqueCopyLoop ρ =
            .error .AssertFail := by
          cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
    · have him : r = la.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [uniqueCopyFwd])
      | succ _ =>
        have hneg : ¬ la.length < la.length := by omega
        have hcon := hfwd
        simp only [uniqueCopyFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)
