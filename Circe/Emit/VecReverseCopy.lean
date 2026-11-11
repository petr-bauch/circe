import Circe.Emit.VecUnique
import Circe.Lemmas.TwoCursor

/-! Pillar-2 goal #17: out-of-place reverse (`vec_reverse_copy`,
the M12 reversal into a caller-sized record) — the countdown read
cursor `j` (seeded at `a.size()`, `0 < j` guard, the M12
discipline) meets the M16 sequential write cursor `w` (seeded at
0). The empty vector short-circuits up front, so there is no seed
leg: every store is guarded by the same per-step `w < out.size()`
check. The invariant ties the two cursors to the record
(`lo.take w = (la.drop j).reverse`, `w + j = la.length`); at exit
`j = 0` gives the full `la.reverse`. Pure `List.reverse` oracle:
no new oracle module. -/

/-- Function name (Itanium mangling of a `vec_reverse_copy` free
    function taking `const vector<int>&` and `vector<int>&`,
    returning `unsigned long`). -/
def vecReverseCopyName : String :=
  "_Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1_"

/-- Loop body: decrement `j` (the countdown, unconditional like
    the CIR `sub`), then — guarded by `w < out.size()` — store
    `a[j]` at `out[w]` and advance `w`; otherwise loud
    `AssertFail`. -/
def vecReverseCopyBody : CStmt :=
  (.seq (.assign "j"
           (.usub (.var "j") (.lit (.u64 (1 : BitVec 64)))))
    (.if_ (.ult (.var "w") (.stdVecLen "out"))
      (.seq (.vecSet "out" (.var "w")
               (.stdVecAt "a" (.var "j")))
        (.assign "w" (.uadd (.var "w")
          (.lit (.u64 (1 : BitVec 64))))))
      .fail))

/-- Loop `while (0 < j) body`. -/
def vecReverseCopyLoop : CStmt :=
  (.while_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
    vecReverseCopyBody)

/-- Whole function: the empty-check early exit, then the `let_`
    prelude binding `w` at 0 and `j` at `a.size()`, the loop, and
    the copied-count return (the M12/M16 convention). -/
def vecReverseCopyFunc : Func :=
  ⟨vecReverseCopyName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 }],
   .u 64,
   (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
     (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq (.let_ "j" (.u 64) (.stdVecLen "a"))
         (.seq vecReverseCopyLoop
           (.return_ (.var "w"))))))⟩

/-- Loop environment (borrowed words + `u64` cursors), in prelude
    `let_` cons order (`j` over `w` over `[a, out]`, so the entry
    bridge is `rfl`). -/
def mkReverseCopyEnv (la lo : List (BitVec 32)) (w j : BitVec 64) : Env :=
  [("j", .u64 j), ("w", .u64 w),
   ("a", .stdVecVal la), ("out", .stdVecVal lo)]

theorem mkReverseCopyEnv_a (la lo : List (BitVec 32)) (w j : BitVec 64) :
    envLookup (mkReverseCopyEnv la lo w j) "a" =
      some (.stdVecVal la) := by
  simp [mkReverseCopyEnv, envLookup,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "w" by decide]

theorem mkReverseCopyEnv_out (la lo : List (BitVec 32)) (w j : BitVec 64) :
    envLookup (mkReverseCopyEnv la lo w j) "out" =
      some (.stdVecVal lo) := by
  simp [mkReverseCopyEnv, envLookup,
    show ("out" : String) ≠ "j" by decide,
    show ("out" : String) ≠ "w" by decide,
    show ("out" : String) ≠ "a" by decide]

theorem mkReverseCopyEnv_w (la lo : List (BitVec 32)) (w j : BitVec 64) :
    envLookup (mkReverseCopyEnv la lo w j) "w" = some (.u64 w) := by
  simp [mkReverseCopyEnv, envLookup,
    show ("w" : String) ≠ "j" by decide]

theorem mkReverseCopyEnv_j (la lo : List (BitVec 32)) (w j : BitVec 64) :
    envLookup (mkReverseCopyEnv la lo w j) "j" = some (.u64 j) := by
  simp [mkReverseCopyEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + source words + record words + write head +
    countdown. Fuel 0 returns the state so far; the `none` arm of
    the source read is unreachable in-invariant (the guard gives
    `j ≥ 1`, so `j - 1 < la.length` — no core lemma packages
    this, hence the local `hread`). The record slot is cased like
    the evaluator: a miss fails loud, so no capacity hypothesis
    here. -/
def reverseCopyFwd :
    List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat →
      Result (Nat × Nat × List (BitVec 32))
  | _, lo, 0, w, j => .ok (w, j, lo)
  | la, lo, fuel + 1, w, j =>
    if _ : 0 < j then
      match la[j - 1]?, lo[w]? with
      | some y, some _ => reverseCopyFwd la (lo.set w y) fuel (w + 1) (j - 1)
      | _, _ => .error .AssertFail
    else .ok (w, j, lo)

/-- Whole-function forward: the empty vector returns 0 (the entry
    early exit), otherwise the loop at measure-exact fuel from the
    `(0, la.length)` cursors, then the copied count. -/
def vecReverseCopyFwd (la lo : List (BitVec 32)) : Result Value :=
  match la with
  | [] => .ok (.u64 (BitVec.ofNat 64 0))
  | _ :: _ =>
    match reverseCopyFwd la lo la.length 0 la.length with
    | .error e => .error e
    | .ok (w', _, _) => .ok (.u64 (BitVec.ofNat 64 w'))

/-- Program over which the entry evaluates (no callees: the body
    is straight-line `assign` / `if` / `vecSet`). -/
abbrev vecReverseCopyProg : Prog := [vecReverseCopyFunc]

/-! ## Value loop (bridges `evalProgStmt` to `reverseCopyFwd`) -/

/-- One body iteration (value level), keep branch: `j`
    decrements through `usub`, the capacity guard holds, the store
    lands and `w` advances. -/
theorem valReverseCopyBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (la lo : List (BitVec 32))
    (w j : Nat) (wB jB : BitVec 64) (y wOld : BitVec 32)
    (hwN : wB.toNat = w) (hjN : jB.toNat = j)
    (_hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hj1 : 1 ≤ j)
    (hy : la[j - 1]? = some y)
    (hwget : lo[w]? = some wOld) :
    ∃ ρ', evalProgStmt prog F vecReverseCopyBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j - 1) := by
  have hwlt : w < lo.length := transformRead_lt lo w wOld hwget
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  -- `--j` (unconditional, like the CIR `sub`).
  have hexpr_j : evalExpr (.usub (.var "j")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (jB - 1)) :=
    evalExpr_u64_usub jB 1 (.var "j") ρ hjVar
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB - 1)) hj
  have hstep_j := revAssign prog F "j"
    (.usub (.var "j") (.lit (.u64 (1 : BitVec 64)))) ρ
    (.u64 (jB - 1)) ρ₁ hexpr_j hu₁
  have hj₁ : envLookup ρ₁ "j" = some (.u64 (jB - 1)) :=
    envLookup_update_hit _ _ _ _ hu₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₁]
    exact ha
  have hout₁ : envLookup ρ₁ "out" = some (.stdVecVal lo) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₁]
    exact hout
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₁]
    exact hw
  have hjN' : (jB - 1).toNat = j - 1 := by
    rw [revU64_pred_toNat jB (by omega : 1 ≤ jB.toNat), hjN]
  have hjVar₁ : evalExpr (.var "j") ρ₁ = .ok (.u64 (jB - 1)) :=
    evalExpr_var_hit _ _ _ hj₁
  have hwVar₁ : evalExpr (.var "w") ρ₁ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw₁
  have hget : la[(jB - 1).toNat]? = some y := by
    rw [hjN']; exact hy
  have hatA : evalExpr (.stdVecAt "a" (.var "j")) ρ₁ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha₁ hjVar₁ hget
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardT : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ₁ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ₁ wB
      (BitVec.ofNat 64 lo.length) hwVar₁
      (evalExpr_stdVecLen_some _ _ _ hout₁)
    have htb : (wB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide, hwN, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hsetB : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  have hgetW : lo[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout₁
  have hstep_set := revVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "j")) ρ₁ wB y lo wOld ρ₂ hwVar₁ hatA hout₁
    hgetW hu₂
  have hj₂ : envLookup ρ₂ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "out" by decide) hu₂]
    exact hj₁
  have ha₂ : envLookup ρ₂ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "out" by decide) hu₂]
    exact ha₁
  have hevW : evalExpr (.uadd (.var "w")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("w" : String) ≠ "out" by decide) hu₂]; exact hw₁))
      (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "w"
    (.u64 wB) (.u64 (wB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "out" by decide) hu₂]; exact hw₁)
  have hstep_w := revAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂
    (.u64 (wB + 1)) ρ₃ hevW hu₃
  have hout₃ : envLookup ρ₃ "out" =
      some (.stdVecVal (lo.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₃]
    have h := envLookup_update_hit _ _ _ _ hu₂
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₃]
    exact ha₂
  have hj₃ : envLookup ρ₃ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "w" by decide) hu₃]
    exact hj₂
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hw' : envLookup ρ₃ "w" = some (.u64 (wB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "j")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ₁ = .ok (ρ₃, .fellThrough) := by
    have hthen : evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "j")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ₁ = .ok (ρ₃, .fellThrough) := by
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
        hstep_w]
    exact (evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hthen
  have hbody : vecReverseCopyBody =
      (.seq (.assign "j" (.usub (.var "j")
             (.lit (.u64 (1 : BitVec 64)))))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "j")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) := rfl
  rw [hbody]
  refine ⟨ρ₃, (evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_j).trans
    hinner, ha₃, hout₃, ⟨_, hw', hwN'⟩, ⟨_, hj₃, ?_⟩⟩
  rw [hjN']

/-- One body iteration (value level), short-record branch: `j`
    decrements, the capacity guard fails, loud `AssertFail`. -/
theorem valReverseCopyBody_short (prog : Prog) (F : Nat)
    (ρ : Env) (lo : List (BitVec 32))
    (w : Nat) (wB jB : BitVec 64)
    (hwN : wB.toNat = w)
    (hlo64 : lo.length < 2 ^ 64)
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hmiss : lo[w]? = none) :
    evalProgStmt prog F vecReverseCopyBody ρ = .error .AssertFail := by
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hexpr_j : evalExpr (.usub (.var "j")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (jB - 1)) :=
    evalExpr_u64_usub jB 1 (.var "j") ρ hjVar
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB - 1)) hj
  have hstep_j := revAssign prog F "j"
    (.usub (.var "j") (.lit (.u64 (1 : BitVec 64)))) ρ
    (.u64 (jB - 1)) ρ₁ hexpr_j hu₁
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₁]
    exact hw
  have hout₁ : envLookup ρ₁ "out" = some (.stdVecVal lo) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₁]
    exact hout
  have hnl : ¬ w < lo.length := by
    intro h
    have hsome : lo[w]? = some lo[w] := List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardF : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ₁ =
      .ok (.b false) := by
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ₁ wB
      (BitVec.ofNat 64 lo.length)
      (evalExpr_var_hit _ _ _ hw₁)
      (evalExpr_stdVecLen_some _ _ _ hout₁)
    have hfb : (wB.ult (BitVec.ofNat 64 lo.length)) = false := by
      rw [BitVec.ult_eq_decide, hwN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hfail : evalProgStmt prog F .fail ρ₁ = .error .AssertFail := by
    simpa [evalProgStmt] using (evalStmtFuel_fail F ρ₁)
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "j")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ₁ = .error .AssertFail :=
    (evalProgStmt_if_false _ _ _ _ _ _ hguardF).trans hfail
  have hbody : vecReverseCopyBody =
      (.seq (.assign "j" (.usub (.var "j")
             (.lit (.u64 (1 : BitVec 64)))))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "j")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) := rfl
  rw [hbody]
  exact evalProgStmt_seq_fallthrough_trans _ _ _ _ _ _ _ hstep_j hinner

/-- Loop bridge (value level), ok leg: the countdown/record
    invariant threads through the loop to the forward model. -/
theorem valReverseCopyLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (la : List (BitVec 32)) (lo : List (BitVec 32))
    (w j : Nat) (wB jB : BitVec 64)
    (lo' : List (BitVec 32)) (w' j' : Nat)
    (hwN : wB.toNat = w) (hjN : jB.toNat = j)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hwj : w + j = la.length) (hle : j ≤ la.length)
    (hwlo : w ≤ lo.length)
    (hpre : lo.take w = (la.drop j).reverse)
    (hF : j ≤ F) (hG : j ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : reverseCopyFwd la lo G w j = .ok (w', j', lo')) :
    ∃ ρ', evalProgStmt prog F vecReverseCopyLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') := by
  induction F generalizing G ρ lo w j wB jB with
  | zero =>
    have hj0 : j = 0 := by omega
    have hguardF : evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
        jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
      have hfb : ((BitVec.ofNat 64 0).ult jB) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt prog 0 vecReverseCopyLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (w, j, lo) = (w', j', lo') := by
      cases G with
      | zero => simpa [reverseCopyFwd] using hfwd
      | succ G =>
        have hneg : ¬ 0 < j := by omega
        simpa [reverseCopyFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hout, ⟨wB, hw, hwN⟩, ⟨jB, hj, hjN⟩⟩
  | succ F ih =>
    by_cases hj0 : 0 < j
    · have hguardT : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
          jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
        have h0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
        have htb : ((BitVec.ofNat 64 0).ult jB) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨y, hy⟩ := hread (j - 1) (by omega)
      cir_fuel_step (F, G, j - 1)
      by_cases hmiss : lo[w]? = none
      · have hcon := hfwd
        simp only [reverseCopyFwd, dite_eq_left hj0, hy,
          hmiss] at hcon
        exact absurd hcon (by simp)
      · have hsome : ∃ z, lo[w]? = some z := by
          match h : lo[w]? with
          | none => exact absurd h hmiss
          | some z => exact ⟨z, rfl⟩
        obtain ⟨wOld, hwget⟩ := hsome
        have hwlt : w < lo.length := transformRead_lt lo w wOld hwget
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = ((la.drop (j - 1))).reverse := by
          rw [htake_set, hpre,
            drop_reverse_succ la j y (by omega) hy]
        have hlo64' : (lo.set w y).length < 2 ^ 64 := by
          rw [List.length_set]; exact hlo64
        have hlen : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by omega
        have hwj' : (w + 1) + (j - 1) = la.length := by omega
        have hF'' : j - 1 ≤ F := by omega
        have hG'' : j - 1 ≤ G' := by omega
        have hfwd' : reverseCopyFwd la (lo.set w y) G' (w + 1)
            (j - 1) = .ok (w', j', lo') := by
          have h := hfwd
          simp only [reverseCopyFwd, dite_eq_left hj0, hy,
            hwget] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨wB₁, hwB₁, hwN₁⟩,
            ⟨jB₁, hjB₁, hjN₁⟩⟩ :=
          valReverseCopyBody_keep prog F ρ la lo w j wB jB y wOld
            hwN hjN hla64 hlo64 ha hout hw hj (by omega) hy hwget
        obtain ⟨ρ', hloop, ha', hout', ⟨wB', hwB', hwN'⟩,
            ⟨jB', hjB', hjN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (lo := lo.set w y)
            (w := w + 1) (j := j - 1) (wB := wB₁) (jB := jB₁)
            (hwN := hwN₁) (hjN := hjN₁) (hlo64 := hlo64')
            (ha := ha₁) (hout := hout₁)
            (hw := hwB₁) (hj := hjB₁)
            (hwj := hwj') (hle := by omega) (hwlo := hwlo')
            (hpre := hpre')
            (hF := hF'') (hG := hG'')
            (hfwd := hfwd')
        refine ⟨ρ', ?_, ha', hout', ⟨wB', hwB', hwN'⟩,
          ⟨jB', hjB', hjN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecReverseCopyLoop ρ =
            evalProgStmt prog F vecReverseCopyLoop ρ₁ := by
          cir_unfold_prog (vecReverseCopyLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have hguardF : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
          jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
        have hfb : ((BitVec.ofNat 64 0).ult jB) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt prog (F + 1) vecReverseCopyLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _
          vecReverseCopyBody _ hguardF
      have hj0' : j = 0 := by omega
      subst hj0'
      have hpair : (w, 0, lo) = (w', j', lo') := by
        cases G with
        | zero => simpa [reverseCopyFwd] using hfwd
        | succ G =>
          have hneg : ¬ 0 < (0 : Nat) := by omega
          simpa [reverseCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hout, ⟨wB, hw, hwN⟩, ⟨jB, hj, hjN⟩⟩

/-- Loop bridge (value level), error leg: a short record fails
    loud at the first overflowing store. -/
theorem valReverseCopyLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (la : List (BitVec 32)) (lo : List (BitVec 32))
    (w j : Nat) (wB jB : BitVec 64)
    (hwN : wB.toNat = w) (hjN : jB.toNat = j)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hwj : w + j = la.length) (hle : j ≤ la.length)
    (hwlo : w ≤ lo.length)
    (hpre : lo.take w = (la.drop j).reverse)
    (hF : j ≤ F) (hG : j ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : reverseCopyFwd la lo G w j = .error .AssertFail) :
    evalProgStmt prog F vecReverseCopyLoop ρ = .error .AssertFail := by
  induction F generalizing G ρ lo w j wB jB with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0
    cases G with
    | zero => exact absurd hfwd (by simp [reverseCopyFwd])
    | succ _ =>
      have hneg : ¬ 0 < (0 : Nat) := by omega
      have hcon := hfwd
      simp only [reverseCopyFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hj0 : 0 < j
    · have hguardT : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
          jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
        have h0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
        have htb : ((BitVec.ofNat 64 0).ult jB) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨y, hy⟩ := hread (j - 1) (by omega)
      cir_fuel_step (F, G, j - 1)
      by_cases hmiss : lo[w]? = none
      · have hshort := valReverseCopyBody_short prog F ρ lo
          w wB jB hwN hlo64 hout hw hj hmiss
        have hwhile : evalProgStmt prog (F + 1) vecReverseCopyLoop ρ =
            .error .AssertFail := by
          have hloop : vecReverseCopyLoop =
              (.while_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
                (.var "j"))
                vecReverseCopyBody) := rfl
          rw [hloop, evalProgStmt_while_true prog F _ _ _ hguardT,
            hshort]
        exact hwhile
      · have hsome : ∃ z, lo[w]? = some z := by
          match h : lo[w]? with
          | none => exact absurd h hmiss
          | some z => exact ⟨z, rfl⟩
        obtain ⟨wOld, hwget⟩ := hsome
        have hwlt : w < lo.length := transformRead_lt lo w wOld hwget
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = ((la.drop (j - 1))).reverse := by
          rw [htake_set, hpre,
            drop_reverse_succ la j y (by omega) hy]
        have hlo64' : (lo.set w y).length < 2 ^ 64 := by
          rw [List.length_set]; exact hlo64
        have hlen : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by omega
        have hwj' : (w + 1) + (j - 1) = la.length := by omega
        have hF'' : j - 1 ≤ F := by omega
        have hG'' : j - 1 ≤ G' := by omega
        have hfwd' : reverseCopyFwd la (lo.set w y) G' (w + 1)
            (j - 1) = .error .AssertFail := by
          have h := hfwd
          simp only [reverseCopyFwd, dite_eq_left hj0, hy,
            hwget] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨wB₁, hwB₁, hwN₁⟩,
            ⟨jB₁, hjB₁, hjN₁⟩⟩ :=
          valReverseCopyBody_keep prog F ρ la lo w j wB jB y wOld
            hwN hjN hla64 hlo64 ha hout hw hj (by omega) hy hwget
        have hloop : evalProgStmt prog F vecReverseCopyLoop ρ₁ =
            .error .AssertFail :=
          ih (G := G') (ρ := ρ₁) (lo := lo.set w y)
            (w := w + 1) (j := j - 1) (wB := wB₁) (jB := jB₁)
            (hwN := hwN₁) (hjN := hjN₁) (hlo64 := hlo64')
            (ha := ha₁) (hout := hout₁)
            (hw := hwB₁) (hj := hjB₁)
            (hwj := hwj') (hle := by omega) (hwlo := hwlo')
            (hpre := hpre')
            (hF := hF'') (hG := hG'')
            (hfwd := hfwd')
        have hwhile : evalProgStmt prog (F + 1) vecReverseCopyLoop ρ =
            .error .AssertFail := by
          cir_unfold_prog (vecReverseCopyLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
    · have hj0' : j = 0 := by omega
      subst hj0'
      have hguardF : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
          jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
        have hfb : ((BitVec.ofNat 64 0).ult jB) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      cases G with
      | zero => exact absurd hfwd (by simp [reverseCopyFwd])
      | succ _ =>
        have hneg : ¬ 0 < (0 : Nat) := by omega
        have hcon := hfwd
        simp only [reverseCopyFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)
