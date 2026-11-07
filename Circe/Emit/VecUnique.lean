import Circe.Emit.VecPartialSum

/-! Pillar-2 goal #13: adjacent-duplicate squeeze (`vec_unique`,
the `std::unique` idiom) — the first length-changing compaction
whose keep test reads the previous survivor (`v.at(w - 1)`, the
P2-M10 read-after-write predecessor read inside the P2-M9 scan
skeleton). The entry guards the empty vector up front and seeds
both cursors at 1 (the first element is the implicit first
survivor, so the predecessor read is always in bounds). -/

/-- Function name (Itanium mangling of a `vec_unique` free
    function taking `vector<int>&`, returning `unsigned long`). -/
def vecUniqueName : String :=
  "_Z10vec_uniqueRSt6vectorIiSaIiEE"

/-- Previous-survivor read shared by the keep test (the
    `w - 1` predecessor index). -/
def vecUniquePrev : CExpr :=
  (.stdVecAt "v" (.usub (.var "w") (.lit (.u64 (1 : BitVec 64)))))

/-- Loop body: keep `v[r]` iff it differs from the previous
    survivor `v[w - 1]` — store it at the write cursor and advance
    `w`; the read cursor always advances. -/
def vecUniqueBody : CStmt :=
  (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .skip)
    (.assign "r" (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- Loop `while (r < n) body`. -/
def vecUniqueLoop : CStmt :=
  (.while_ (.ult (.var "r") (.stdVecLen "v")) vecUniqueBody)

/-- Whole function: the empty-check early exit, then the `let_`
    prelude binding `w` and `r` at 1, the loop, and the new logical
    length returns. -/
def vecUniqueFunc : Func :=
  ⟨vecUniqueName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 }],
   .u 64,
   (.seq (.if_ (.ueq (.stdVecLen "v")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
     (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
       (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
         (.seq vecUniqueLoop
           (.return_ (.var "w"))))))⟩

/-- Loop environment (borrowed words + `u64` cursors), in prelude
    `let_` cons order (`r` over `w` over `[v]`, so the entry bridge
    is `rfl`). -/
def mkUniqueEnv (l : List (BitVec 32)) (w r : BitVec 64) : Env :=
  [("r", .u64 r), ("w", .u64 w),
   ("v", .stdVecVal l)]

theorem mkUniqueEnv_v (l : List (BitVec 32)) (w r : BitVec 64) :
    envLookup (mkUniqueEnv l w r) "v" =
      some (.stdVecVal l) := by
  simp [mkUniqueEnv, envLookup, show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "w" by decide]

theorem mkUniqueEnv_w (l : List (BitVec 32)) (w r : BitVec 64) :
    envLookup (mkUniqueEnv l w r) "w" = some (.u64 w) := by
  simp [mkUniqueEnv, envLookup, show ("w" : String) ≠ "r" by decide]

theorem mkUniqueEnv_r (l : List (BitVec 32)) (w r : BitVec 64) :
    envLookup (mkUniqueEnv l w r) "r" = some (.u64 r) := by
  simp [mkUniqueEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + current words + read cursor + write
    cursor. Fuel 0 returns the state so far; the `none` arm is
    unreachable in-invariant (every access is guard-justified:
    `r < len` from the loop guard, `w ≤ r` from the compaction,
    `1 ≤ w` from the seed — the predecessor read never wraps). -/
def uniqueFwd :
    List (BitVec 32) → Nat → Nat → Nat →
      Result (Nat × Nat × List (BitVec 32))
  | l, 0, r, w => .ok (r, w, l)
  | l, fuel + 1, r, w =>
    if _ : r < l.length then
      match l[r]?, l[w - 1]? with
      | some y, some p =>
        if (y != p) then uniqueFwd (l.set w y) fuel (r + 1) (w + 1)
        else uniqueFwd l fuel (r + 1) w
      | _, _ => .error .AssertFail
    else .ok (r, w, l)

/-- Whole-function forward: the empty vector returns 0 (the entry
    early exit), otherwise the loop at measure-exact fuel from the
    (1, 1) seed, then the new logical length. -/
def vecUniqueFwd (l : List (BitVec 32)) : Result Value :=
  match l with
  | [] => .ok (.u64 (BitVec.ofNat 64 0))
  | _ :: _ =>
    match uniqueFwd l l.length 1 1 with
    | .error e => .error e
    | .ok (_, w', _) => .ok (.u64 (BitVec.ofNat 64 w'))

/-- Program over which the entry evaluates (no callees: the body
    is straight-line `if` / `vecSet` / `assign`). -/
abbrev vecUniqueProg : Prog := [vecUniqueFunc]

/-! ## Value loop (bridges `evalProgStmt` to `uniqueFwd`) -/

/-- One body iteration (value level), keep branch: the `une`
    test against the predecessor fires, the survivor stores at
    `w`, both cursors advance. -/
theorem valUniqueBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p wOld : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length) (hw1 : 1 ≤ w)
    (hy : l[r]? = some y) (hp : l[w - 1]? = some p)
    (hwget : l[w]? = some wOld)
    (hwlt : w < l.length)
    (hkeep : (y != p) = true) :
    ∃ ρ', evalProgStmt prog F vecUniqueBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal (l.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : l[rB.toNat]? = some y := by rw [hrN]; exact hy
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
  have hgetW : l[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
  have hgetP : l[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hatR : evalExpr (.stdVecAt "v" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hrVar hgetR
  have hatP : evalExpr (.stdVecAt "v" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = .ok (.i32 p) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetP
  have hune : evalExpr
      (.une (.stdVecAt "v" (.var "r")) vecUniquePrev) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      vecUniquePrev ρ y p hatR hatP
    rwa [hkeep] at h
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "v"
    (.stdVecVal l) (.stdVecVal (l.set wB.toNat y)) hv
  have hstep_set := revVecSet prog F "v" (.var "w")
    (.stdVecAt "v" (.var "r")) ρ wB y l wOld ρ₁ hwVar hatR hv hgetW hu₁
  have hsetB : l.set wB.toNat y = l.set w y := by rw [hwN]
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "v" by decide) hu₁]
    exact hw
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "v" by decide) hu₁]
    exact hr
  have hwVar₁ : evalExpr (.var "w") ρ₁ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw₁
  have hevW : evalExpr (.uadd (.var "w")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hwVar₁ (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₁
  have hstep_w := revAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (wB + 1)) ρ₂ hevW hu₂
  have hr₂ : envLookup ρ₂ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "w" by decide) hu₂]
    exact hr₁
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
  have hout₃ : envLookup ρ₃ "v" =
      some (.stdVecVal (l.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "w" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
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
  have hthen : evalProgStmt prog F
      (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
        (.assign "w" (.uadd (.var "w")
          (.lit (.u64 (BitVec.ofNat 64 1))))))
      ρ = .ok (ρ₂, .fellThrough) := by
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
      hstep_w]
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .skip) ρ = .ok (ρ₂, .fellThrough) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hune).trans hthen
  have hbody : vecUniqueBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : evalProgStmt prog F vecUniqueBody ρ =
      .ok (ρ₃, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, heval, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩⟩

/-- One body iteration (value level), drop branch: the `une`
    test against the predecessor fails, the state threads
    untouched, only `r` advances. -/
theorem valUniqueBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length) (hw1 : 1 ≤ w)
    (hy : l[r]? = some y) (hp : l[w - 1]? = some p)
    (hdrop : (y != p) = false) :
    ∃ ρ', evalProgStmt prog F vecUniqueBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : l[rB.toNat]? = some y := by rw [hrN]; exact hy
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
  have hgetP : l[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hatR : evalExpr (.stdVecAt "v" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hrVar hgetR
  have hatP : evalExpr (.stdVecAt "v" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = .ok (.i32 p) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetP
  have hune : evalExpr
      (.une (.stdVecAt "v" (.var "r")) vecUniquePrev) ρ =
      .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      vecUniquePrev ρ y p hatR hatP
    rwa [hdrop] at h
  have hskipV : evalProgStmt prog F .skip ρ =
      .ok (ρ, .fellThrough) := by
    simpa [evalProgStmt] using
      (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
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
  have hout' : envLookup ρ' "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu]
    exact hv
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
  have hbody : vecUniqueBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : evalProgStmt prog F vecUniqueBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', heval, hout', ⟨(rB + 1), hr', hrN'⟩, ⟨wB, hw', hwN⟩⟩

/-- Value loop, ok leg: the scan runs to `l.length` and the
    words are the forward-model result (fuel induction threading
    the body hits; the forward equation unfolds one step per
    iteration; the `1 ≤ w` seed fact justifies every predecessor
    read). -/
theorem valUniqueLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64)
    (l' : List (BitVec 32)) (r' w' : Nat)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ l.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : l.length - r ≤ F) (hG : l.length - r ≤ G)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : uniqueFwd l G r w = .ok (r', w', l')) :
    ∃ ρ', evalProgStmt prog F vecUniqueLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') := by
  induction F generalizing G ρ l r w rB wB with
  | zero =>
    have him : r = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hguardF : evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "v") ρ rB
        (BitVec.ofNat 64 l.length)
        (evalExpr_var_hit _ _ _ hr)
        (evalExpr_stdVecLen_some _ _ _ hv)
      have hfb : (rB.ult (BitVec.ofNat 64 l.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt prog 0 vecUniqueLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (r, w, l) = (r', w', l') := by
      cases G with
      | zero => simpa [uniqueFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < l.length := by omega
        simpa [uniqueFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, hv, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩⟩
  | succ F ih =>
    by_cases hlt : r < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardT : evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "v") ρ rB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have htb : (rB.ult (BitVec.ofNat 64 l.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨y, hy⟩ := hread r hlt
      have hwltM : w - 1 < l.length := by omega
      obtain ⟨p, hp⟩ := hread (w - 1) hwltM
      have hwlt : w < l.length := by omega
      obtain ⟨wOld, hwget⟩ := hread w hwlt
      cir_fuel_step (F, G, l.length - (r + 1))
      by_cases hkeep : (y != p) = true
      · have hle' : r + 1 ≤ (l.set w y).length := by
          have : (l.set w y).length = l.length := by
            simp [List.length_set]
          omega
        have hwle' : w + 1 ≤ r + 1 := by omega
        have hw1' : 1 ≤ w + 1 := by omega
        have hread' : ∀ p, p < (l.set w y).length →
            ∃ z, (l.set w y)[p]? = some z := by
          intro p hp
          have hplen : p < l.length := by
            have : (l.set w y).length = l.length := by
              simp [List.length_set]
            omega
          by_cases hpw : p = w
          · rw [hpw]
            exact ⟨y, List.getElem?_set_self hwlt⟩
          · obtain ⟨z, hz⟩ := hread p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
              exact hz⟩
        obtain ⟨ρ₁, hbody, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩⟩ :=
          valUniqueBody_keep prog F ρ l r w rB wB y p wOld
            hrN hwN hl64 hv hr hw hlt hw1 hy hp hwget hwlt hkeep
        have hlen : (l.set w y).length = l.length := by
          simp [List.length_set]
        have hlo64' : (l.set w y).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hF'' : (l.set w y).length - (r + 1) ≤ F := by omega
        have hG'' : (l.set w y).length - (r + 1) ≤ G' := by omega
        have hfwd' : uniqueFwd (l.set w y) G' (r + 1) (w + 1) =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [uniqueFwd, dite_eq_left hlt, hy, hp, hkeep] at h
          exact h
        obtain ⟨ρ', hloop, hout', ⟨rB', hrB', hrN'⟩, ⟨wB', hwB', hwN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l.set w y)
            (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁) (hl64 := hlo64')
            (hv := hout₁) (hr := hrB₁) (hw := hwB₁)
            (hle := hle') (hwle := hwle') (hw1 := hw1')
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecUniqueLoop ρ =
            evalProgStmt prog F vecUniqueLoop ρ₁ := by
          cir_unfold_prog (vecUniqueLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        obtain ⟨ρ₁, hbody, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩⟩ :=
          valUniqueBody_drop prog F ρ l r w rB wB y p
            hrN hwN hl64 hv hr hw hlt hw1 hy hp hdrop
        have hwle' : w ≤ r + 1 := by omega
        have hfwd' : uniqueFwd l G' (r + 1) w =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [uniqueFwd, dite_eq_left hlt, hy, hp, hdrop] at h
          exact h
        obtain ⟨ρ', hloop, hout', ⟨rB', hrB', hrN'⟩, ⟨wB', hwB', hwN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁) (hl64 := hl64)
            (hv := hout₁) (hr := hrB₁) (hw := hwB₁)
            (hle := by omega) (hwle := hwle') (hw1 := hw1)
            (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecUniqueLoop ρ =
            evalProgStmt prog F vecUniqueLoop ρ₁ := by
          cir_unfold_prog (vecUniqueLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : r = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardF : evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "v") ρ rB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have hfb : (rB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt prog (F + 1) vecUniqueLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (l.length, w, l) = (r', w', l') := by
        cases G with
        | zero => simpa [uniqueFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [uniqueFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, hv, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩⟩
