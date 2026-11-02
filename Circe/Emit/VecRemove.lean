/-
Erase-compress (`std::remove` idiom) over `std::vector<int>` —
the first length-changing write (pillar-2 proposed goal, P2-M9).

Corpus: `tests/cpp/vec_remove.cpp` →
`tests/cir/vec_remove.cir` (entry
`_Z10vec_removeRSt6vectorIiSaIiEEi`: one `mutBorrow` vector +
one owned `i32` value, `u64` out; a single `cir.while`
two-cursor compaction scan with a conditional store).

Model: the read/write cursors `r`/`w` ride the loop; the keep
test `v.at(r) != x` is the fused `at()` read (`.une`, total on
`i32`); the survivor store is the fused non-const `at()` write
(`.vecSet`). `w ≤ r` keeps the store in bounds, so the model is
total. The endpoint is new: the function returns the new
logical length `w` (length out ≤ length in) and the caller
owes the actual `erase`/`resize` (caller-debt) — `l'.take w'`
holds the survivors in order, the tail past `w'` is
don't-care, exactly `std::remove` semantics. First
scalar-returning mutating kernel: the transfer closes on the
`u64` length while the compacted words are pinned on the
memory side.
-/
import Circe.Emit.VecPartition

/-- Function name (Itanium mangling of a `vec_remove` free
    function taking `vector<int>&` + `int`, returning
    `unsigned long`). -/
def vecRemoveName : String :=
  "_Z10vec_removeRSt6vectorIiSaIiEEi"

/-- Loop body: keep `v[r]` iff it differs from `x` — store it
    at the write cursor and advance `w`; the read cursor always
    advances. -/
def vecRemoveBody : CStmt :=
  (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .skip)
    (.assign "r" (.uadd (.var "r") (.lit (.u64 1)))))

/-- Loop `while (r < n) body`. -/
def vecRemoveLoop : CStmt :=
  (.while_ (.ult (.var "r") (.stdVecLen "v")) vecRemoveBody)

/-- Whole function: `let_`-prelude binds `w` and `r`, the loop,
    then the new logical length returns. -/
def vecRemoveFunc : Func :=
  ⟨vecRemoveName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "x", ty := .i 32, role := .owned }],
   .u 64,
   (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq vecRemoveLoop
         (.return_ (.var "w")))))⟩

/-- Loop environment (borrowed words + owned value + `u64`
    cursors), in prelude `let_` cons order (`r` over `w` over
    `[v, x]`, so the entry bridge is `rfl`). -/
def mkRemoveEnv (l : List (BitVec 32)) (x : BitVec 32)
    (w r : BitVec 64) : Env :=
  [("r", .u64 r), ("w", .u64 w), ("x", .i32 x),
   ("v", .stdVecVal l)]

theorem mkRemoveEnv_v (l : List (BitVec 32)) (x : BitVec 32)
    (w r : BitVec 64) :
    envLookup (mkRemoveEnv l x w r) "v" =
      some (.stdVecVal l) := by
  simp [mkRemoveEnv, envLookup, show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "w" by decide,
    show ("v" : String) ≠ "x" by decide]

theorem mkRemoveEnv_x (l : List (BitVec 32)) (x : BitVec 32)
    (w r : BitVec 64) :
    envLookup (mkRemoveEnv l x w r) "x" = some (.i32 x) := by
  simp [mkRemoveEnv, envLookup,
    show ("x" : String) ≠ "r" by decide,
    show ("x" : String) ≠ "w" by decide]

theorem mkRemoveEnv_w (l : List (BitVec 32)) (x : BitVec 32)
    (w r : BitVec 64) :
    envLookup (mkRemoveEnv l x w r) "w" = some (.u64 w) := by
  simp [mkRemoveEnv, envLookup, show ("w" : String) ≠ "r" by decide]

theorem mkRemoveEnv_r (l : List (BitVec 32)) (x : BitVec 32)
    (w r : BitVec 64) :
    envLookup (mkRemoveEnv l x w r) "r" = some (.u64 r) := by
  simp [mkRemoveEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + current words + read cursor + write
    cursor. Fuel 0 returns the state so far (the V1
    miss-default idiom); the `none` arm is unreachable
    in-invariant (every access is guard-justified: `r < len`
    from the loop guard, `w ≤ r` from the compaction). -/
def removeFwd (x : BitVec 32) :
    List (BitVec 32) → Nat → Nat → Nat →
      Result (Nat × Nat × List (BitVec 32))
  | l, 0, r, w => .ok (r, w, l)
  | l, fuel + 1, r, w =>
    if _ : r < l.length then
      match l[r]? with
      | none => .error .AssertFail
      | some y =>
        if (y != x) then removeFwd x (l.set w y) fuel (r + 1) (w + 1)
        else removeFwd x l fuel (r + 1) w
    else .ok (r, w, l)

/-- Whole-function forward: the loop at measure-exact fuel, then
    the new logical length. -/
def vecRemoveFwd (l : List (BitVec 32)) (x : BitVec 32) :
    Result Value :=
  match removeFwd x l l.length 0 0 with
  | .error e => .error e
  | .ok (_, w', _) => .ok (.u64 (BitVec.ofNat 64 w'))

/-- Program over which the entry evaluates (no callees: the body
    is straight-line `if` / `vecSet` / `assign`). -/
abbrev vecRemoveProg : Prog := [vecRemoveFunc]

/-! ## Value loop (bridges `evalProgStmt` to `removeFwd`) -/

/-- One body iteration (value level), keep branch: the `une`
    test fires, the survivor stores at `w`, both cursors
    advance. -/
theorem valRemoveBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y wOld : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length)
    (hy : l[r]? = some y) (hwget : l[w]? = some wOld)
    (hwlt : w < l.length)
    (hkeep : (y != x) = true) :
    ∃ ρ', evalProgStmt prog F vecRemoveBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal (l.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
      envLookup ρ' "x" = some (.i32 x) := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : l[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : l[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
  have hatR : evalExpr (.stdVecAt "v" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hrVar hgetR
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have hune : evalExpr (.une (.stdVecAt "v" (.var "r")) (.var "x")) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      (.var "x") ρ y x hatR hxV
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
  have hx₁ : envLookup ρ₁ "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "v" by decide) hu₁]
    exact hx
  have hwVar₁ : evalExpr (.var "w") ρ₁ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw₁
  have hevW : evalExpr (.uadd (.var "w") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hwVar₁ (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₁
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
  have hout₃ : envLookup ρ₃ "v" =
      some (.stdVecVal (l.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "w" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have hx' : envLookup ρ₃ "x" = some (.i32 x) := by
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
  have hthen : evalProgStmt prog F
      (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
        (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
      ρ = .ok (ρ₂, .fellThrough) := by
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
      hstep_w]
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        .skip) ρ = .ok (ρ₂, .fellThrough) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hune).trans hthen
  have hbody : vecRemoveBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecRemoveBody ρ =
      .ok (ρ₃, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, heval, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩, hx'⟩

/-- One body iteration (value level), drop branch: the `une`
    test fails, the state threads untouched, only `r` advances. -/
theorem valRemoveBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y : BitVec 32)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length)
    (hy : l[r]? = some y)
    (hdrop : (y != x) = false) :
    ∃ ρ', evalProgStmt prog F vecRemoveBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) ∧
      envLookup ρ' "x" = some (.i32 x) := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hgetR : l[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hatR : evalExpr (.stdVecAt "v" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hrVar hgetR
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have hune : evalExpr (.une (.stdVecAt "v" (.var "r")) (.var "x")) ρ =
      .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      (.var "x") ρ y x hatR hxV
    rwa [hdrop] at h
  have hskipV : evalProgStmt prog F .skip ρ =
      .ok (ρ, .fellThrough) := by
    simpa [evalProgStmt] using
      (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
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
  have hout' : envLookup ρ' "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu]
    exact hv
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
  have hbody : vecRemoveBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecRemoveBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', heval, hout', ⟨(rB + 1), hr', hrN'⟩, ⟨wB, hw', hwN⟩, hx'⟩

/-- Value loop, ok leg: the scan runs to `l.length` and the
    words are the forward-model result (fuel induction threading
    the body hits; the forward equation unfolds one step per
    iteration). -/
theorem valRemoveLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (l : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64)
    (l' : List (BitVec 32)) (r' w' : Nat)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ l.length) (hwle : w ≤ r)
    (hF : l.length - r ≤ F) (hG : l.length - r ≤ G)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : removeFwd x l G r w = .ok (r', w', l')) :
    ∃ ρ', evalProgStmt prog F vecRemoveLoop ρ =
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
    have hexit : evalProgStmt prog 0 vecRemoveLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (r, w, l) = (r', w', l') := by
      cases G with
      | zero => simpa [removeFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < l.length := by omega
        simpa [removeFwd, dite_eq_right hneg] using hfwd
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
      have hwlt : w < l.length := by omega
      obtain ⟨wOld, hwget⟩ := hread w hwlt
      cir_fuel_step (F, G, l.length - (r + 1))
      by_cases hkeep : (y != x) = true
      · have hle' : r + 1 ≤ (l.set w y).length := by
          have : (l.set w y).length = l.length := by
            simp [List.length_set]
          omega
        have hwle' : w + 1 ≤ r + 1 := by omega
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
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁⟩ :=
          valRemoveBody_keep prog F ρ l x r w rB wB y wOld
            hrN hwN hl64 hv hx hr hw hlt hy hwget hwlt hkeep
        have hlen : (l.set w y).length = l.length := by
          simp [List.length_set]
        have hlo64' : (l.set w y).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hF'' : (l.set w y).length - (r + 1) ≤ F := by omega
        have hG'' : (l.set w y).length - (r + 1) ≤ G' := by omega
        have hfwd' : removeFwd x (l.set w y) G' (r + 1) (w + 1) =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [removeFwd, dite_eq_left hlt, hy, hkeep] at h
          exact h
        obtain ⟨ρ', hloop, hout', ⟨rB', hrB', hrN'⟩, ⟨wB', hwB', hwN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l.set w y)
            (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁) (hl64 := hlo64')
            (hv := hout₁) (hx := hx₁) (hr := hrB₁) (hw := hwB₁)
            (hle := hle') (hwle := hwle')
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecRemoveLoop ρ =
            evalProgStmt prog F vecRemoveLoop ρ₁ := by
          cir_unfold_prog (vecRemoveLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        obtain ⟨ρ₁, hbody, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁⟩ :=
          valRemoveBody_drop prog F ρ l x r w rB wB y
            hrN hwN hl64 hv hx hr hw hlt hy hdrop
        have hwle' : w ≤ r + 1 := by omega
        have hfwd' : removeFwd x l G' (r + 1) w =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [removeFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        obtain ⟨ρ', hloop, hout', ⟨rB', hrB', hrN'⟩, ⟨wB', hwB', hwN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁) (hl64 := hl64)
            (hv := hout₁) (hx := hx₁) (hr := hrB₁) (hw := hwB₁)
            (hle := by omega) (hwle := hwle')
            (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecRemoveLoop ρ =
            evalProgStmt prog F vecRemoveLoop ρ₁ := by
          cir_unfold_prog (vecRemoveLoop, prog, F, hguardT, hbody)
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
      have hexit : evalProgStmt prog (F + 1) vecRemoveLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (l.length, w, l) = (r', w', l') := by
        cases G with
        | zero => simpa [removeFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [removeFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, hv, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩⟩
