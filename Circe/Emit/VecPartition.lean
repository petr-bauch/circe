/-
M3 in-place Lomuto partition over `std::vector<int>`.

Corpus: `tests/cpp/vec_partition.cpp` →
`tests/cir/vec_partition.cir` (entry
`_Z13vec_partitionRSt6vectorIiSaIiEEi`: one `mutBorrow` vector +
one owned `i32` pivot, `void` out; a single `cir.while`
forward scan with a conditional swap).

Model (the `vecAt`/`vec_at_set` fusion precedents): the const
`at()` reads fuse into the pure reads (`stdVecAt`); both swap
writes carry the loop-guard shape (`i < len`, and `s ≤ i` keeps
the `s` write in bounds — the guard justifies every access, so
the model is total). The `slt` comparison on `s32` maps to the
plain signed less-than (total); the `u64` counter bumps are the
plain `.uadd` (exact below `2 ^ 64` by the length bound, the
`bv64_succ_toNat` idiom).
-/
import Circe.Emit.VecAtSet
import Circe.Emit.VecReverse

/-- Function name (Itanium mangling of a `vec_partition` free
    function taking `vector<int>&` + `int`, returning `void`). -/
def vecPartitionName : String :=
  "_Z13vec_partitionRSt6vectorIiSaIiEEi"

/-- Loop body: conditional swap of `v[i]` below the pivot to the
    store front, both counters advance. -/
def vecPartitionBody : CStmt :=
  (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
            (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
              (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
                (.seq (.vecSet "v" (.var "s") (.var "t"))
                  (.assign "s"
                    (.uadd (.var "s") (.lit (.u64 1)))))))
            .skip)
    (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))

/-- Loop `while (i < n) body`. -/
def vecPartitionLoop : CStmt :=
  (.while_ (.ult (.var "i") (.stdVecLen "v")) vecPartitionBody)

/-- Whole function: `let_`-prelude binds `s` and `i`, the loop, then
    the updated words return (`xor_n` out-param idiom). -/
def vecPartitionFunc : Func :=
  ⟨vecPartitionName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "pivot", ty := .i 32, role := .owned }],
   stdVecObjTy,
   (.seq (.let_ "s" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq vecPartitionLoop
         (.return_ (.var "v")))))⟩

/-- Loop environment (borrowed words + owned pivot + `u64` store
    bound and index), in prelude `let_` cons order (`i` over `s`
    over `[v, pivot]`, so the entry bridge is `rfl`). -/
def mkPartitionEnv (l : List (BitVec 32)) (pivot : BitVec 32)
    (s i : BitVec 64) : Env :=
  [("i", .u64 i), ("s", .u64 s), ("pivot", .i32 pivot),
   ("v", .stdVecVal l)]

theorem mkPartitionEnv_v (l : List (BitVec 32)) (pivot : BitVec 32)
    (s i : BitVec 64) :
    envLookup (mkPartitionEnv l pivot s i) "v" =
      some (.stdVecVal l) := by
  simp [mkPartitionEnv, envLookup, show ("v" : String) ≠ "i" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "pivot" by decide]

theorem mkPartitionEnv_pivot (l : List (BitVec 32)) (pivot : BitVec 32)
    (s i : BitVec 64) :
    envLookup (mkPartitionEnv l pivot s i) "pivot" =
      some (.i32 pivot) := by
  simp [mkPartitionEnv, envLookup,
    show ("pivot" : String) ≠ "i" by decide,
    show ("pivot" : String) ≠ "s" by decide]

theorem mkPartitionEnv_s (l : List (BitVec 32)) (pivot : BitVec 32)
    (s i : BitVec 64) :
    envLookup (mkPartitionEnv l pivot s i) "s" = some (.u64 s) := by
  simp [mkPartitionEnv, envLookup, show ("s" : String) ≠ "i" by decide]

theorem mkPartitionEnv_i (l : List (BitVec 32)) (pivot : BitVec 32)
    (s i : BitVec 64) :
    envLookup (mkPartitionEnv l pivot s i) "i" = some (.u64 i) := by
  simp [mkPartitionEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + current words + scan index + store bound.
    Fuel 0 returns the state so far (no more progress — the V1
    miss-default idiom); the `none` arms are unreachable
    in-invariant (every access is guard-justified: `i < len` from
    the loop guard, `s ≤ i` from the scan). -/
def partitionFwd (pivot : BitVec 32) :
    List (BitVec 32) → Nat → Nat → Nat →
      Result (Nat × Nat × List (BitVec 32))
  | l, 0, i, s => .ok (i, s, l)
  | l, fuel + 1, i, s =>
    if _ : i < l.length then
      match l[i]? with
      | none => .error .AssertFail
      | some x =>
        if x.slt pivot then
          match l[s]? with
          | none => .error .AssertFail
          | some w =>
            partitionFwd pivot ((l.set i w).set s x) fuel (i + 1) (s + 1)
        else partitionFwd pivot l fuel (i + 1) s
    else .ok (i, s, l)

/-- Whole-function forward: the loop at measure-exact fuel, then the
    words. -/
def vecPartitionFwd (l : List (BitVec 32)) (pivot : BitVec 32) :
    Result Value :=
  match partitionFwd pivot l l.length 0 0 with
  | .error e => .error e
  | .ok (_, _, l') => .ok (.stdVecVal l')


/-- Program over which the entry evaluates (no callees: the body is
    straight-line `if` / `let_` / `vecSet` / `assign`). -/
abbrev vecPartitionProg : Prog := [vecPartitionFunc]

/-! ## M3c: value loop (bridges `evalProgStmt` to `partitionFwd`) -/

/-- One body iteration (value level), take branch: the pivot test
    fires, the temp binds, both swap stores and both bumps thread. -/
theorem valPartitionBody_take (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (pivot : BitVec 32)
    (i s : Nat) (iB sB : BitVec 64) (x w : BitVec 32)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hilt : i < l.length)
    (hx : l[i]? = some x) (hw : l[s]? = some w)
    (hslt : s < l.length)
    (htake : (x.slt pivot) = true) :
    ∃ ρ', evalProgStmt prog F vecPartitionBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i w).set s x)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s + 1) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hsVar : evalExpr (.var "s") ρ = .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs
  have hvLen : evalExpr (.stdVecLen "v") ρ =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some _ _ _ hv
  have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
  have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
      (BitVec.ofNat 64 l.length) hiVar hvLen
    have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hgetB : l[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hgetS : l[sB.toNat]? = some w := by rw [hsN]; exact hw
  have hatI : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetB
  have hpivV : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hsltV : evalExpr (.slt (.stdVecAt "v" (.var "i"))
      (.var "pivot")) ρ = .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "v" (.var "i"))
      (.var "pivot") ρ x pivot hatI hpivV
    rwa [htake] at h
  have hatS : evalExpr (.stdVecAt "v" (.var "s")) ρ = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsVar hgetS
  have hlet := revLet prog F "t" (.i 32)
    (.stdVecAt "v" (.var "i")) ρ (.i32 x) hatI
  have ht : envLookup (envExtend ρ "t" (.i32 x)) "t" =
      some (.i32 x) :=
    envExtend_hit _ _ _
  have hv₁ : envLookup (envExtend ρ "t" (.i32 x)) "v" =
      some (.stdVecVal l) :=
    envLookup_extend_miss _ _ _ _ _ hv (by decide)
  have hi₁ : envLookup (envExtend ρ "t" (.i32 x)) "i" =
      some (.u64 iB) :=
    envLookup_extend_miss _ _ _ _ _ hi (by decide)
  have hs₁ : envLookup (envExtend ρ "t" (.i32 x)) "s" =
      some (.u64 sB) :=
    envLookup_extend_miss _ _ _ _ _ hs (by decide)
  have hpiv₁ : envLookup (envExtend ρ "t" (.i32 x)) "pivot" =
      some (.i32 pivot) :=
    envLookup_extend_miss _ _ _ _ _ hpiv (by decide)
  have hiVar₁ : evalExpr (.var "i") (envExtend ρ "t" (.i32 x)) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₁
  have hsVar₁ : evalExpr (.var "s") (envExtend ρ "t" (.i32 x)) =
      .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs₁
  have hatS₁ : evalExpr (.stdVecAt "v" (.var "s"))
      (envExtend ρ "t" (.i32 x)) = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv₁ hsVar₁ hgetS
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup
    (envExtend ρ "t" (.i32 x)) "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat w)) hv₁
  have hstep_set1 := revVecSet prog F "v" (.var "i")
    (.stdVecAt "v" (.var "s")) (envExtend ρ "t" (.i32 x))
    iB w l x ρ₁ hiVar₁ hatS₁ hv₁ hgetB hu₁
  have hsetB : l.set iB.toNat w = l.set i w := by rw [hiN]
  have hs₁' : envLookup ρ₁ "s" = some (.u64 sB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "v" by decide) hu₁]
    exact hs₁
  have ht₁ : envLookup ρ₁ "t" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "v" by decide) hu₁]
    exact ht
  have hiB₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₁]
    exact hi₁
  have hpiv₂ : envLookup ρ₁ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "v" by decide) hu₁]
    exact hpiv₁
  have hsVar₂ : evalExpr (.var "s") ρ₁ = .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs₁'
  have htVar : evalExpr (.var "t") ρ₁ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ ht₁
  have hgetS₁ : (l.set iB.toNat w)[sB.toNat]? = some w := by
    rw [hiN, hsN]
    by_cases hsi : s = i
    · rw [hsi]; exact List.getElem?_set_self hilt
    · rw [List.getElem?_set_ne (show i ≠ s by omega)]
      exact hw
  have hout₁ : envLookup ρ₁ "v" =
      some (.stdVecVal (l.set iB.toNat w)) :=
    envLookup_update_hit _ _ _ _ hu₁
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "v"
    (.stdVecVal (l.set iB.toNat w))
    (.stdVecVal ((l.set iB.toNat w).set sB.toNat x)) hout₁
  have hstep_set2 := revVecSet prog F "v" (.var "s") (.var "t")
    ρ₁ sB x (l.set iB.toNat w) w ρ₂ hsVar₂ htVar hout₁ hgetS₁ hu₂
  have hs₂ : envLookup ρ₂ "s" = some (.u64 sB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "v" by decide) hu₂]
    exact hs₁'
  have hi₂ : envLookup ρ₂ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₂]
    exact hiB₁
  have hsVar₃ : evalExpr (.var "s") ρ₂ = .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs₂
  have hevS : evalExpr (.uadd (.var "s") (.lit (.u64 1))) ρ₂ =
      .ok (.u64 (sB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hsVar₃ (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "s"
    (.u64 sB) (.u64 (sB + 1)) hs₂
  have hstep_s := revAssign prog F "s"
    (.uadd (.var "s") (.lit (.u64 1))) ρ₂ (.u64 (sB + 1)) ρ₃ hevS hu₃
  have hi₃ : envLookup ρ₃ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "s" by decide) hu₃]
    exact hi₂
  have hiVar₄ : evalExpr (.var "i") ρ₃ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₃
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₃ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hiVar₄ (by simp [evalExpr, litVal])
  obtain ⟨ρ₄, hu₄⟩ := envUpdate_some_of_lookup ρ₃ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₃
  have hpiv₃ : envLookup ρ₂ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "v" by decide) hu₂]
    exact hpiv₂
  have hpiv₄ : envLookup ρ₃ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "s" by decide) hu₃]
    exact hpiv₃
  have hpiv' : envLookup ρ₄ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "i" by decide) hu₄]
    exact hpiv₄
  have hstep_i := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₃ (.u64 (iB + 1)) ρ₄ hevI hu₄
  have hset : ((l.set iB.toNat w).set sB.toNat x) =
      ((l.set i w).set s x) := by rw [hiN, hsN]
  have hout₄ : envLookup ρ₄ "v" =
      some (.stdVecVal ((l.set i w).set s x)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₄]
    have : envLookup ρ₃ "v" =
        some (.stdVecVal ((l.set iB.toNat w).set sB.toNat x)) := by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("v" : String) ≠ "s" by decide) hu₃]
      exact envLookup_update_hit _ _ _ _ hu₂
    rw [hset] at this
    exact this
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hsN' : (sB + 1).toNat = s + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hsN]
    exact Nat.mod_eq_of_lt (by omega)
  have hi' : envLookup ρ₄ "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₄
  have hs₃ : envLookup ρ₃ "s" = some (.u64 (sB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hs' : envLookup ρ₄ "s" = some (.u64 (sB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "i" by decide) hu₄]
    exact hs₃
  have hthen : evalProgStmt prog F
      (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
        (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
          (.seq (.vecSet "v" (.var "s") (.var "t"))
            (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
      ρ = .ok (ρ₃, .fellThrough) := by
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set1,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set2,
      hstep_s]
  have hif : evalProgStmt prog F
      (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip) ρ = .ok (ρ₃, .fellThrough) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hsltV).trans hthen
  have hbody : vecPartitionBody =
      (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecPartitionBody ρ =
      .ok (ρ₄, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_i]
  exact ⟨ρ₄, heval, hout₄, ⟨(iB + 1), hi', hiN'⟩,
    ⟨(sB + 1), hs', hsN'⟩, hpiv'⟩

/-- One body iteration (value level), skip branch: the pivot test
    fails, the state threads untouched, only `i` advances. -/
theorem valPartitionBody_skip (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (pivot : BitVec 32)
    (i s : Nat) (iB sB : BitVec 64) (x : BitVec 32)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hilt : i < l.length)
    (hx : l[i]? = some x)
    (hskip : (x.slt pivot) = false) :
    ∃ ρ', evalProgStmt prog F vecPartitionBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hvLen : evalExpr (.stdVecLen "v") ρ =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some _ _ _ hv
  have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
  have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
      (BitVec.ofNat 64 l.length) hiVar hvLen
    have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hgetB : l[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hatI : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetB
  have hpivV : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hsltF : evalExpr (.slt (.stdVecAt "v" (.var "i"))
      (.var "pivot")) ρ = .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "v" (.var "i"))
      (.var "pivot") ρ x pivot hatI hpivV
    rwa [hskip] at h
  have hskipV : evalProgStmt prog F .skip ρ =
      .ok (ρ, .fellThrough) := by
    simpa [evalProgStmt] using
      (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
  have hif : evalProgStmt prog F
      (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip) ρ = .ok (ρ, .fellThrough) :=
    (evalProgStmt_if_false _ _ _ _ _ _ hsltF).trans hskipV
  have hiVar' : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hiVar' (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "i"
    (.u64 iB) (.u64 (iB + 1)) hi
  have hstep_i := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ (.u64 (iB + 1)) ρ' hevI hu
  have hout' : envLookup ρ' "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu]
    exact hv
  have hs' : envLookup ρ' "s" = some (.u64 sB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "i" by decide) hu]
    exact hs
  have hpiv' : envLookup ρ' "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "i" by decide) hu]
    exact hpiv
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hi' : envLookup ρ' "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : vecPartitionBody =
      (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecPartitionBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_i]
  exact ⟨ρ', heval, hout', ⟨(iB + 1), hi', hiN'⟩, ⟨sB, hs', hsN⟩, hpiv'⟩

/-- Value loop, ok leg: the scan runs to `l.length` and the words
    are the forward-model result (fuel induction threading the body
    hits; the forward equation unfolds one step per iteration). -/
theorem valPartitionLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (l : List (BitVec 32)) (pivot : BitVec 32)
    (i s : Nat) (iB sB : BitVec 64)
    (l' : List (BitVec 32)) (i' s' : Nat)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hle : i ≤ l.length) (hsle : s ≤ i)
    (hF : l.length - i ≤ F) (hG : l.length - i ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partitionFwd pivot l G i s = .ok (i', s', l')) :
    ∃ ρ', evalProgStmt prog F vecPartitionLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s') := by
  induction F generalizing G ρ l i s iB sB with
  | zero =>
    have him : i = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
        (BitVec.ofNat 64 l.length)
        (evalExpr_var_hit _ _ _ hi)
        (evalExpr_stdVecLen_some _ _ _ hv)
      have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt prog 0 vecPartitionLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (i, s, l) = (i', s', l') := by
      cases G with
      | zero => simpa [partitionFwd] using hfwd
      | succ G =>
        have hneg : ¬ i < l.length := by omega
        simpa [partitionFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, hv, ⟨iB, hi, hiN⟩, ⟨sB, hs, hsN⟩⟩
  | succ F ih =>
    by_cases hlt : i < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨x, hx⟩ := hread i hlt
      have hslt : s < l.length := by omega
      obtain ⟨w, hw⟩ := hread s hslt
      cir_fuel_step (F, G, l.length - (i + 1))
      by_cases htake : (x.slt pivot) = true
      · have hle' : i + 1 ≤ ((l.set i w).set s x).length := by
          have : ((l.set i w).set s x).length = l.length := by
            simp [List.length_set]
          omega
        have hsle' : s + 1 ≤ i + 1 := by omega
        have hread' : ∀ p, p < ((l.set i w).set s x).length →
            ∃ y, ((l.set i w).set s x)[p]? = some y := by
          intro p hp
          have hplen : p < l.length := by
            have : ((l.set i w).set s x).length = l.length := by
              simp [List.length_set]
            omega
          by_cases hpi : p = i
          · rw [hpi]
            by_cases hsi : s = i
            · rw [hsi]
              exact ⟨x, List.getElem?_set_self (by
                rw [List.length_set]; exact hlt)⟩
            · exact ⟨w, by
                rw [List.getElem?_set_ne (show s ≠ i by omega)]
                exact List.getElem?_set_self hlt⟩
          · by_cases hps : p = s
            · rw [hps]
              exact ⟨x, List.getElem?_set_self (by
                rw [List.length_set]; exact hslt)⟩
            · obtain ⟨y, hy⟩ := hread p hplen
              exact ⟨y, by
                rw [List.getElem?_set_ne (show s ≠ p by omega),
                  List.getElem?_set_ne (show i ≠ p by omega)]
                exact hy⟩
        obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
            ⟨sB₁, hsB₁, hsN₁⟩, hpiv₁⟩ :=
          valPartitionBody_take prog F ρ l pivot i s iB sB x w
            hiN hsN hl64 hv hpiv hi hs hlt hx hw hslt htake
        have hlen : ((l.set i w).set s x).length = l.length := by
          simp [List.length_set]
        have hlo64' : ((l.set i w).set s x).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hF'' : ((l.set i w).set s x).length - (i + 1) ≤ F := by
          omega
        have hG'' : ((l.set i w).set s x).length - (i + 1) ≤ G' := by
          omega
        have hfwd' : partitionFwd pivot ((l.set i w).set s x) G'
            (i + 1) (s + 1) = .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, htake, hw] at h
          exact h
        obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩, ⟨sB', hsB', hsN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := (l.set i w).set s x)
            (i := i + 1) (s := s + 1) (iB := iB₁) (sB := sB₁)
            (hiN := hiN₁) (hsN := hsN₁) (hl64 := hlo64')
            (hv := hout₁) (hpiv := hpiv₁) (hi := hiB₁) (hs := hsB₁)
            (hle := hle') (hsle := hsle')
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', ?_, hout', ⟨iB', hiB', hiN'⟩,
          ⟨sB', hsB', hsN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecPartitionLoop ρ =
            evalProgStmt prog F vecPartitionLoop ρ₁ := by
          cir_unfold_prog (vecPartitionLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hskip : (x.slt pivot) = false := by
          cases h : x.slt pivot with
          | true => exact absurd h htake
          | false => rfl
        obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
            ⟨sB₁, hsB₁, hsN₁⟩, hpiv₁⟩ :=
          valPartitionBody_skip prog F ρ l pivot i s iB sB x
            hiN hsN hl64 hv hpiv hi hs hlt hx hskip
        have hsle' : s ≤ i + 1 := by omega
        have hfwd' : partitionFwd pivot l G' (i + 1) s =
            .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, hskip] at h
          exact h
        obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩, ⟨sB', hsB', hsN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l)
            (i := i + 1) (s := s) (iB := iB₁) (sB := sB₁)
            (hiN := hiN₁) (hsN := hsN₁) (hl64 := hl64)
            (hv := hout₁) (hpiv := hpiv₁) (hi := hiB₁) (hs := hsB₁)
            (hle := by omega) (hsle := hsle')
            (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', ?_, hout', ⟨iB', hiB', hiN'⟩,
          ⟨sB', hsB', hsN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecPartitionLoop ρ =
            evalProgStmt prog F vecPartitionLoop ρ₁ := by
          cir_unfold_prog (vecPartitionLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : i = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt prog (F + 1) vecPartitionLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (l.length, s, l) = (i', s', l') := by
        cases G with
        | zero => simpa [partitionFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [partitionFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, hv, ⟨iB, hi, hiN⟩, ⟨sB, hs, hsN⟩⟩
