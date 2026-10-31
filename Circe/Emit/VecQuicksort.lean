/-
P2-M8 recursive quicksort over `std::vector<int>`.

Corpus: `tests/cpp/vec_quicksort.cpp` →
`tests/cir/vec_quicksort.cir` (entry
`_Z13vec_quicksortRSt6vectorIiSaIiEEmm`: one `mutBorrow`
vector + two owned `u64` bounds, `void` out; two early returns,
an inline Lomuto partition loop with a conditional swap, the
pivot place, and two self-calls on the strictly smaller ranges).

Model (the `vec_partition` fusion precedent): the `at()` reads
fuse into the pure reads (`stdVecAt`); both swap writes carry
the loop-guard shape (`i < hi - 1`, and `s ≤ i` keeps the `s`
write in bounds — the guard justifies every access, so the
model is total). The `slt` comparison on `s32` maps to the
plain signed less-than (total); the `u64` counter bumps are the
plain `.uadd` (exact below `2 ^ 64` by the length bound, the
`bv64_succ_toNat` idiom). The self-calls are `callProg` (fuel
steps down at each call — the spike result — so the model
terminates by fuel with exhaustion as `AssertFail`, the Rule 7
precedent). The `void` entry returns the sorted words (the
`xor_n` out-param idiom).
-/
import Circe.Emit.VecAtSet
import Circe.Emit.VecReverse

namespace VecQuicksort

/-- Function name (Itanium mangling of a `vec_quicksort` free
    function taking `vector<int>&` + two `unsigned long`, returning
    `void`). -/
def vecQuicksortName : String :=
  "_Z13vec_quicksortRSt6vectorIiSaIiEEmm"

/-- Partition loop body: conditional swap of `v[i]` below the pivot
    to the store front, then advance `i`. -/
def qsPartBody : CStmt :=
  (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
            (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
              (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
                (.seq (.vecSet "v" (.var "s") (.var "t"))
                  (.assign "s"
                    (.uadd (.var "s") (.lit (.u64 (BitVec.ofNat 64 1))))))))
            .skip)
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- Partition loop `while (i < hi - 1) body`. -/
def qsPartLoop : CStmt :=
  (.while_ (.ult (.var "i")
    (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))) qsPartBody)

/-- Pivot place: `v[hi-1] ↔ v[s]` via the fused read/write pair. -/
def qsPlacePivot : CStmt :=
  (.seq (.vecSet "v"
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
          (.stdVecAt "v" (.var "s")))
    (.vecSet "v" (.var "s") (.var "pivot")))

/-- Left self-call on `[lo, s)` (rebinds `"v"` to the sorted words). -/
def qsCallLeft : CStmt :=
  (.callProg "v" vecQuicksortName ["v", "lo", "s"])

/-- Right self-call on `[s+1, hi)` (rebinds `"v"` again). -/
def qsCallRight : CStmt :=
  (.callProg "v" vecQuicksortName ["v", "s1", "hi"])

/-- Whole function: two early returns (empty range, singleton),
    pivot/store/index prelude, partition loop, pivot place, the two
    self-calls, and the sorted words return. -/
def vecQuicksortFunc : Func :=
  ⟨vecQuicksortName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "lo", ty := .u 64, role := .owned },
    { name := "hi", ty := .u 64, role := .owned }],
   stdVecObjTy,
   (.if_ (.ult (.var "lo") (.var "hi"))
     (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
               (.usub (.var "hi") (.var "lo")))
       (.seq (.let_ "pivot" (.i 32)
               (.stdVecAt "v"
                 (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))))
         (.seq (.let_ "s" (.u 64) (.var "lo"))
           (.seq (.let_ "i" (.u 64) (.var "lo"))
             (.seq qsPartLoop
               (.seq qsPlacePivot
                 (.seq (.let_ "s1" (.u 64)
                         (.uadd (.var "s")
                           (.lit (.u64 (BitVec.ofNat 64 1)))))
                   (.seq qsCallLeft
                     (.seq qsCallRight
                       (.return_ (.var "v"))))))))))
       (.return_ (.var "v")))
     (.return_ (.var "v")))⟩

/-- The quicksort program (single function; self-calls resolve by
    `findFunc` against this list). -/
def vecQuicksortProg : Prog := [vecQuicksortFunc]

/-! ## Forward models (fuel-threaded, mirroring evaluation) -/

/-- One Lomuto pass over `[i, hi)` with pivot `pivot`, store bound
    `s`. Each scan step costs one fuel level (mirroring the
    evaluator's `while_` unfold); the exit costs nothing. Fuel 0
    with a live guard is loud (the Rule-7 exhaustion idiom); the
    `none` arms are unreachable in-invariant (every access is
    guard-justified: `i < hi - 1` from the loop guard, `s ≤ i`
    from the scan). -/
def qsPartFwd (pivot : BitVec 32) :
    List (BitVec 32) → Nat → Nat → Nat → Nat →
      Result (Nat × List (BitVec 32))
  | l, 0, hi, i, s =>
    if i + 1 < hi then .error .AssertFail else .ok (s, l)
  | l, fuel + 1, hi, i, s =>
    if i + 1 < hi then
      match l[i]? with
      | none => .error .AssertFail
      | some x =>
        match l[s]? with
        | none => .error .AssertFail
        | some w =>
          if x.slt pivot then
            match qsPartFwd pivot ((l.set i w).set s x) fuel hi (i + 1) (s + 1) with
            | .error e => .error e
            | .ok (s', l') => .ok (s', l')
          else
            match qsPartFwd pivot l fuel hi (i + 1) s with
            | .error e => .error e
            | .ok (s', l') => .ok (s', l')
    else .ok (s, l)

/-- Whole-function forward: the length guard, the pivot read, one
    partition pass, then the two recursive sorts at one less fuel
    (mirroring the `callProg` step — `seq` restores the entry fuel
    after the scan, so the calls see the full budget minus one).
    Fuel 0 with work remaining is loud (the Rule-7 exhaustion
    idiom). -/
def vecQuicksortFwd (l : List (BitVec 32)) (F : Nat) (lo hi : Nat) :
    Result (List (BitVec 32)) :=
  match F with
  | 0 =>
    if lo < hi then
      if 1 < hi - lo then .error .AssertFail else .ok l
    else .ok l
  | F + 1 =>
    if lo < hi then
      if 1 < hi - lo then
        match l[hi - 1]? with
        | none => .error .AssertFail
        | some pivot =>
          match qsPartFwd pivot l (F + 1) hi lo lo with
          | .error e => .error e
          | .ok (s, l1) =>
            match l1[s]?, l1[hi - 1]? with
            | some w, some _ =>
              let l1' := ((l1.set (hi - 1) w).set s pivot)
              match vecQuicksortFwd l1' F lo s with
              | .error e => .error e
              | .ok l2 => vecQuicksortFwd l2 F (s + 1) hi
            | _, _ => .error .AssertFail
      else .ok l
    else .ok l

/-! ## Proof-A: value-level bridge (eval ↔ fwd) -/

/-- One body iteration (value level), take branch: the pivot test
    fires, the temp binds, both swap stores and both bumps thread. -/
theorem valQsPartBody_take (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (pivot : BitVec 32)
    (i s : Nat) (loB hiB iB sB : BitVec 64) (x w : BitVec 32)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hhi : envLookup ρ "hi" = some (.u64 hiB))
    (hlo : envLookup ρ "lo" = some (.u64 loB))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hilt : i < l.length) (hslt : s < l.length)
    (hx : l[i]? = some x) (hw : l[s]? = some w)
    (htake : (x.slt pivot) = true) :
    ∃ ρ', evalProgStmt prog F qsPartBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i w).set s x)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s + 1) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      envLookup ρ' "hi" = some (.u64 hiB) ∧
      envLookup ρ' "lo" = some (.u64 loB) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hsVar : evalExpr (.var "s") ρ = .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs
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
  have hhi₁ : envLookup (envExtend ρ "t" (.i32 x)) "hi" =
      some (.u64 hiB) :=
    envLookup_extend_miss _ _ _ _ _ hhi (by decide)
  have hlo₁ : envLookup (envExtend ρ "t" (.i32 x)) "lo" =
      some (.u64 loB) :=
    envLookup_extend_miss _ _ _ _ _ hlo (by decide)
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
  have hhi₂ : envLookup ρ₁ "hi" = some (.u64 hiB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "v" by decide) hu₁]
    exact hhi₁
  have hlo₂ : envLookup ρ₁ "lo" = some (.u64 loB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "v" by decide) hu₁]
    exact hlo₁
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
  have hhi₃ : envLookup ρ₂ "hi" = some (.u64 hiB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "v" by decide) hu₂]
    exact hhi₂
  have hlo₃ : envLookup ρ₂ "lo" = some (.u64 loB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "v" by decide) hu₂]
    exact hlo₂
  have hhi₄ : envLookup ρ₃ "hi" = some (.u64 hiB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "s" by decide) hu₃]
    exact hhi₃
  have hlo₄ : envLookup ρ₃ "lo" = some (.u64 loB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "s" by decide) hu₃]
    exact hlo₃
  have hhi' : envLookup ρ₄ "hi" = some (.u64 hiB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "i" by decide) hu₄]
    exact hhi₄
  have hlo' : envLookup ρ₄ "lo" = some (.u64 loB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "i" by decide) hu₄]
    exact hlo₄
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
  have hiltB : iB.toNat < l.length := by rw [hiN]; exact hilt
  have hsltB : sB.toNat < l.length := by rw [hsN]; exact hslt
  have hiN' : (iB + 1).toNat = i + 1 := by
    rw [revU64_succ_toNat iB l.length hiltB hl64, hiN]
  have hsN' : (sB + 1).toNat = s + 1 := by
    rw [revU64_succ_toNat sB l.length hsltB hl64, hsN]
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
  have hbody : qsPartBody =
      (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F qsPartBody ρ =
      .ok (ρ₄, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_i]
  exact ⟨ρ₄, heval, hout₄, ⟨(iB + 1), hi', hiN'⟩,
    ⟨(sB + 1), hs', hsN'⟩, hpiv', hhi', hlo'⟩

/-- One body iteration (value level), skip branch: the pivot test
    fails, only the index bump threads. -/
theorem valQsPartBody_skip (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (pivot : BitVec 32)
    (i : Nat) (loB hiB iB sB : BitVec 64) (x : BitVec 32)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hhi : envLookup ρ "hi" = some (.u64 hiB))
    (hlo : envLookup ρ "lo" = some (.u64 loB))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hilt : i < l.length)
    (hx : l[i]? = some x)
    (hskip : (x.slt pivot) = false) :
    ∃ ρ', evalProgStmt prog F qsPartBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      envLookup ρ' "s" = some (.u64 sB) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      envLookup ρ' "hi" = some (.u64 hiB) ∧
      envLookup ρ' "lo" = some (.u64 loB) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hgetB : l[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hatI : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetB
  have hpivV : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hsltV : evalExpr (.slt (.stdVecAt "v" (.var "i"))
      (.var "pivot")) ρ = .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "v" (.var "i"))
      (.var "pivot") ρ x pivot hatI hpivV
    rwa [hskip] at h
  have hif : evalProgStmt prog F
      (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip) ρ = .ok (ρ, .fellThrough) := by
    have hskipV : evalProgStmt prog F .skip ρ =
        .ok (ρ, .fellThrough) := by
      simpa [evalProgStmt] using
        (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
          cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
    exact (evalProgStmt_if_false _ _ _ _ _ _ hsltV).trans hskipV
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
  have hbody : qsPartBody =
      (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F qsPartBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif,
      hstep_i]
  have hiltB : iB.toNat < l.length := by rw [hiN]; exact hilt
  have hiN' : (iB + 1).toNat = i + 1 := by
    rw [revU64_succ_toNat iB l.length hiltB hl64, hiN]
  have hi' : envLookup ρ' "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hv' : envLookup ρ' "v" = some (.stdVecVal l) := by
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
  have hhi' : envLookup ρ' "hi" = some (.u64 hiB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "i" by decide) hu]
    exact hhi
  have hlo' : envLookup ρ' "lo" = some (.u64 loB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "i" by decide) hu]
    exact hlo
  exact ⟨ρ', heval, hv', ⟨(iB + 1), hi', hiN'⟩, hs', hpiv', hhi', hlo'⟩

/-- Scan loop bridge (value level): the evaluator loop and the
    forward pass agree step for step at the same fuel (regular
    induction — both sides peel exactly one level per iteration).
    The exit index is `hi - 1` (the guard fails first there). -/
theorem valQsPartLoop_ok (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (pivot : BitVec 32)
    (hi i s : Nat) (loB hiB iB sB : BitVec 64)
    (s' : Nat) (l' : List (BitVec 32))
    (hi64 : hiB.toNat = hi) (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hhi_le : hi ≤ l.length) (hhi1 : 1 ≤ hi)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hhi : envLookup ρ "hi" = some (.u64 hiB))
    (hlo : envLookup ρ "lo" = some (.u64 loB))
    (hii : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hsle : s ≤ i) (hle : i ≤ hi - 1)
    (hfwd : qsPartFwd pivot l F hi i s = .ok (s', l')) :
    ∃ ρ', evalProgStmt prog F qsPartLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s') ∧
      s' ≤ hi - 1 ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = hi - 1) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      envLookup ρ' "hi" = some (.u64 hiB) ∧
      envLookup ρ' "lo" = some (.u64 loB) := by
  induction F generalizing ρ l i s loB iB sB s' l' with
  | zero =>
    simp only [qsPartFwd] at hfwd
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at hfwd
      cases hfwd
    · rw [ite_eq_right hg] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hii
      have hhiVar : evalExpr (.var "hi") ρ = .ok (.u64 hiB) :=
        evalExpr_var_hit _ _ _ hhi
      have hsub : evalExpr (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
          .ok (.u64 (hiB - 1)) :=
        evalExpr_u64_usub _ _ _ _ hhiVar
      have h1B : (1 : BitVec 64).toNat = 1 := rfl
      have hsubN : (hiB - 1).toNat = hi - 1 := by
        rw [u64sub_toNat_exact _ _
          (by rw [h1B, hi64]; omega), h1B, hi64]
      have hfalse : iB.ult (hiB - 1) = false :=
        ult_ofNat_eq_false hiN hsubN (by omega)
      have hguardF : evalExpr (.ult (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ = .ok (.b false) := by
        have h := evalExpr_ult_u64 (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ iB (hiB - 1)
          hiVar hsub
        rwa [hfalse] at h
      have hexit : evalProgStmt prog 0 qsPartLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false _ _ _ _ _ hguardF
      have hi' : i = hi - 1 := by omega
      refine ⟨ρ, hexit, hv, ⟨sB, hs, hsN⟩, ?_, ⟨iB, hii, ?_⟩, hpiv, hhi, hlo⟩
      · omega
      · rw [hiN, hi']
  | succ F ih =>
    simp only [qsPartFwd] at hfwd
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at hfwd
      have hilt : i < l.length := by omega
      have hslt : s < l.length := by omega
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hii
      have hhiVar : evalExpr (.var "hi") ρ = .ok (.u64 hiB) :=
        evalExpr_var_hit _ _ _ hhi
      have hsub : evalExpr (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
          .ok (.u64 (hiB - 1)) :=
        evalExpr_u64_usub _ _ _ _ hhiVar
      have h1B : (1 : BitVec 64).toNat = 1 := rfl
      have hsubN : (hiB - 1).toNat = hi - 1 := by
        rw [u64sub_toNat_exact _ _
          (by rw [h1B, hi64]; omega), h1B, hi64]
      have htrue : iB.ult (hiB - 1) = true :=
        ult_ofNat_eq_true hiN hsubN (by omega)
      have hguardT : evalExpr (.ult (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ = .ok (.b true) := by
        have h := evalExpr_ult_u64 (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ iB (hiB - 1)
          hiVar hsub
        rwa [htrue] at h
      cases hxi : l[i]? with
      | none => simp only [hxi] at hfwd; cases hfwd
      | some x =>
        cases hsj : l[s]? with
        | none => simp only [hxi, hsj] at hfwd; cases hfwd
        | some w =>
          simp only [hxi, hsj] at hfwd
          by_cases hsltB : x.slt pivot
          · have htake : (x.slt pivot) = true := hsltB
            rw [ite_eq_left hsltB] at hfwd
            match hr : qsPartFwd pivot ((l.set i w).set s x) F hi (i + 1) (s + 1) with
            | .error e => simp only [hr] at hfwd; cases hfwd
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at hfwd
              obtain ⟨rfl, rfl⟩ := hfwd
              have hlen : ((l.set i w).set s x).length = l.length := by
                simp [List.length_set]
              have hlo64 : ((l.set i w).set s x).length < 2 ^ 64 := by
                rw [hlen]; exact hl64
              have hhi_le' : hi ≤ ((l.set i w).set s x).length := by
                rw [hlen]; exact hhi_le
              have hsle' : s + 1 ≤ i + 1 := by omega
              have hle' : i + 1 ≤ hi - 1 := by omega
              obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
                  ⟨sB₁, hsB₁, hsN₁⟩, hpiv₁, hhi₁, hlo₁⟩ :=
                valQsPartBody_take prog F ρ l pivot i s loB hiB iB sB x w
                  hiN hsN hl64 hv hpiv hhi hlo hii hs hilt hslt hxi hsj htake
              obtain ⟨ρ', hloop, hout', ⟨sB', hsB', hsN'⟩, hsle'',
                  ⟨iB', hiB', hiN'⟩, hpiv', hhi', hlo'⟩ :=
                ih (ρ := ρ₁) (l := (l.set i w).set s x)
                  (i := i + 1) (s := s + 1) (loB := loB) (iB := iB₁) (sB := sB₁)
                  (s' := s'') (l' := l'')
                  (hiN := hiN₁) (hsN := hsN₁) (hl64 := hlo64)
                  (hhi_le := hhi_le')
                  (hv := hout₁) (hpiv := hpiv₁) (hhi := hhi₁) (hlo := hlo₁)
                  (hii := hiB₁) (hs := hsB₁)
                  (hsle := hsle') (hle := hle') (hfwd := hr)
              refine ⟨ρ', ?_, hout', ⟨sB', hsB', hsN'⟩, hsle'',
                ⟨iB', hiB', hiN'⟩, hpiv', hhi', hlo'⟩
              have hwhile : evalProgStmt prog (F + 1) qsPartLoop ρ =
                  evalProgStmt prog F qsPartLoop ρ₁ := by
                simp only [qsPartLoop,
                  evalProgStmt_while_true prog F _ _ _ hguardT, hbody]
              rw [hwhile]
              exact hloop
          · have hskip : (x.slt pivot) = false := by simp [hsltB]
            rw [ite_eq_right hsltB] at hfwd
            match hr : qsPartFwd pivot l F hi (i + 1) s with
            | .error e => simp only [hr] at hfwd; cases hfwd
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at hfwd
              obtain ⟨rfl, rfl⟩ := hfwd
              have hsle' : s ≤ i + 1 := by omega
              have hle' : i + 1 ≤ hi - 1 := by omega
              obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
                  hsB₁, hpiv₁, hhi₁, hlo₁⟩ :=
                valQsPartBody_skip prog F ρ l pivot i loB hiB iB sB x
                  hiN hl64 hv hpiv hhi hlo hii hs hilt hxi hskip
              obtain ⟨ρ', hloop, hout', ⟨sB', hsB', hsN'⟩, hsle'',
                  ⟨iB', hiB', hiN'⟩, hpiv', hhi', hlo'⟩ :=
                ih (ρ := ρ₁) (l := l) (i := i + 1) (s := s)
                  (loB := loB) (iB := iB₁) (sB := sB)
                  (s' := s'') (l' := l'')
                  (hiN := hiN₁) (hsN := hsN)
                  (hl64 := hl64) (hhi_le := hhi_le)
                  (hv := hout₁) (hpiv := hpiv₁) (hhi := hhi₁) (hlo := hlo₁)
                  (hii := hiB₁) (hs := hsB₁)
                  (hsle := hsle') (hle := hle') (hfwd := hr)
              refine ⟨ρ', ?_, hout', ⟨sB', hsB', hsN'⟩, hsle'',
                ⟨iB', hiB', hiN'⟩, hpiv', hhi', hlo'⟩
              have hwhile : evalProgStmt prog (F + 1) qsPartLoop ρ =
                  evalProgStmt prog F qsPartLoop ρ₁ := by
                simp only [qsPartLoop,
                  evalProgStmt_while_true prog F _ _ _ hguardT, hbody]
              rw [hwhile]
              exact hloop
    · rw [ite_eq_right hg] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hii
      have hhiVar : evalExpr (.var "hi") ρ = .ok (.u64 hiB) :=
        evalExpr_var_hit _ _ _ hhi
      have hsub : evalExpr (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
          .ok (.u64 (hiB - 1)) :=
        evalExpr_u64_usub _ _ _ _ hhiVar
      have h1B : (1 : BitVec 64).toNat = 1 := rfl
      have hsubN : (hiB - 1).toNat = hi - 1 := by
        rw [u64sub_toNat_exact _ _
          (by rw [h1B, hi64]; omega), h1B, hi64]
      have hfalse : iB.ult (hiB - 1) = false :=
        ult_ofNat_eq_false hiN hsubN (by omega)
      have hguardF : evalExpr (.ult (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ = .ok (.b false) := by
        have h := evalExpr_ult_u64 (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ iB (hiB - 1)
          hiVar hsub
        rwa [hfalse] at h
      have hexit : evalProgStmt prog (F + 1) qsPartLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false _ _ _ _ _ hguardF
      have hi' : i = hi - 1 := by omega
      refine ⟨ρ, hexit, hv, ⟨sB, hs, hsN⟩, ?_, ⟨iB, hii, ?_⟩, hpiv, hhi, hlo⟩
      · omega
      · rw [hiN, hi']

/-! ## Proof-A (cont.): forward-model framing facts -/

/-- The partition pass only swaps, so the length never changes. -/
theorem qsPartFwd_length (pivot : BitVec 32) (l : List (BitVec 32))
    (F hi i s : Nat) (s' : Nat) (l' : List (BitVec 32))
    (h : qsPartFwd pivot l F hi i s = .ok (s', l')) :
    l'.length = l.length := by
  induction F generalizing l i s s' l' with
  | zero =>
    simp only [qsPartFwd] at h
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at h
      cases h
    · rw [ite_eq_right hg] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | succ F ih =>
    simp only [qsPartFwd] at h
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at h
      match hiM : l[i]? with
      | none => simp only [hiM] at h; cases h
      | some x =>
        simp only [hiM] at h
        match hsM : l[s]? with
        | none => simp only [hsM] at h; cases h
        | some w =>
          simp only [hsM] at h
          by_cases hsltB : x.slt pivot
          · have htake : (x.slt pivot) = true := hsltB
            rw [ite_eq_left hsltB] at h
            match hr : qsPartFwd pivot ((l.set i w).set s x) F hi (i + 1) (s + 1) with
            | .error e => simp only [hr] at h; cases h
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hlen := ih _ _ _ _ _ hr
              rwa [List.length_set, List.length_set] at hlen
          · have hskip : (x.slt pivot) = false := by simp [hsltB]
            rw [ite_eq_right hsltB] at h
            match hr : qsPartFwd pivot l F hi (i + 1) s with
            | .error e => simp only [hr] at h; cases h
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ih _ _ _ _ _ hr
    · rw [ite_eq_right hg] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- The store front only advances, so the result is no smaller. -/
theorem qsPartFwd_le (pivot : BitVec 32) (l : List (BitVec 32))
    (F hi i s : Nat) (s' : Nat) (l' : List (BitVec 32))
    (h : qsPartFwd pivot l F hi i s = .ok (s', l')) :
    s ≤ s' := by
  induction F generalizing l i s s' l' with
  | zero =>
    simp only [qsPartFwd] at h
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at h
      cases h
    · rw [ite_eq_right hg] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      omega
  | succ F ih =>
    simp only [qsPartFwd] at h
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at h
      match hiM : l[i]? with
      | none => simp only [hiM] at h; cases h
      | some x =>
        simp only [hiM] at h
        match hsM : l[s]? with
        | none => simp only [hsM] at h; cases h
        | some w =>
          simp only [hsM] at h
          by_cases hsltB : x.slt pivot
          · have htake : (x.slt pivot) = true := hsltB
            rw [ite_eq_left hsltB] at h
            match hr : qsPartFwd pivot ((l.set i w).set s x) F hi (i + 1) (s + 1) with
            | .error e => simp only [hr] at h; cases h
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hle := ih _ _ _ _ _ hr
              omega
          · have hskip : (x.slt pivot) = false := by simp [hsltB]
            rw [ite_eq_right hsltB] at h
            match hr : qsPartFwd pivot l F hi (i + 1) s with
            | .error e => simp only [hr] at h; cases h
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ih _ _ _ _ _ hr
    · rw [ite_eq_right hg] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      omega

/-- Error reflection for the scan: a failing forward pass fails loudly
    on the evaluator side with the same panic (the `_err` twin of
    `valQsPartLoop_ok`, mirroring the M7 `sortSeg_ok`/`sortSeg_err`
    split). -/
theorem valQsPartLoop_err (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (pivot : BitVec 32)
    (hi i s : Nat) (loB hiB iB sB : BitVec 64) (e : Panic)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hi64 : hiB.toNat = hi)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hhi : envLookup ρ "hi" = some (.u64 hiB))
    (hlo : envLookup ρ "lo" = some (.u64 loB))
    (hii : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hsle : s ≤ i) (hle : i ≤ hi - 1) (hhi_le : hi ≤ l.length)
    (hfwd : qsPartFwd pivot l F hi i s = .error e) :
    evalProgStmt prog F qsPartLoop ρ = .error e := by
  induction F generalizing ρ l i s iB sB e with
  | zero =>
    simp only [qsPartFwd] at hfwd
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at hfwd
      cases hfwd
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hii
      have hhiVar : evalExpr (.var "hi") ρ = .ok (.u64 hiB) :=
        evalExpr_var_hit _ _ _ hhi
      have hsub : evalExpr (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
          .ok (.u64 (hiB - 1)) :=
        evalExpr_u64_usub _ _ _ _ hhiVar
      have h1B : (1 : BitVec 64).toNat = 1 := rfl
      have hsubN : (hiB - 1).toNat = hi - 1 := by
        rw [u64sub_toNat_exact _ _
          (by rw [h1B, hi64]; omega), h1B, hi64]
      have htrue : iB.ult (hiB - 1) = true :=
        ult_ofNat_eq_true hiN hsubN (by omega)
      have hguardT : evalExpr (.ult (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ = .ok (.b true) := by
        have h := evalExpr_ult_u64 (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ iB (hiB - 1)
          hiVar hsub
        rwa [htrue] at h
      have hexit : evalProgStmt prog 0 qsPartLoop ρ = .error .AssertFail := by
        simp only [qsPartLoop]
        simp [evalProgStmt, evalStmtFuel, evalStmtZero, evalStmtWith,
          evalStmtZeroHandler, hguardT]
      exact hexit
    · rw [ite_eq_right hg] at hfwd
      cases hfwd
  | succ F ih =>
    simp only [qsPartFwd] at hfwd
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at hfwd
      have hilt : i < l.length := by omega
      have hslt : s < l.length := by omega
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hii
      have hhiVar : evalExpr (.var "hi") ρ = .ok (.u64 hiB) :=
        evalExpr_var_hit _ _ _ hhi
      have hsub : evalExpr (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
          .ok (.u64 (hiB - 1)) :=
        evalExpr_u64_usub _ _ _ _ hhiVar
      have h1B : (1 : BitVec 64).toNat = 1 := rfl
      have hsubN : (hiB - 1).toNat = hi - 1 := by
        rw [u64sub_toNat_exact _ _
          (by rw [h1B, hi64]; omega), h1B, hi64]
      have htrue : iB.ult (hiB - 1) = true :=
        ult_ofNat_eq_true hiN hsubN (by omega)
      have hguardT : evalExpr (.ult (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))) ρ = .ok (.b true) := by
        have h := evalExpr_ult_u64 (.var "i")
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ iB (hiB - 1)
          hiVar hsub
        rwa [htrue] at h
      cases hxi : l[i]? with
      | none =>
        have hsome : l[i]? = some l[i] := List.getElem?_eq_getElem hilt
        rw [hsome] at hxi
        cases hxi
      | some x =>
        cases hsj : l[s]? with
        | none =>
          have hsome : l[s]? = some l[s] := List.getElem?_eq_getElem hslt
          rw [hsome] at hsj
          cases hsj
        | some w =>
          simp only [hxi, hsj] at hfwd
          by_cases hsltB : x.slt pivot
          · have htake : (x.slt pivot) = true := hsltB
            rw [ite_eq_left hsltB] at hfwd
            match hr : qsPartFwd pivot ((l.set i w).set s x) F hi (i + 1) (s + 1) with
            | .error e₁ =>
              simp only [hr] at hfwd
              obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
                  ⟨sB₁, hsB₁, hsN₁⟩, hpiv₁, hhi₁, hlo₁⟩ :=
                valQsPartBody_take prog F ρ l pivot i s loB hiB iB sB x w
                  hiN hsN hl64 hv hpiv hhi hlo hii hs hilt hslt hxi hsj htake
              have hlen : ((l.set i w).set s x).length = l.length := by
                simp [List.length_set]
              have hlo64 : ((l.set i w).set s x).length < 2 ^ 64 := by
                rw [hlen]; exact hl64
              have hhi_le' : hi ≤ ((l.set i w).set s x).length := by
                rw [hlen]; exact hhi_le
              have hsle' : s + 1 ≤ i + 1 := by omega
              have hle' : i + 1 ≤ hi - 1 := by omega
              have hrest := ih (ρ := ρ₁) (l := (l.set i w).set s x)
                (i := i + 1) (s := s + 1) (iB := iB₁) (sB := sB₁) (e := e₁)
                (hiN := hiN₁) (hsN := hsN₁) (hl64 := hlo64)
                (hhi_le := hhi_le')
                (hv := hout₁) (hpiv := hpiv₁) (hhi := hhi₁) (hlo := hlo₁)
                (hii := hiB₁) (hs := hsB₁)
                (hsle := hsle') (hle := hle') (hfwd := hr)
              rw [Except.error.injEq] at hfwd
              have hwhile : evalProgStmt prog (F + 1) qsPartLoop ρ =
                  evalProgStmt prog F qsPartLoop ρ₁ := by
                simp only [qsPartLoop,
                  evalProgStmt_while_true prog F _ _ _ hguardT, hbody]
              rw [hwhile, hrest, hfwd]
            | .ok (s'', l'') =>
              simp only [hr] at hfwd
              cases hfwd
          · have hskip : (x.slt pivot) = false := by simp [hsltB]
            rw [ite_eq_right hsltB] at hfwd
            match hr : qsPartFwd pivot l F hi (i + 1) s with
            | .error e₁ =>
              simp only [hr] at hfwd
              obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
                  hsB₁, hpiv₁, hhi₁, hlo₁⟩ :=
                valQsPartBody_skip prog F ρ l pivot i loB hiB iB sB x
                  hiN hl64 hv hpiv hhi hlo hii hs hilt hxi hskip
              have hsle' : s ≤ i + 1 := by omega
              have hle' : i + 1 ≤ hi - 1 := by omega
              have hrest := ih (ρ := ρ₁) (l := l) (i := i + 1) (s := s)
                (iB := iB₁) (sB := sB) (e := e₁)
                (hiN := hiN₁) (hsN := hsN)
                (hl64 := hl64) (hhi_le := hhi_le)
                (hv := hout₁) (hpiv := hpiv₁) (hhi := hhi₁) (hlo := hlo₁)
                (hii := hiB₁) (hs := hsB₁)
                (hsle := hsle') (hle := hle') (hfwd := hr)
              rw [Except.error.injEq] at hfwd
              have hwhile : evalProgStmt prog (F + 1) qsPartLoop ρ =
                  evalProgStmt prog F qsPartLoop ρ₁ := by
                simp only [qsPartLoop,
                  evalProgStmt_while_true prog F _ _ _ hguardT, hbody]
              rw [hwhile, hrest, hfwd]
            | .ok (s'', l'') =>
              simp only [hr] at hfwd
              cases hfwd
    · rw [ite_eq_right hg] at hfwd
      cases hfwd

/-- The whole sort only swaps, so the length never changes (pure
    forward-model fact; feeds the recursive-call bounds). -/
theorem vecQuicksortFwd_length (l : List (BitVec 32)) (F lo hi : Nat)
    (l' : List (BitVec 32))
    (h : vecQuicksortFwd l F lo hi = .ok l') :
    l'.length = l.length := by
  induction F generalizing l lo hi l' with
  | zero =>
    simp only [vecQuicksortFwd] at h
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at h
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at h
        cases h
      · rw [ite_eq_right h2] at h
        simp only [Except.ok.injEq] at h
        obtain rfl := h
        rfl
    · rw [ite_eq_right h1] at h
      simp only [Except.ok.injEq] at h
      obtain rfl := h
      rfl
  | succ F ih =>
    simp only [vecQuicksortFwd] at h
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at h
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at h
        match hpivM : l[hi - 1]? with
        | none => simp only [hpivM] at h; cases h
        | some pivot =>
          simp only [hpivM] at h
          match hpart : qsPartFwd pivot l (F + 1) hi lo lo with
          | .error e => simp only [hpart] at h; cases h
          | .ok (s, l1) =>
            simp only [hpart] at h
            match hwM : l1[s]? with
            | none => simp only [hwM] at h; cases h
            | some w =>
              simp only [hwM] at h
              match hpM : l1[hi - 1]? with
              | none => simp only [hpM] at h; cases h
              | some _ =>
                simp only [hpM] at h
                match hleft : vecQuicksortFwd
                    ((l1.set (hi - 1) w).set s pivot) F lo s with
                | .error e => simp only [hleft] at h; cases h
                | .ok l2 =>
                  simp only [hleft] at h
                  match hright : vecQuicksortFwd l2 F (s + 1) hi with
                  | .error e => simp only [hright] at h; cases h
                  | .ok l3 =>
                    simp only [hright, Except.ok.injEq] at h
                    obtain rfl := h
                    have e1 := ih _ _ _ _ hleft
                    have e2 := ih _ _ _ _ hright
                    have e3 := qsPartFwd_length _ _ _ _ _ _ _ _ hpart
                    simp only [List.length_set] at e1
                    omega
      · rw [ite_eq_right h2] at h
        simp only [Except.ok.injEq] at h
        obtain rfl := h
        rfl
    · rw [ite_eq_right h1] at h
      simp only [Except.ok.injEq] at h
      obtain rfl := h
      rfl

/-- Whole-function value-level bridge, ok direction: a successful
    forward run evaluates to the same words (the `_ok` twin; `_err`
    below reflects failures). By fuel induction: the scan reuses
    `valQsPartLoop_ok`, the place is two `revVecSet` steps, and the
    two self-calls close by the induction hypothesis at predecessor
    fuel (the `callProg` step), exactly matching the forward-model
    recursion. -/
theorem evalProgFunc_vecQuicksort_ok (F : Nat)
    (l : List (BitVec 32)) (lo hi : Nat) (loB hiB : BitVec 64)
    (hloN : loB.toNat = lo) (hhiN : hiB.toNat = hi)
    (hl64 : l.length < 2 ^ 64)
    (hlo_le : lo ≤ hi) (hhi_le : hi ≤ l.length)
    (l' : List (BitVec 32))
    (hfwd : vecQuicksortFwd l F lo hi = .ok l') :
    ∃ ret, evalProgFunc vecQuicksortProg F vecQuicksortFunc
      [.stdVecVal l, .u64 loB, .u64 hiB] = .ok ret ∧
      ret = .stdVecVal l' := by
  induction F generalizing l lo hi loB hiB l' with
  | zero =>
    have hbind : bindArgs vecQuicksortFunc.args
        [.stdVecVal l, .u64 loB, .u64 hiB] =
        some [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] := rfl
    have hbody : vecQuicksortFunc.body =
        (.if_ (.ult (.var "lo") (.var "hi"))
          (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
                    (.usub (.var "hi") (.var "lo")))
            (.seq (.let_ "pivot" (.i 32)
                    (.stdVecAt "v"
                      (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))))
              (.seq (.let_ "s" (.u 64) (.var "lo"))
                (.seq (.let_ "i" (.u 64) (.var "lo"))
                  (.seq qsPartLoop
                    (.seq qsPlacePivot
                      (.seq (.let_ "s1" (.u 64)
                              (.uadd (.var "s")
                                (.lit (.u64 (BitVec.ofNat 64 1)))))
                        (.seq qsCallLeft
                          (.seq qsCallRight
                            (.return_ (.var "v"))))))))))
            (.return_ (.var "v")))
          (.return_ (.var "v"))) := rfl
    simp only [vecQuicksortFwd] at hfwd
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at hfwd
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at hfwd
        cases hfwd
      · rw [ite_eq_right h2] at hfwd
        simp only [Except.ok.injEq] at hfwd
        obtain rfl := hfwd
        have hloVar : evalExpr (.var "lo")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hhiVar : evalExpr (.var "hi")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
        have hltB : loB.ult hiB = true :=
          ult_ofNat_eq_true hloN hhiN h1
        have gloT : evalExpr (.ult (.var "lo") (.var "hi"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _ hloVar hhiVar
          rwa [hltB] at h
        have hsub : evalExpr (.usub (.var "hi") (.var "lo"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 (hiB - loB)) :=
          evalExpr_usub_u64u64 _ _ _ _ _ hhiVar hloVar
        have hle64 : loB.toNat ≤ hiB.toNat := by
          rw [hloN, hhiN]; exact hlo_le
        have hsubN : (hiB - loB).toNat = hi - lo := by
          rw [u64sub_toNat_exact hiB loB hle64, hloN, hhiN]
        have h1B : (1 : BitVec 64).toNat = 1 := rfl
        have h1of : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
        have h2lt : (BitVec.ofNat 64 1).ult (hiB - loB) = false := by
          rw [← h1of, BitVec.ult_eq_decide, h1B, hsubN]
          exact decide_eq_false h2
        have g2F : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
            (.usub (.var "hi") (.var "lo")))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b false) := by
          have h : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
              (.usub (.var "hi") (.var "lo")))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.b ((BitVec.ofNat 64 1).ult (hiB - loB))) :=
            evalExpr_ult_u64lit _ _ _ _ hsub
          rwa [h2lt] at h
        have hv₀ : envLookup [("v", .stdVecVal l),
            ("lo", .u64 loB), ("hi", .u64 hiB)] "v" =
            some (.stdVecVal l) := by rfl
        have hret : evalProgStmt vecQuicksortProg 0
            (.return_ (.var "v"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
              .returned (.stdVecVal l)) :=
          evalProgStmt_return _ _ _ _ _
            (evalExpr_var_hit _ _ _ hv₀)
        have hstmt : evalProgStmt vecQuicksortProg 0
            vecQuicksortFunc.body
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
              .returned (.stdVecVal l)) := by
          rw [hbody,
            evalProgStmt_if_true vecQuicksortProg 0 _ _ _ _ gloT,
            evalProgStmt_if_false vecQuicksortProg 0 _ _ _ _ g2F]
          exact hret
        exact ⟨.stdVecVal l,
          by simp [evalProgFunc, hbind, hstmt], rfl⟩
    · rw [ite_eq_right h1] at hfwd
      simp only [Except.ok.injEq] at hfwd
      obtain rfl := hfwd
      have hloVar : evalExpr (.var "lo")
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
      have hhiVar : evalExpr (.var "hi")
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
      have hltB : loB.ult hiB = false :=
        ult_ofNat_eq_false hloN hhiN h1
      have gloF : evalExpr (.ult (.var "lo") (.var "hi"))
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ hloVar hhiVar
        rwa [hltB] at h
      have hv₀ : envLookup [("v", .stdVecVal l),
          ("lo", .u64 loB), ("hi", .u64 hiB)] "v" =
          some (.stdVecVal l) := by rfl
      have hret : evalProgStmt vecQuicksortProg 0
          (.return_ (.var "v"))
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
            .returned (.stdVecVal l)) :=
        evalProgStmt_return _ _ _ _ _
          (evalExpr_var_hit _ _ _ hv₀)
      have hstmt : evalProgStmt vecQuicksortProg 0
          vecQuicksortFunc.body
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
            .returned (.stdVecVal l)) := by
        rw [hbody,
          evalProgStmt_if_false vecQuicksortProg 0 _ _ _ _ gloF]
        exact hret
      exact ⟨.stdVecVal l,
        by simp [evalProgFunc, hbind, hstmt], rfl⟩
  | succ F ih =>
    have hbind : bindArgs vecQuicksortFunc.args
        [.stdVecVal l, .u64 loB, .u64 hiB] =
        some [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] := rfl
    have hbody : vecQuicksortFunc.body =
        (.if_ (.ult (.var "lo") (.var "hi"))
          (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
                    (.usub (.var "hi") (.var "lo")))
            (.seq (.let_ "pivot" (.i 32)
                    (.stdVecAt "v"
                      (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))))
              (.seq (.let_ "s" (.u 64) (.var "lo"))
                (.seq (.let_ "i" (.u 64) (.var "lo"))
                  (.seq qsPartLoop
                    (.seq qsPlacePivot
                      (.seq (.let_ "s1" (.u 64)
                              (.uadd (.var "s")
                                (.lit (.u64 (BitVec.ofNat 64 1)))))
                        (.seq qsCallLeft
                          (.seq qsCallRight
                            (.return_ (.var "v"))))))))))
            (.return_ (.var "v")))
          (.return_ (.var "v"))) := rfl
    simp only [vecQuicksortFwd] at hfwd
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at hfwd
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at hfwd
        have hhi1 : 1 ≤ hi := by omega
        have hhi1len : hi - 1 < l.length := by omega
        have hpivM : l[hi - 1]? = some l[hi - 1] :=
          List.getElem?_eq_getElem hhi1len
        simp only [hpivM] at hfwd
        match hpart : qsPartFwd l[hi - 1] l (F + 1) hi lo lo with
        | .error e => simp only [hpart] at hfwd; cases hfwd
        | .ok (s₁, l₁) =>
          simp only [hpart] at hfwd
          have hv₀ : envLookup [("v", .stdVecVal l),
              ("lo", .u64 loB), ("hi", .u64 hiB)] "v" =
              some (.stdVecVal l) := by rfl
          have hloVar₀ : evalExpr (.var "lo")
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
          have hhiVar₀ : evalExpr (.var "hi")
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
          have hltB : loB.ult hiB = true :=
            ult_ofNat_eq_true hloN hhiN h1
          have gloT : evalExpr (.ult (.var "lo") (.var "hi"))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.b true) := by
            have h := evalExpr_ult_u64 _ _ _ _ _ hloVar₀ hhiVar₀
            rwa [hltB] at h
          have hle64 : loB.toNat ≤ hiB.toNat := by
            rw [hloN, hhiN]; exact hlo_le
          have hsubOl : evalExpr (.usub (.var "hi") (.var "lo"))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.u64 (hiB - loB)) :=
            evalExpr_usub_u64u64 _ _ _ _ _ hhiVar₀ hloVar₀
          have hsubNOl : (hiB - loB).toNat = hi - lo := by
            rw [u64sub_toNat_exact hiB loB hle64, hloN, hhiN]
          have h1of : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
          have h2ltT : (BitVec.ofNat 64 1).ult (hiB - loB) = true := by
            have h1B : (1 : BitVec 64).toNat = 1 := rfl
            rw [← h1of, BitVec.ult_eq_decide, h1B, hsubNOl]
            exact decide_eq_true h2
          have g2T : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
              (.usub (.var "hi") (.var "lo")))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.b true) := by
            have h : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
                (.usub (.var "hi") (.var "lo")))
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
                .ok (.b ((BitVec.ofNat 64 1).ult (hiB - loB))) :=
              evalExpr_ult_u64lit _ _ _ _ hsubOl
            rwa [h2ltT] at h
          have h1B' : (1 : BitVec 64).toNat = 1 := rfl
          have h1hle : (1 : BitVec 64).toNat ≤ hiB.toNat := by
            rw [h1B', hhiN]; omega
          have hsubN : (hiB - 1).toNat = hi - 1 := by
            rw [u64sub_toNat_exact _ _ h1hle, h1B', hhiN]
          have hsubHi : evalExpr
              (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.u64 (hiB - 1)) :=
            evalExpr_u64_usub _ _ _ _ hhiVar₀
          have hpivB : evalExpr
              (.stdVecAt "v"
                (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.i32 l[hi - 1]) := by
            have hget : l[(hiB - 1).toNat]? = some l[hi - 1] := by
              rw [hsubN]; exact hpivM
            exact evalExpr_stdVecAt_some _ _ _ _ _ _ hv₀ hsubHi hget
          have hletPiv := revLet vecQuicksortProg (F + 1) "pivot" (.i 32)
            _ _ _ hpivB
          have hsVarP : evalExpr (.var "lo")
              (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
                ("hi", .u64 hiB)] "pivot" (.i32 l[hi - 1])) =
              .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
          have hletS := revLet vecQuicksortProg (F + 1) "s" (.u 64)
            _ _ _ hsVarP
          have hiVarS : evalExpr (.var "lo")
              (envExtend (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
                ("hi", .u64 hiB)] "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) =
              .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
          have hletI := revLet vecQuicksortProg (F + 1) "i" (.u 64)
            _ _ _ hiVarS
          have hvL : envLookup
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              "v" = some (.stdVecVal l) := by rfl
          have hpivL : envLookup
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              "pivot" = some (.i32 l[hi - 1]) := by rfl
          have hhiL : envLookup
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              "hi" = some (.u64 hiB) := by rfl
          have hloL : envLookup
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              "lo" = some (.u64 loB) := by rfl
          have hiiL : envLookup
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              "i" = some (.u64 loB) := by rfl
          have hsL : envLookup
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              "s" = some (.u64 loB) := by rfl
          obtain ⟨ρ₁, hloop, hout₁, ⟨sB₁, hsB₁, hsN₁⟩, hs'le,
              ⟨iB₁, hiB₁, hiN₁⟩, hpiv₁, hhi₁, hlo₁⟩ :=
            valQsPartLoop_ok vecQuicksortProg (F + 1)
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              l l[hi - 1] hi lo lo loB hiB loB loB s₁ l₁
              hhiN hloN hloN hl64 hhi_le hhi1
              hvL hpivL hhiL hloL hiiL hsL (by omega) (by omega) hpart
          simp only [qsPartLoop] at hloop
          have hlen₁ : l₁.length = l.length :=
            qsPartFwd_length _ _ _ _ _ _ _ _ hpart
          have hl64₁ : l₁.length < 2 ^ 64 := by
            rw [hlen₁]; exact hl64
          have hs₁lt : s₁ < l₁.length := by omega
          have hhi1' : hi - 1 < l₁.length := by omega
          have hwM : l₁[s₁]? = some l₁[s₁] :=
            List.getElem?_eq_getElem hs₁lt
          have hpM : l₁[hi - 1]? = some l₁[hi - 1] :=
            List.getElem?_eq_getElem hhi1'
          simp only [hwM, hpM] at hfwd
          match hleft : vecQuicksortFwd
              ((l₁.set (hi - 1) l₁[s₁]).set s₁ l[hi - 1]) F lo s₁ with
          | .error e => simp only [hleft] at hfwd; cases hfwd
          | .ok l2 =>
            simp only [hleft] at hfwd
            match hright : vecQuicksortFwd l2 F (s₁ + 1) hi with
            | .error e => simp only [hright] at hfwd; cases hfwd
            | .ok l3 =>
              simp only [hright, Except.ok.injEq] at hfwd
              obtain rfl := hfwd
              have hhiVar₁ : evalExpr (.var "hi") ρ₁ =
                  .ok (.u64 hiB) := evalExpr_var_hit _ _ _ hhi₁
              have hsVar₁ : evalExpr (.var "s") ρ₁ =
                  .ok (.u64 sB₁) := evalExpr_var_hit _ _ _ hsB₁
              have hsubHi₁ : evalExpr
                  (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
                  .ok (.u64 (hiB - 1)) :=
                evalExpr_u64_usub _ _ _ _ hhiVar₁
              have hgetS₁ : l₁[sB₁.toNat]? = some l₁[s₁] := by
                rw [hsN₁]; exact hwM
              have hgetOld : l₁[(hiB - 1).toNat]? = some l₁[hi - 1] := by
                rw [hsubN]; exact hpM
              have hatS₁ : evalExpr (.stdVecAt "v" (.var "s")) ρ₁ =
                  .ok (.i32 l₁[s₁]) :=
                evalExpr_stdVecAt_some _ _ _ _ _ _ hout₁ hsVar₁ hgetS₁
              obtain ⟨ρ₂, hu₁⟩ := envUpdate_some_of_lookup ρ₁ "v"
                (.stdVecVal l₁)
                (.stdVecVal (l₁.set (hiB - 1).toNat l₁[s₁])) hout₁
              have hstep1 := revVecSet vecQuicksortProg (F + 1) "v"
                (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
                (.stdVecAt "v" (.var "s")) ρ₁ (hiB - 1) l₁[s₁] l₁
                l₁[hi - 1] ρ₂ hsubHi₁ hatS₁ hout₁ hgetOld hu₁
              have hout₂ : envLookup ρ₂ "v" =
                  some (.stdVecVal (l₁.set (hiB - 1).toNat l₁[s₁])) :=
                envLookup_update_hit _ _ _ _ hu₁
              rw [hsubN] at hu₁
              have hout₂' : envLookup ρ₂ "v" =
                  some (.stdVecVal (l₁.set (hi - 1) l₁[s₁])) :=
                envLookup_update_hit _ _ _ _ hu₁
              have hs₂ : envLookup ρ₂ "s" = some (.u64 sB₁) := by
                rw [envLookup_update_miss _ _ _ _ _
                  (show ("s" : String) ≠ "v" by decide) hu₁]
                exact hsB₁
              have hpiv₂ : envLookup ρ₂ "pivot" =
                  some (.i32 l[hi - 1]) := by
                rw [envLookup_update_miss _ _ _ _ _
                  (show ("pivot" : String) ≠ "v" by decide) hu₁]
                exact hpiv₁
              have hhi₂ : envLookup ρ₂ "hi" = some (.u64 hiB) := by
                rw [envLookup_update_miss _ _ _ _ _
                  (show ("hi" : String) ≠ "v" by decide) hu₁]
                exact hhi₁
              have hlo₂ : envLookup ρ₂ "lo" = some (.u64 loB) := by
                rw [envLookup_update_miss _ _ _ _ _
                  (show ("lo" : String) ≠ "v" by decide) hu₁]
                exact hlo₁
              have hsVar₂ : evalExpr (.var "s") ρ₂ =
                  .ok (.u64 sB₁) := evalExpr_var_hit _ _ _ hs₂
              have hpivVar₂ : evalExpr (.var "pivot") ρ₂ =
                  .ok (.i32 l[hi - 1]) := evalExpr_var_hit _ _ _ hpiv₂
              have hlenSet1 : (l₁.set (hi - 1) l₁[s₁]).length =
                  l₁.length := List.length_set
              have hs₁lt1 : s₁ < (l₁.set (hi - 1) l₁[s₁]).length := by
                rw [hlenSet1]; exact hs₁lt
              have hget₂ : ((l₁.set (hi - 1) l₁[s₁]))[sB₁.toNat]? =
                  some (((l₁.set (hi - 1) l₁[s₁]))[s₁]) := by
                rw [hsN₁]
                exact List.getElem?_eq_getElem hs₁lt1
              obtain ⟨ρ₃, hu₂⟩ := envUpdate_some_of_lookup ρ₂ "v"
                (.stdVecVal (l₁.set (hi - 1) l₁[s₁]))
                (.stdVecVal (((l₁.set (hi - 1) l₁[s₁])).set sB₁.toNat
                  l[hi - 1])) hout₂'
              have hstep2 := revVecSet vecQuicksortProg (F + 1) "v"
                (.var "s") (.var "pivot") ρ₂ sB₁ l[hi - 1]
                (l₁.set (hi - 1) l₁[s₁])
                (((l₁.set (hi - 1) l₁[s₁]))[s₁]) ρ₃
                hsVar₂ hpivVar₂ hout₂' hget₂ hu₂
              rw [hsN₁] at hu₂
              have hout₃ : envLookup ρ₃ "v" = some (.stdVecVal
                  (((l₁.set (hi - 1) l₁[s₁])).set s₁ l[hi - 1])) :=
                envLookup_update_hit _ _ _ _ hu₂
              have hs₃ : envLookup ρ₃ "s" = some (.u64 sB₁) := by
                rw [envLookup_update_miss _ _ _ _ _
                  (show ("s" : String) ≠ "v" by decide) hu₂]
                exact hs₂
              have hhi₃ : envLookup ρ₃ "hi" = some (.u64 hiB) := by
                rw [envLookup_update_miss _ _ _ _ _
                  (show ("hi" : String) ≠ "v" by decide) hu₂]
                exact hhi₂
              have hlo₃ : envLookup ρ₃ "lo" = some (.u64 loB) := by
                rw [envLookup_update_miss _ _ _ _ _
                  (show ("lo" : String) ≠ "v" by decide) hu₂]
                exact hlo₂
              have hsVar₃ : evalExpr (.var "s") ρ₃ =
                  .ok (.u64 sB₁) := evalExpr_var_hit _ _ _ hs₃
              have hevS1 : evalExpr
                  (.uadd (.var "s")
                    (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ =
                  .ok (.u64 (sB₁ + 1)) :=
                evalExpr_uadd_u64 _ _ _ _ _ hsVar₃
                  (by simp [evalExpr, litVal])
              have htoNat : (sB₁ + 1).toNat = s₁ + 1 := by
                rw [revU64_succ_toNat sB₁ l₁.length
                  (by rw [hsN₁]; exact hs₁lt) hl64₁, hsN₁]
              have hletS1 := revLet vecQuicksortProg (F + 1) "s1"
                (.u 64) _ _ _ hevS1
              have hs1₄ : envLookup
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "s1" =
                  some (.u64 (sB₁ + 1)) := envExtend_hit _ _ _
              have hv₄ : envLookup
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v" =
                  some (.stdVecVal
                    (((l₁.set (hi - 1) l₁[s₁])).set s₁ l[hi - 1])) :=
                envLookup_extend_miss _ _ _ _ _ hout₃ (by decide)
              have hlo₄ : envLookup
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "lo" =
                  some (.u64 loB) :=
                envLookup_extend_miss _ _ _ _ _ hlo₃ (by decide)
              have hs₄ : envLookup
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "s" =
                  some (.u64 sB₁) :=
                envLookup_extend_miss _ _ _ _ _ hs₃ (by decide)
              have hargsL : lookupArgs
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) ["v", "lo", "s"] =
                  some [.stdVecVal
                    (((l₁.set (hi - 1) l₁[s₁])).set s₁ l[hi - 1]),
                    .u64 loB, .u64 sB₁] :=
                lookupArgs_cons_hit _ _ _ _ _ hv₄
                  (lookupArgs_cons_hit _ _ _ _ _ hlo₄
                    (lookupArgs_cons_hit _ _ _ _ _ hs₄
                      (lookupArgs_nil _)))
              have hfind : findFunc vecQuicksortProg
                  vecQuicksortName = some vecQuicksortFunc :=
                findFunc_hit vecQuicksortFunc []
              have hlenL1' : ((((l₁.set (hi - 1) l₁[s₁])).set s₁
                  l[hi - 1]).length) = l₁.length := by
                simp [List.length_set]
              have hL64 : ((((l₁.set (hi - 1) l₁[s₁])).set s₁
                  l[hi - 1]).length) < 2 ^ 64 := by
                rw [hlenL1']; exact hl64₁
              have hLlo : lo ≤ s₁ :=
                qsPartFwd_le _ _ _ _ _ _ _ _ hpart
              have hLhi : s₁ ≤ ((((l₁.set (hi - 1) l₁[s₁])).set s₁
                  l[hi - 1]).length) := by omega
              have hL := ih (((l₁.set (hi - 1) l₁[s₁])).set s₁
                  l[hi - 1]) lo s₁ loB sB₁ hloN hsN₁ hL64 hLlo hLhi
                l2 hleft
              obtain ⟨_, hLeval, rfl⟩ := hL
              have hcallL := evalProgStmt_callProg_ok vecQuicksortProg
                F "v" vecQuicksortName ["v", "lo", "s"]
                (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) _ _ _
                hargsL hfind hLeval
              have hhi₄ : envLookup
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "hi" =
                  some (.u64 hiB) :=
                envLookup_extend_miss _ _ _ _ _ hhi₃ (by decide)
              have hv₅ : envLookup (envExtend
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                  (.stdVecVal l2)) "v" = some (.stdVecVal l2) :=
                envExtend_hit _ _ _
              have hs1₅ : envLookup (envExtend
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                  (.stdVecVal l2)) "s1" = some (.u64 (sB₁ + 1)) :=
                envLookup_extend_miss _ _ _ _ _ hs1₄ (by decide)
              have hhi₅ : envLookup (envExtend
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                  (.stdVecVal l2)) "hi" = some (.u64 hiB) :=
                envLookup_extend_miss _ _ _ _ _ hhi₄ (by decide)
              have hargsR : lookupArgs (envExtend
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                  (.stdVecVal l2)) ["v", "s1", "hi"] =
                  some [.stdVecVal l2, .u64 (sB₁ + 1), .u64 hiB] :=
                lookupArgs_cons_hit _ _ _ _ _ hv₅
                  (lookupArgs_cons_hit _ _ _ _ _ hs1₅
                    (lookupArgs_cons_hit _ _ _ _ _ hhi₅
                      (lookupArgs_nil _)))
              have hlenL2 : l2.length =
                  ((((l₁.set (hi - 1) l₁[s₁])).set s₁
                    l[hi - 1]).length) :=
                vecQuicksortFwd_length _ _ _ _ _ hleft
              have hR := ih l2 (s₁ + 1) hi (sB₁ + 1) hiB htoNat hhiN
                (by rw [hlenL2]; exact hL64) (by omega) (by omega)
                l3 hright
              obtain ⟨_, hReval, rfl⟩ := hR
              have hcallR := evalProgStmt_callProg_ok vecQuicksortProg
                F "v" vecQuicksortName ["v", "s1", "hi"]
                (envExtend (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                  (.stdVecVal l2)) _ _ _
                hargsR hfind hReval
              have hv₆ : envLookup (envExtend (envExtend
                  (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                  (.stdVecVal l2)) "v" (.stdVecVal l3)) "v" =
                  some (.stdVecVal l3) := envExtend_hit _ _ _
              have hret6 := evalProgStmt_return vecQuicksortProg
                (F + 1) (.var "v") _ _ (evalExpr_var_hit _ _ _ hv₆)
              have hplace : evalProgStmt vecQuicksortProg (F + 1)
                  (.seq (.vecSet "v"
                    (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
                    (.stdVecAt "v" (.var "s")))
                    (.vecSet "v" (.var "s") (.var "pivot"))) ρ₁ =
                  .ok (ρ₃, .fellThrough) := by
                rw [evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hstep1]
                exact hstep2
              have hstmt : evalProgStmt vecQuicksortProg (F + 1)
                  vecQuicksortFunc.body
                  [("v", .stdVecVal l), ("lo", .u64 loB),
                    ("hi", .u64 hiB)] =
                  .ok (envExtend (envExtend
                    (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                    (.stdVecVal l2)) "v" (.stdVecVal l3),
                    .returned (.stdVecVal l3)) := by
                rw [hbody]
                simp only [qsPartLoop, qsPlacePivot, qsCallLeft,
                  qsCallRight]
                rw [evalProgStmt_if_true vecQuicksortProg (F + 1)
                    _ _ _ _ gloT,
                  evalProgStmt_if_true vecQuicksortProg (F + 1)
                    _ _ _ _ g2T,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletPiv,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletS,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletI,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hloop,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hplace,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletS1,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hcallL,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hcallR]
                exact hret6
              have hfin : evalProgFunc vecQuicksortProg (F + 1)
                  vecQuicksortFunc
                  [.stdVecVal l, .u64 loB, .u64 hiB] =
                  .ok (.stdVecVal l3) := by
                simp [evalProgFunc, hbind, hstmt]
              exact ⟨.stdVecVal l3, hfin, rfl⟩

      · rw [ite_eq_right h2] at hfwd
        simp only [Except.ok.injEq] at hfwd
        obtain rfl := hfwd
        have hloVar : evalExpr (.var "lo")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hhiVar : evalExpr (.var "hi")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
        have hltB : loB.ult hiB = true :=
          ult_ofNat_eq_true hloN hhiN h1
        have gloT : evalExpr (.ult (.var "lo") (.var "hi"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _ hloVar hhiVar
          rwa [hltB] at h
        have hsub : evalExpr (.usub (.var "hi") (.var "lo"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 (hiB - loB)) :=
          evalExpr_usub_u64u64 _ _ _ _ _ hhiVar hloVar
        have hle64 : loB.toNat ≤ hiB.toNat := by
          rw [hloN, hhiN]; exact hlo_le
        have hsubN : (hiB - loB).toNat = hi - lo := by
          rw [u64sub_toNat_exact hiB loB hle64, hloN, hhiN]
        have h1B : (1 : BitVec 64).toNat = 1 := rfl
        have h1of : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
        have h2lt : (BitVec.ofNat 64 1).ult (hiB - loB) = false := by
          rw [← h1of, BitVec.ult_eq_decide, h1B, hsubN]
          exact decide_eq_false h2
        have g2F : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
            (.usub (.var "hi") (.var "lo")))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b false) := by
          have h : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
              (.usub (.var "hi") (.var "lo")))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.b ((BitVec.ofNat 64 1).ult (hiB - loB))) :=
            evalExpr_ult_u64lit _ _ _ _ hsub
          rwa [h2lt] at h
        have hv₀ : envLookup [("v", .stdVecVal l),
            ("lo", .u64 loB), ("hi", .u64 hiB)] "v" =
            some (.stdVecVal l) := by rfl
        have hret : evalProgStmt vecQuicksortProg (F + 1)
            (.return_ (.var "v"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
              .returned (.stdVecVal l)) :=
          evalProgStmt_return _ _ _ _ _
            (evalExpr_var_hit _ _ _ hv₀)
        have hstmt : evalProgStmt vecQuicksortProg (F + 1)
            vecQuicksortFunc.body
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
              .returned (.stdVecVal l)) := by
          rw [hbody,
            evalProgStmt_if_true vecQuicksortProg (F + 1) _ _ _ _ gloT,
            evalProgStmt_if_false vecQuicksortProg (F + 1) _ _ _ _ g2F]
          exact hret
        exact ⟨.stdVecVal l,
          by simp [evalProgFunc, hbind, hstmt], rfl⟩
    · rw [ite_eq_right h1] at hfwd
      simp only [Except.ok.injEq] at hfwd
      obtain rfl := hfwd
      have hloVar : evalExpr (.var "lo")
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
      have hhiVar : evalExpr (.var "hi")
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
      have hltB : loB.ult hiB = false :=
        ult_ofNat_eq_false hloN hhiN h1
      have gloF : evalExpr (.ult (.var "lo") (.var "hi"))
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ hloVar hhiVar
        rwa [hltB] at h
      have hv₀ : envLookup [("v", .stdVecVal l),
          ("lo", .u64 loB), ("hi", .u64 hiB)] "v" =
          some (.stdVecVal l) := by rfl
      have hret : evalProgStmt vecQuicksortProg (F + 1)
          (.return_ (.var "v"))
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
            .returned (.stdVecVal l)) :=
        evalProgStmt_return _ _ _ _ _
          (evalExpr_var_hit _ _ _ hv₀)
      have hstmt : evalProgStmt vecQuicksortProg (F + 1)
          vecQuicksortFunc.body
          [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
          .ok ([("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)],
            .returned (.stdVecVal l)) := by
        rw [hbody,
          evalProgStmt_if_false vecQuicksortProg (F + 1) _ _ _ _ gloF]
        exact hret
      exact ⟨.stdVecVal l,
        by simp [evalProgFunc, hbind, hstmt], rfl⟩
/-- Whole-function value-level bridge, error direction: a failing
    forward run fails loudly with the same panic (the `_err` twin;
    succeeding calls reuse the `_ok` bridge). -/
theorem evalProgFunc_vecQuicksort_err (F : Nat)
    (l : List (BitVec 32)) (lo hi : Nat) (loB hiB : BitVec 64)
    (e : Panic)
    (hloN : loB.toNat = lo) (hhiN : hiB.toNat = hi)
    (hl64 : l.length < 2 ^ 64)
    (hlo_le : lo ≤ hi) (hhi_le : hi ≤ l.length)
    (hfwd : vecQuicksortFwd l F lo hi = .error e) :
    evalProgFunc vecQuicksortProg F vecQuicksortFunc
      [.stdVecVal l, .u64 loB, .u64 hiB] = .error e := by
  induction F generalizing l lo hi loB hiB e with
  | zero =>
    have hbind : bindArgs vecQuicksortFunc.args
        [.stdVecVal l, .u64 loB, .u64 hiB] =
        some [("v", .stdVecVal l), ("lo", .u64 loB),
          ("hi", .u64 hiB)] := rfl
    have hbody : vecQuicksortFunc.body =
        (.if_ (.ult (.var "lo") (.var "hi"))
          (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
                    (.usub (.var "hi") (.var "lo")))
            (.seq (.let_ "pivot" (.i 32)
                    (.stdVecAt "v"
                      (.usub (.var "hi")
                        (.lit (.u64 (BitVec.ofNat 64 1))))))
              (.seq (.let_ "s" (.u 64) (.var "lo"))
                (.seq (.let_ "i" (.u 64) (.var "lo"))
                  (.seq qsPartLoop
                    (.seq qsPlacePivot
                      (.seq (.let_ "s1" (.u 64)
                              (.uadd (.var "s")
                                (.lit (.u64 (BitVec.ofNat 64 1)))))
                        (.seq qsCallLeft
                          (.seq qsCallRight
                            (.return_ (.var "v"))))))))))
            (.return_ (.var "v")))
          (.return_ (.var "v"))) := rfl
    simp only [vecQuicksortFwd] at hfwd
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at hfwd
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at hfwd
        cases hfwd
        have hloVar₀ : evalExpr (.var "lo")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hhiVar₀ : evalExpr (.var "hi")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
        have hltB : loB.ult hiB = true :=
          ult_ofNat_eq_true hloN hhiN h1
        have gloT : evalExpr (.ult (.var "lo") (.var "hi"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _ hloVar₀ hhiVar₀
          rwa [hltB] at h
        have hle64 : loB.toNat ≤ hiB.toNat := by
          rw [hloN, hhiN]; exact hlo_le
        have hsubOl : evalExpr (.usub (.var "hi") (.var "lo"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 (hiB - loB)) :=
          evalExpr_usub_u64u64 _ _ _ _ _ hhiVar₀ hloVar₀
        have hsubNOl : (hiB - loB).toNat = hi - lo := by
          rw [u64sub_toNat_exact hiB loB hle64, hloN, hhiN]
        have h1of : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
        have h2ltT : (BitVec.ofNat 64 1).ult (hiB - loB) = true := by
          have h1B : (1 : BitVec 64).toNat = 1 := rfl
          rw [← h1of, BitVec.ult_eq_decide, h1B, hsubNOl]
          exact decide_eq_true h2
        have g2T : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
            (.usub (.var "hi") (.var "lo")))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b true) := by
          have h : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
              (.usub (.var "hi") (.var "lo")))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.b ((BitVec.ofNat 64 1).ult (hiB - loB))) :=
            evalExpr_ult_u64lit _ _ _ _ hsubOl
          rwa [h2ltT] at h
        have hv₀ : envLookup [("v", .stdVecVal l),
            ("lo", .u64 loB), ("hi", .u64 hiB)] "v" =
            some (.stdVecVal l) := by rfl
        have h1B' : (1 : BitVec 64).toNat = 1 := rfl
        have h1hle : (1 : BitVec 64).toNat ≤ hiB.toNat := by
          rw [h1B', hhiN]; omega
        have hsubN : (hiB - 1).toNat = hi - 1 := by
          rw [u64sub_toNat_exact _ _ h1hle, h1B', hhiN]
        have hsubHi : evalExpr
            (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 (hiB - 1)) :=
          evalExpr_u64_usub _ _ _ _ hhiVar₀
        have hhi1len : hi - 1 < l.length := by omega
        have hpivM : l[hi - 1]? = some l[hi - 1] :=
          List.getElem?_eq_getElem hhi1len
        have hpivB : evalExpr
            (.stdVecAt "v"
              (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.i32 l[hi - 1]) := by
          have hget : l[(hiB - 1).toNat]? = some l[hi - 1] := by
            rw [hsubN]; exact hpivM
          exact evalExpr_stdVecAt_some _ _ _ _ _ _ hv₀ hsubHi hget
        have hletPiv := revLet vecQuicksortProg 0 "pivot" (.i 32)
          _ _ _ hpivB
        have hsVarP : evalExpr (.var "lo")
            (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
              ("hi", .u64 hiB)] "pivot" (.i32 l[hi - 1])) =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hletS := revLet vecQuicksortProg 0 "s" (.u 64)
          _ _ _ hsVarP
        have hiVarS : evalExpr (.var "lo")
            (envExtend (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
              ("hi", .u64 hiB)] "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hletI := revLet vecQuicksortProg 0 "i" (.u 64)
          _ _ _ hiVarS
        have hiVarL : evalExpr (.var "i")
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB)) =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hhiVarL : evalExpr (.var "hi")
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB)) =
            .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
        have hsubL : evalExpr
            (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB)) =
            .ok (.u64 (hiB - 1)) :=
          evalExpr_u64_usub _ _ _ _ hhiVarL
        have htrueL : loB.ult (hiB - 1) = true :=
          ult_ofNat_eq_true hloN hsubN (by omega)
        have hguardT0 : evalExpr (.ult (.var "i")
            (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))))
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB)) =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 (.var "i")
            (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) _ _ _
            hiVarL hsubL
          rwa [htrueL] at h
        have hloop0 : evalProgStmt vecQuicksortProg 0 qsPartLoop
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB)) =
            .error .AssertFail := by
          simp only [qsPartLoop]
          simp [evalProgStmt, evalStmtFuel, evalStmtZero, evalStmtWith,
            evalStmtZeroHandler, hguardT0]
        have hstmt0 : evalProgStmt vecQuicksortProg 0
            vecQuicksortFunc.body
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .error .AssertFail := by
          rw [hbody,
            evalProgStmt_if_true vecQuicksortProg 0 _ _ _ _ gloT,
            evalProgStmt_if_true vecQuicksortProg 0 _ _ _ _ g2T,
            evalProgStmt_seq_fallthrough vecQuicksortProg 0 _ _ _ _
              hletPiv,
            evalProgStmt_seq_fallthrough vecQuicksortProg 0 _ _ _ _
              hletS,
            evalProgStmt_seq_fallthrough vecQuicksortProg 0 _ _ _ _
              hletI,
            evalProgStmt_seq_err vecQuicksortProg 0 _ _ _ _ hloop0]
        unfold evalProgFunc
        simp only [hbind, hstmt0]
      · rw [ite_eq_right h2] at hfwd
        cases hfwd
    · rw [ite_eq_right h1] at hfwd
      cases hfwd
  | succ F ih =>
    have hbind : bindArgs vecQuicksortFunc.args
        [.stdVecVal l, .u64 loB, .u64 hiB] =
        some [("v", .stdVecVal l), ("lo", .u64 loB),
          ("hi", .u64 hiB)] := rfl
    have hbody : vecQuicksortFunc.body =
        (.if_ (.ult (.var "lo") (.var "hi"))
          (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
                    (.usub (.var "hi") (.var "lo")))
            (.seq (.let_ "pivot" (.i 32)
                    (.stdVecAt "v"
                      (.usub (.var "hi")
                        (.lit (.u64 (BitVec.ofNat 64 1))))))
              (.seq (.let_ "s" (.u 64) (.var "lo"))
                (.seq (.let_ "i" (.u 64) (.var "lo"))
                  (.seq qsPartLoop
                    (.seq qsPlacePivot
                      (.seq (.let_ "s1" (.u 64)
                              (.uadd (.var "s")
                                (.lit (.u64 (BitVec.ofNat 64 1)))))
                        (.seq qsCallLeft
                          (.seq qsCallRight
                            (.return_ (.var "v"))))))))))
            (.return_ (.var "v")))
          (.return_ (.var "v"))) := rfl
    simp only [vecQuicksortFwd] at hfwd
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at hfwd
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at hfwd
        have hhi1 : 1 ≤ hi := by omega
        have hhi1len : hi - 1 < l.length := by omega
        have hpivM : l[hi - 1]? = some l[hi - 1] :=
          List.getElem?_eq_getElem hhi1len
        simp only [hpivM] at hfwd
        have hv₀ : envLookup [("v", .stdVecVal l),
            ("lo", .u64 loB), ("hi", .u64 hiB)] "v" =
            some (.stdVecVal l) := by rfl
        have hloVar₀ : evalExpr (.var "lo")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hhiVar₀ : evalExpr (.var "hi")
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 hiB) := evalExpr_var_hit _ _ _ (by rfl)
        have hltB : loB.ult hiB = true :=
          ult_ofNat_eq_true hloN hhiN h1
        have gloT : evalExpr (.ult (.var "lo") (.var "hi"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _ hloVar₀ hhiVar₀
          rwa [hltB] at h
        have hle64 : loB.toNat ≤ hiB.toNat := by
          rw [hloN, hhiN]; exact hlo_le
        have hsubOl : evalExpr (.usub (.var "hi") (.var "lo"))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 (hiB - loB)) :=
          evalExpr_usub_u64u64 _ _ _ _ _ hhiVar₀ hloVar₀
        have hsubNOl : (hiB - loB).toNat = hi - lo := by
          rw [u64sub_toNat_exact hiB loB hle64, hloN, hhiN]
        have h1of : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
        have h2ltT : (BitVec.ofNat 64 1).ult (hiB - loB) = true := by
          have h1B : (1 : BitVec 64).toNat = 1 := rfl
          rw [← h1of, BitVec.ult_eq_decide, h1B, hsubNOl]
          exact decide_eq_true h2
        have g2T : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
            (.usub (.var "hi") (.var "lo")))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.b true) := by
          have h : evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
              (.usub (.var "hi") (.var "lo")))
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
              .ok (.b ((BitVec.ofNat 64 1).ult (hiB - loB))) :=
            evalExpr_ult_u64lit _ _ _ _ hsubOl
          rwa [h2ltT] at h
        have h1B' : (1 : BitVec 64).toNat = 1 := rfl
        have h1hle : (1 : BitVec 64).toNat ≤ hiB.toNat := by
          rw [h1B', hhiN]; omega
        have hsubN : (hiB - 1).toNat = hi - 1 := by
          rw [u64sub_toNat_exact _ _ h1hle, h1B', hhiN]
        have hsubHi : evalExpr
            (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.u64 (hiB - 1)) :=
          evalExpr_u64_usub _ _ _ _ hhiVar₀
        have hpivB : evalExpr
            (.stdVecAt "v"
              (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))))
            [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)] =
            .ok (.i32 l[hi - 1]) := by
          have hget : l[(hiB - 1).toNat]? = some l[hi - 1] := by
            rw [hsubN]; exact hpivM
          exact evalExpr_stdVecAt_some _ _ _ _ _ _ hv₀ hsubHi hget
        have hletPiv := revLet vecQuicksortProg (F + 1) "pivot" (.i 32)
          _ _ _ hpivB
        have hsVarP : evalExpr (.var "lo")
            (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
              ("hi", .u64 hiB)] "pivot" (.i32 l[hi - 1])) =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hletS := revLet vecQuicksortProg (F + 1) "s" (.u 64)
          _ _ _ hsVarP
        have hiVarS : evalExpr (.var "lo")
            (envExtend (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
              ("hi", .u64 hiB)] "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) =
            .ok (.u64 loB) := evalExpr_var_hit _ _ _ (by rfl)
        have hletI := revLet vecQuicksortProg (F + 1) "i" (.u 64)
          _ _ _ hiVarS
        have hvL : envLookup
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
            "v" = some (.stdVecVal l) := by rfl
        have hpivL : envLookup
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
            "pivot" = some (.i32 l[hi - 1]) := by rfl
        have hhiL : envLookup
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
            "hi" = some (.u64 hiB) := by rfl
        have hloL : envLookup
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
            "lo" = some (.u64 loB) := by rfl
        have hiiL : envLookup
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
            "i" = some (.u64 loB) := by rfl
        have hsL : envLookup
            (envExtend (envExtend (envExtend
              [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
              "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
            "s" = some (.u64 loB) := by rfl
        match hpart : qsPartFwd l[hi - 1] l (F + 1) hi lo lo with
        | .error e =>
            simp only [hpart] at hfwd
            cases hfwd
            have hloopE := valQsPartLoop_err vecQuicksortProg (F + 1)
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              l l[hi - 1] hi lo lo loB hiB loB loB e
              hloN hloN hhiN hl64 hvL hpivL hhiL hloL hiiL hsL
              (by omega) (by omega) hhi_le hpart
            simp only [qsPartLoop] at hloopE
            have hstmt : evalProgStmt vecQuicksortProg (F + 1)
                vecQuicksortFunc.body
                [("v", .stdVecVal l), ("lo", .u64 loB),
                  ("hi", .u64 hiB)] =
                .error e := by
              rw [hbody]
              simp only [qsPartLoop, qsPlacePivot, qsCallLeft,
                qsCallRight]
              rw [evalProgStmt_if_true vecQuicksortProg (F + 1)
                  _ _ _ _ gloT,
                evalProgStmt_if_true vecQuicksortProg (F + 1)
                  _ _ _ _ g2T,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hletPiv,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hletS,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hletI,
                evalProgStmt_seq_err vecQuicksortProg (F + 1)
                  _ _ _ _ hloopE]
            have hfin : evalProgFunc vecQuicksortProg (F + 1)
                vecQuicksortFunc
                [.stdVecVal l, .u64 loB, .u64 hiB] = .error e := by
              simp [evalProgFunc, hbind, hstmt]
            exact hfin
        | .ok (s₁, l₁) =>
          simp only [hpart] at hfwd
          obtain ⟨ρ₁, hloop, hout₁, ⟨sB₁, hsB₁, hsN₁⟩, hs'le,
              ⟨iB₁, hiB₁, hiN₁⟩, hpiv₁, hhi₁, hlo₁⟩ :=
            valQsPartLoop_ok vecQuicksortProg (F + 1)
              (envExtend (envExtend (envExtend
                [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
                "pivot" (.i32 l[hi - 1])) "s" (.u64 loB)) "i" (.u64 loB))
              l l[hi - 1] hi lo lo loB hiB loB loB s₁ l₁
              hhiN hloN hloN hl64 hhi_le hhi1
              hvL hpivL hhiL hloL hiiL hsL (by omega) (by omega) hpart
          simp only [qsPartLoop] at hloop
          have hlen₁ : l₁.length = l.length :=
            qsPartFwd_length _ _ _ _ _ _ _ _ hpart
          have hl64₁ : l₁.length < 2 ^ 64 := by
            rw [hlen₁]; exact hl64
          have hs₁lt : s₁ < l₁.length := by omega
          have hhi1' : hi - 1 < l₁.length := by omega
          have hwM : l₁[s₁]? = some l₁[s₁] :=
            List.getElem?_eq_getElem hs₁lt
          have hpM : l₁[hi - 1]? = some l₁[hi - 1] :=
            List.getElem?_eq_getElem hhi1'
          simp only [hwM, hpM] at hfwd
          have hhiVar₁ : evalExpr (.var "hi") ρ₁ =
              .ok (.u64 hiB) := evalExpr_var_hit _ _ _ hhi₁
          have hsVar₁ : evalExpr (.var "s") ρ₁ =
              .ok (.u64 sB₁) := evalExpr_var_hit _ _ _ hsB₁
          have hsubHi₁ : evalExpr
              (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
              .ok (.u64 (hiB - 1)) :=
            evalExpr_u64_usub _ _ _ _ hhiVar₁
          have hgetS₁ : l₁[sB₁.toNat]? = some l₁[s₁] := by
            rw [hsN₁]; exact hwM
          have hgetOld : l₁[(hiB - 1).toNat]? = some l₁[hi - 1] := by
            rw [hsubN]; exact hpM
          have hatS₁ : evalExpr (.stdVecAt "v" (.var "s")) ρ₁ =
              .ok (.i32 l₁[s₁]) :=
            evalExpr_stdVecAt_some _ _ _ _ _ _ hout₁ hsVar₁ hgetS₁
          obtain ⟨ρ₂, hu₁⟩ := envUpdate_some_of_lookup ρ₁ "v"
            (.stdVecVal l₁)
            (.stdVecVal (l₁.set (hiB - 1).toNat l₁[s₁])) hout₁
          have hstep1 := revVecSet vecQuicksortProg (F + 1) "v"
            (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
            (.stdVecAt "v" (.var "s")) ρ₁ (hiB - 1) l₁[s₁] l₁
            l₁[hi - 1] ρ₂ hsubHi₁ hatS₁ hout₁ hgetOld hu₁
          have hout₂ : envLookup ρ₂ "v" =
              some (.stdVecVal (l₁.set (hiB - 1).toNat l₁[s₁])) :=
            envLookup_update_hit _ _ _ _ hu₁
          rw [hsubN] at hu₁
          have hout₂' : envLookup ρ₂ "v" =
              some (.stdVecVal (l₁.set (hi - 1) l₁[s₁])) :=
            envLookup_update_hit _ _ _ _ hu₁
          have hs₂ : envLookup ρ₂ "s" = some (.u64 sB₁) := by
            rw [envLookup_update_miss _ _ _ _ _
              (show ("s" : String) ≠ "v" by decide) hu₁]
            exact hsB₁
          have hpiv₂ : envLookup ρ₂ "pivot" =
              some (.i32 l[hi - 1]) := by
            rw [envLookup_update_miss _ _ _ _ _
              (show ("pivot" : String) ≠ "v" by decide) hu₁]
            exact hpiv₁
          have hhi₂ : envLookup ρ₂ "hi" = some (.u64 hiB) := by
            rw [envLookup_update_miss _ _ _ _ _
              (show ("hi" : String) ≠ "v" by decide) hu₁]
            exact hhi₁
          have hlo₂ : envLookup ρ₂ "lo" = some (.u64 loB) := by
            rw [envLookup_update_miss _ _ _ _ _
              (show ("lo" : String) ≠ "v" by decide) hu₁]
            exact hlo₁
          have hsVar₂ : evalExpr (.var "s") ρ₂ =
              .ok (.u64 sB₁) := evalExpr_var_hit _ _ _ hs₂
          have hpivVar₂ : evalExpr (.var "pivot") ρ₂ =
              .ok (.i32 l[hi - 1]) := evalExpr_var_hit _ _ _ hpiv₂
          have hlenSet1 : (l₁.set (hi - 1) l₁[s₁]).length =
              l₁.length := List.length_set
          have hs₁lt1 : s₁ < (l₁.set (hi - 1) l₁[s₁]).length := by
            rw [hlenSet1]; exact hs₁lt
          have hget₂ : ((l₁.set (hi - 1) l₁[s₁]))[sB₁.toNat]? =
              some (((l₁.set (hi - 1) l₁[s₁]))[s₁]) := by
            rw [hsN₁]
            exact List.getElem?_eq_getElem hs₁lt1
          obtain ⟨ρ₃, hu₂⟩ := envUpdate_some_of_lookup ρ₂ "v"
            (.stdVecVal (l₁.set (hi - 1) l₁[s₁]))
            (.stdVecVal (((l₁.set (hi - 1) l₁[s₁])).set sB₁.toNat
              l[hi - 1])) hout₂'
          have hstep2 := revVecSet vecQuicksortProg (F + 1) "v"
            (.var "s") (.var "pivot") ρ₂ sB₁ l[hi - 1]
            (l₁.set (hi - 1) l₁[s₁])
            (((l₁.set (hi - 1) l₁[s₁]))[s₁]) ρ₃
            hsVar₂ hpivVar₂ hout₂' hget₂ hu₂
          rw [hsN₁] at hu₂
          have hout₃ : envLookup ρ₃ "v" = some (.stdVecVal
              (((l₁.set (hi - 1) l₁[s₁])).set s₁ l[hi - 1])) :=
            envLookup_update_hit _ _ _ _ hu₂
          have hs₃ : envLookup ρ₃ "s" = some (.u64 sB₁) := by
            rw [envLookup_update_miss _ _ _ _ _
              (show ("s" : String) ≠ "v" by decide) hu₂]
            exact hs₂
          have hhi₃ : envLookup ρ₃ "hi" = some (.u64 hiB) := by
            rw [envLookup_update_miss _ _ _ _ _
              (show ("hi" : String) ≠ "v" by decide) hu₂]
            exact hhi₂
          have hlo₃ : envLookup ρ₃ "lo" = some (.u64 loB) := by
            rw [envLookup_update_miss _ _ _ _ _
              (show ("lo" : String) ≠ "v" by decide) hu₂]
            exact hlo₂
          have hsVar₃ : evalExpr (.var "s") ρ₃ =
              .ok (.u64 sB₁) := evalExpr_var_hit _ _ _ hs₃
          have hevS1 : evalExpr
              (.uadd (.var "s")
                (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ =
              .ok (.u64 (sB₁ + 1)) :=
            evalExpr_uadd_u64 _ _ _ _ _ hsVar₃
              (by simp [evalExpr, litVal])
          have htoNat : (sB₁ + 1).toNat = s₁ + 1 := by
            rw [revU64_succ_toNat sB₁ l₁.length
              (by rw [hsN₁]; exact hs₁lt) hl64₁, hsN₁]
          have hletS1 := revLet vecQuicksortProg (F + 1) "s1"
            (.u 64) _ _ _ hevS1
          have hs1₄ : envLookup
              (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "s1" =
              some (.u64 (sB₁ + 1)) := envExtend_hit _ _ _
          have hv₄ : envLookup
              (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v" =
              some (.stdVecVal
                (((l₁.set (hi - 1) l₁[s₁])).set s₁ l[hi - 1])) :=
            envLookup_extend_miss _ _ _ _ _ hout₃ (by decide)
          have hlo₄ : envLookup
              (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "lo" =
              some (.u64 loB) :=
            envLookup_extend_miss _ _ _ _ _ hlo₃ (by decide)
          have hs₄ : envLookup
              (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "s" =
              some (.u64 sB₁) :=
            envLookup_extend_miss _ _ _ _ _ hs₃ (by decide)
          have hargsL : lookupArgs
              (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) ["v", "lo", "s"] =
              some [.stdVecVal
                (((l₁.set (hi - 1) l₁[s₁])).set s₁ l[hi - 1]),
                .u64 loB, .u64 sB₁] :=
            lookupArgs_cons_hit _ _ _ _ _ hv₄
              (lookupArgs_cons_hit _ _ _ _ _ hlo₄
                (lookupArgs_cons_hit _ _ _ _ _ hs₄
                  (lookupArgs_nil _)))
          have hfind : findFunc vecQuicksortProg
              vecQuicksortName = some vecQuicksortFunc :=
            findFunc_hit vecQuicksortFunc []
          have hlenL1' : ((((l₁.set (hi - 1) l₁[s₁])).set s₁
              l[hi - 1]).length) = l₁.length := by
            simp [List.length_set]
          have hL64 : ((((l₁.set (hi - 1) l₁[s₁])).set s₁
              l[hi - 1]).length) < 2 ^ 64 := by
            rw [hlenL1']; exact hl64₁
          have hLlo : lo ≤ s₁ :=
            qsPartFwd_le _ _ _ _ _ _ _ _ hpart
          have hLhi : s₁ ≤ ((((l₁.set (hi - 1) l₁[s₁])).set s₁
              l[hi - 1]).length) := by omega
          have hplace : evalProgStmt vecQuicksortProg (F + 1)
              (.seq (.vecSet "v"
                (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
                (.stdVecAt "v" (.var "s")))
                (.vecSet "v" (.var "s") (.var "pivot"))) ρ₁ =
              .ok (ρ₃, .fellThrough) := by
            rw [evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
              _ _ _ _ hstep1]
            exact hstep2
          match hleft : vecQuicksortFwd
              ((l₁.set (hi - 1) l₁[s₁]).set s₁ l[hi - 1]) F lo s₁ with
          | .error e₁ =>
            simp only [hleft] at hfwd
            rw [Except.error.injEq] at hfwd
            have hL := ih (((l₁.set (hi - 1) l₁[s₁])).set s₁
                l[hi - 1]) lo s₁ loB sB₁ e₁ hloN hsN₁ hL64 hLlo hLhi
              hleft
            have hcallL := evalProgStmt_callProg_err vecQuicksortProg
              F "v" vecQuicksortName ["v", "lo", "s"]
              (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) _ _ _
              hargsL hfind hL
            have hstmt : evalProgStmt vecQuicksortProg (F + 1)
                vecQuicksortFunc.body
                [("v", .stdVecVal l), ("lo", .u64 loB),
                  ("hi", .u64 hiB)] =
                .error e₁ := by
              rw [hbody]
              simp only [qsPartLoop, qsPlacePivot, qsCallLeft,
                qsCallRight]
              rw [evalProgStmt_if_true vecQuicksortProg (F + 1)
                  _ _ _ _ gloT,
                evalProgStmt_if_true vecQuicksortProg (F + 1)
                  _ _ _ _ g2T,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hletPiv,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hletS,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hletI,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hloop,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hplace,
                evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                  _ _ _ _ hletS1,
                evalProgStmt_seq_err vecQuicksortProg (F + 1)
                  _ _ _ _ hcallL]
            simp [evalProgFunc, hbind, hstmt, hfwd]
          | .ok l2 =>
            simp only [hleft] at hfwd
            have hL := evalProgFunc_vecQuicksort_ok F
              (((l₁.set (hi - 1) l₁[s₁])).set s₁ l[hi - 1]) lo s₁
              loB sB₁ hloN hsN₁ hL64 hLlo hLhi l2 hleft
            obtain ⟨_, hLeval, rfl⟩ := hL
            have hcallL := evalProgStmt_callProg_ok vecQuicksortProg
              F "v" vecQuicksortName ["v", "lo", "s"]
              (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) _ _ _
              hargsL hfind hLeval
            have hhi₄ : envLookup
                (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "hi" =
                some (.u64 hiB) :=
              envLookup_extend_miss _ _ _ _ _ hhi₃ (by decide)
            have hv₅ : envLookup (envExtend
                (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                (.stdVecVal l2)) "v" = some (.stdVecVal l2) :=
              envExtend_hit _ _ _
            have hs1₅ : envLookup (envExtend
                (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                (.stdVecVal l2)) "s1" = some (.u64 (sB₁ + 1)) :=
              envLookup_extend_miss _ _ _ _ _ hs1₄ (by decide)
            have hhi₅ : envLookup (envExtend
                (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                (.stdVecVal l2)) "hi" = some (.u64 hiB) :=
              envLookup_extend_miss _ _ _ _ _ hhi₄ (by decide)
            have hargsR : lookupArgs (envExtend
                (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                (.stdVecVal l2)) ["v", "s1", "hi"] =
                some [.stdVecVal l2, .u64 (sB₁ + 1), .u64 hiB] :=
              lookupArgs_cons_hit _ _ _ _ _ hv₅
                (lookupArgs_cons_hit _ _ _ _ _ hs1₅
                  (lookupArgs_cons_hit _ _ _ _ _ hhi₅
                    (lookupArgs_nil _)))
            have hlenL2 : l2.length =
                ((((l₁.set (hi - 1) l₁[s₁])).set s₁
                  l[hi - 1]).length) :=
              vecQuicksortFwd_length _ _ _ _ _ hleft
            match hright : vecQuicksortFwd l2 F (s₁ + 1) hi with
            | .error e₁ =>
              simp only [hright] at hfwd
              rw [Except.error.injEq] at hfwd
              have htoNatR : (sB₁ + 1).toNat = s₁ + 1 := htoNat
              have hR := ih l2 (s₁ + 1) hi (sB₁ + 1) hiB e₁
                htoNat hhiN
                (by rw [hlenL2]; exact hL64) (by omega) (by omega)
                hright
              have hcallR := evalProgStmt_callProg_err vecQuicksortProg
                F "v" vecQuicksortName ["v", "s1", "hi"]
                (envExtend (envExtend ρ₃ "s1" (.u64 (sB₁ + 1))) "v"
                  (.stdVecVal l2)) _ _ _
                hargsR hfind hR
              have hstmt : evalProgStmt vecQuicksortProg (F + 1)
                  vecQuicksortFunc.body
                  [("v", .stdVecVal l), ("lo", .u64 loB),
                    ("hi", .u64 hiB)] =
                  .error e₁ := by
                rw [hbody]
                simp only [qsPartLoop, qsPlacePivot, qsCallLeft,
                  qsCallRight]
                rw [evalProgStmt_if_true vecQuicksortProg (F + 1)
                    _ _ _ _ gloT,
                  evalProgStmt_if_true vecQuicksortProg (F + 1)
                    _ _ _ _ g2T,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletPiv,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletS,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletI,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hloop,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hplace,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hletS1,
                  evalProgStmt_seq_fallthrough vecQuicksortProg (F + 1)
                    _ _ _ _ hcallL,
                  evalProgStmt_seq_err vecQuicksortProg (F + 1)
                    _ _ _ _ hcallR]
              simp [evalProgFunc, hbind, hstmt, hfwd]
            | .ok l3 =>
              simp only [hright] at hfwd
              cases hfwd
      · rw [ite_eq_right h2] at hfwd
        cases hfwd
    · rw [ite_eq_right h1] at hfwd
      cases hfwd

end VecQuicksort
