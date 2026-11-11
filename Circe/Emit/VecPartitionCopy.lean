import Circe.Emit.VecCopyIf
import Circe.Lemmas.TwoCursor

/-! Pillar-2 next slice: dual-record partition
(`vec_partition_copy`, the `std::partition_copy` idiom) — the
first dual-record write. The P2-M3 Lomuto predicate test
(`a.at(r) < pivot`, signed `slt`) over a read-only input,
writing keepers into one caller-sized record and droppers
into a second (the M12 out-borrow discipline composed
twice). Read cursor `r` scans from 0; write cursors `wYes` /
`wNo` advance independently; each store is capacity-guarded
(short record fails loud); the return is the keeper count
(`wYes + wNo = a.size()` at exit, so the dropper count is
implied). Pure `List.filter` oracle, twice (keepers and
droppers) — no new oracle module. -/

/-- Function name (Itanium mangling of a `vec_partition_copy`
    free function taking `const vector<int>&`,
    `vector<int>&`, `vector<int>&`, `int`, returning
    `unsigned long`). -/
def vecPartitionCopyName : String :=
  "_Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i"

/-- Loop body: keeper test `a[r] < pivot` (signed); keepers
    store at `yes[wYes]` under the `wYes` guard, droppers at
    `no[wNo]` under the `wNo` guard; the read cursor always
    advances. -/
def vecPartitionCopyBody : CStmt :=
  (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                     (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                     (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
    (.assign "r" (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- Loop `while (r < n) body`. -/
def vecPartitionCopyLoop : CStmt :=
  (.while_ (.ult (.var "r") (.stdVecLen "a")) vecPartitionCopyBody)

/-- Whole function: the `let_` prelude binding `r`, `wYes`,
    `wNo` at 0 (no seed, no empty early exit — the loop guard
    handles the empty input), the loop, and the keeper-count
    return. -/
def vecPartitionCopyFunc : Func :=
  ⟨vecPartitionCopyName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "yes", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "no", ty := stdVecObjTy, role := .mutBorrow 1 },
    { name := "pivot", ty := .i 32, role := .owned }],
   .u 64,
   (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "wYes" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq (.let_ "wNo" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq vecPartitionCopyLoop
           (.return_ (.var "wYes"))))))⟩

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + source words + both record words + read
    cursor + both write cursors. Fuel 0 returns the state so
    far; the `none` arm of the source read is unreachable
    in-invariant (the guard gives `r < la.length`); each
    record slot is cased like the evaluator, so a miss fails
    loud and no capacity hypothesis appears here. -/
def partitionCopyFwd (pivot : BitVec 32) :
    List (BitVec 32) → List (BitVec 32) → List (BitVec 32) →
      Nat → Nat → Nat → Nat →
      Result (Nat × Nat × Nat × List (BitVec 32) × List (BitVec 32))
  | _, yes, no, 0, r, wYes, wNo => .ok (r, wYes, wNo, yes, no)
  | la, yes, no, fuel + 1, r, wYes, wNo =>
    if _ : r < la.length then
      match la[r]? with
      | none => .error .AssertFail
      | some y =>
        if y.slt pivot then
          match yes[wYes]? with
          | none => .error .AssertFail
          | some _ => partitionCopyFwd pivot la (yes.set wYes y) no
              fuel (r + 1) (wYes + 1) wNo
        else
          match no[wNo]? with
          | none => .error .AssertFail
          | some _ => partitionCopyFwd pivot la yes (no.set wNo y)
              fuel (r + 1) wYes (wNo + 1)
    else .ok (r, wYes, wNo, yes, no)

/-- Whole-function forward: the loop at measure-exact fuel
    from the `(0, 0, 0)` cursors, then the keeper count. -/
def vecPartitionCopyFwd (la yes no : List (BitVec 32))
    (pivot : BitVec 32) : Result Value :=
  match partitionCopyFwd pivot la yes no la.length 0 0 0 with
  | .error e => .error e
  | .ok (_, wYes', _, _, _) => .ok (.u64 (BitVec.ofNat 64 wYes'))

/-- Program over which the entry evaluates (no callees: the body
    is straight-line `if` / `vecSet` / `assign` / `fail`). -/
abbrev vecPartitionCopyProg : Prog := [vecPartitionCopyFunc]

/-! ## Filter boundary lemmas (signed take-succ, both records) -/

/-- Keepers before `r + 1` extend keepers before `r` when
    `la[r]` is a keeper (the take-succ step for the keeper
    count and prefix invariants). -/
theorem partFilterYes_take_succ (pivot : BitVec 32)
    (la : List (BitVec 32)) (r : Nat) (y : BitVec 32)
    (hy : la[r]? = some y)
    (hkeep : (y.slt pivot) = true) :
    ((la.take (r + 1)).filter (fun z => z.slt pivot)) =
      ((la.take r).filter (fun z => z.slt pivot)) ++ [y] := by
  have htake : la.take (r + 1) = la.take r ++ [y] := by
    have h0 : la.take (r + 1) = la.take r ++ la[r]?.toList :=
      List.take_add_one
    have h1 : la[r]?.toList = [y] := by rw [hy]; rfl
    rwa [h1] at h0
  rw [htake, List.filter_append]
  simp [hkeep]

/-- Keepers before `r + 1` equal keepers before `r` when
    `la[r]` is a dropper. -/
theorem partFilterYes_take_succ_drop (pivot : BitVec 32)
    (la : List (BitVec 32)) (r : Nat) (y : BitVec 32)
    (hy : la[r]? = some y)
    (hdrop : (y.slt pivot) = false) :
    ((la.take (r + 1)).filter (fun z => z.slt pivot)) =
      ((la.take r).filter (fun z => z.slt pivot)) := by
  have htake : la.take (r + 1) = la.take r ++ [y] := by
    have h0 : la.take (r + 1) = la.take r ++ la[r]?.toList :=
      List.take_add_one
    have h1 : la[r]?.toList = [y] := by rw [hy]; rfl
    rwa [h1] at h0
  rw [htake, List.filter_append]
  simp [hdrop]

/-- Droppers before `r + 1` extend droppers before `r` when
    `la[r]` is a dropper. -/
theorem partFilterNo_take_succ (pivot : BitVec 32)
    (la : List (BitVec 32)) (r : Nat) (y : BitVec 32)
    (hy : la[r]? = some y)
    (hkeep : (!(y.slt pivot)) = true) :
    ((la.take (r + 1)).filter (fun z => !(z.slt pivot))) =
      ((la.take r).filter (fun z => !(z.slt pivot))) ++ [y] := by
  have htake : la.take (r + 1) = la.take r ++ [y] := by
    have h0 : la.take (r + 1) = la.take r ++ la[r]?.toList :=
      List.take_add_one
    have h1 : la[r]?.toList = [y] := by rw [hy]; rfl
    rwa [h1] at h0
  rw [htake, List.filter_append]
  simp [hkeep]

/-- Droppers before `r + 1` equal droppers before `r` when
    `la[r]` is a keeper. -/
theorem partFilterNo_take_succ_drop (pivot : BitVec 32)
    (la : List (BitVec 32)) (r : Nat) (y : BitVec 32)
    (hy : la[r]? = some y)
    (hdrop : (!(y.slt pivot)) = false) :
    ((la.take (r + 1)).filter (fun z => !(z.slt pivot))) =
      ((la.take r).filter (fun z => !(z.slt pivot))) := by
  have htake : la.take (r + 1) = la.take r ++ [y] := by
    have h0 : la.take (r + 1) = la.take r ++ la[r]?.toList :=
      List.take_add_one
    have h1 : la[r]?.toList = [y] := by rw [hy]; rfl
    rwa [h1] at h0
  rw [htake, List.filter_append]
  simp [hdrop]

/-- Keeper split at `r + 1`: total keepers = keepers before +
    keepers from (the capacity argument for the next
    keeper write). -/
theorem partFilterYes_split (pivot : BitVec 32)
    (la : List (BitVec 32)) (r : Nat)
    (_hle : r + 1 ≤ la.length) :
    (la.filter (fun y => y.slt pivot)).length =
      (((la.take (r + 1)).filter (fun y => y.slt pivot)).length +
        ((la.drop (r + 1)).filter (fun y => y.slt pivot)).length) := by
  have h : la.take (r + 1) ++ la.drop (r + 1) = la :=
    List.take_append_drop (r + 1) la
  have hfilter : (((la.take (r + 1) ++ la.drop (r + 1)).filter
      (fun y => y.slt pivot))).length =
      (((la.take (r + 1)).filter (fun y => y.slt pivot))).length +
        (((la.drop (r + 1)).filter
          (fun y => y.slt pivot))).length := by
    rw [List.filter_append, List.length_append]
  rwa [h] at hfilter

/-- Dropper split at `r + 1`: total droppers = droppers before
    + droppers from (the capacity argument for the next
    dropper write). -/
theorem partFilterNo_split (pivot : BitVec 32)
    (la : List (BitVec 32)) (r : Nat)
    (_hle : r + 1 ≤ la.length) :
    (la.filter (fun y => !(y.slt pivot))).length =
      (((la.take (r + 1)).filter (fun y => !(y.slt pivot))).length +
        ((la.drop (r + 1)).filter (fun y => !(y.slt pivot))).length) := by
  have h : la.take (r + 1) ++ la.drop (r + 1) = la :=
    List.take_append_drop (r + 1) la
  have hfilter : (((la.take (r + 1) ++ la.drop (r + 1)).filter
      (fun y => !(y.slt pivot)))).length =
      (((la.take (r + 1)).filter
        (fun y => !(y.slt pivot)))).length +
        (((la.drop (r + 1)).filter
          (fun y => !(y.slt pivot)))).length := by
    rw [List.filter_append, List.length_append]
  rwa [h] at hfilter

/-- One body iteration (value level), keeper branch: the `slt`
    test fires, the `yes` guard holds, the keeper stores at
    `wYes`, both the read cursor and `wYes` advance (`wNo`
    and the `no` record thread untouched). -/
theorem valPartitionCopyBody_yes (prog : Prog) (F : Nat)
    (ρ : Env) (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (y wOld : BitVec 32)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (_hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hkeep : (y.slt pivot) = true)
    (hwget : yes[wYes]? = some wOld) :
    ∃ ρ', evalProgStmt prog F vecPartitionCopyBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "yes" = some (.stdVecVal (yes.set wYes y)) ∧
      envLookup ρ' "no" = some (.stdVecVal no) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wYesB', envLookup ρ' "wYes" = some (.u64 wYesB') ∧
        wYesB'.toNat = wYes + 1) ∧
      (∃ wNoB', envLookup ρ' "wNo" = some (.u64 wNoB') ∧
        wNoB'.toNat = wNo) := by
  have hwYesLt : wYes < yes.length :=
    transformRead_lt yes wYes wOld hwget
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwYesVar : evalExpr (.var "wYes") ρ = .ok (.u64 wYesB) :=
    evalExpr_var_hit _ _ _ hwYes
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : yes[wYesB.toNat]? = some wOld := by
    rw [hwYesN]; exact hwget
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hsltV : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hatR hpivVar
    rwa [hkeep] at h
  have hlenN : (BitVec.ofNat 64 yes.length).toNat = yes.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hyes64
  have hguardT : evalExpr
      (.ult (.var "wYes") (.stdVecLen "yes")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "wYes") (.stdVecLen "yes") ρ
      wYesB (BitVec.ofNat 64 yes.length) hwYesVar
      (evalExpr_stdVecLen_some _ _ _ hyes)
    have htb : (wYesB.ult (BitVec.ofNat 64 yes.length)) = true := by
      rw [BitVec.ult_eq_decide, hwYesN, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hsetB : yes.set wYesB.toNat y = yes.set wYes y := by rw [hwYesN]
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "yes"
    (.stdVecVal yes) (.stdVecVal (yes.set wYesB.toNat y)) hyes
  have hstep_set := revVecSet prog F "yes" (.var "wYes")
    (.stdVecAt "a" (.var "r")) ρ wYesB y yes wOld ρ₁ hwYesVar hatR
    hyes hgetW hu₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "yes" _ ρ₁
      (show ("a" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact ha
  have hno₁ : envLookup ρ₁ "no" = some (.stdVecVal no) := by
    have h := envLookup_update_miss ρ "no" "yes" _ ρ₁
      (show ("no" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hno
  have hpiv₁ : envLookup ρ₁ "pivot" = some (.i32 pivot) := by
    have h := envLookup_update_miss ρ "pivot" "yes" _ ρ₁
      (show ("pivot" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hpiv
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "yes" _ ρ₁
      (show ("r" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hr
  have hwNo₁ : envLookup ρ₁ "wNo" = some (.u64 wNoB) := by
    have h := envLookup_update_miss ρ "wNo" "yes" _ ρ₁
      (show ("wNo" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hwNo
  have hevW : evalExpr (.uadd (.var "wYes")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wYesB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("wYes" : String) ≠ "yes" by decide) hu₁]; exact hwYes))
      (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "wYes"
    (.u64 wYesB) (.u64 (wYesB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "yes" by decide) hu₁]; exact hwYes)
  have hstep_w := revAssign prog F "wYes"
    (.uadd (.var "wYes") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (wYesB + 1)) ρ₂ hevW hu₂
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (rB + 1)) := by
    have hr₂' : envLookup ρ₂ "r" = some (.u64 rB) := by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide) hu₂]
      exact hr₁
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr₂') (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) (by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide) hu₂]
      exact hr₁)
  have hstep_r := revAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂
    (.u64 (rB + 1)) ρ₃ hevR hu₃
  have hyes₃ : envLookup ρ₃ "yes" =
      some (.stdVecVal (yes.set wYes y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "wYes" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "wYes" by decide) hu₂]
    exact ha₁
  have hno₃ : envLookup ρ₃ "no" = some (.stdVecVal no) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "wYes" by decide) hu₂]
    exact hno₁
  have hpiv₃ : envLookup ρ₃ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "wYes" by decide) hu₂]
    exact hpiv₁
  have hwNo₃ : envLookup ρ₃ "wNo" = some (.u64 wNoB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "wYes" by decide) hu₂]
    exact hwNo₁
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwYesN' : (wYesB + 1).toNat = wYes + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwYesN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ₃ "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hwYes₂ : envLookup ρ₂ "wYes" = some (.u64 (wYesB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hwYes' : envLookup ρ₃ "wYes" = some (.u64 (wYesB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "r" by decide) hu₃]
    exact hwYes₂
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
        (.seq (.vecSet "yes" (.var "wYes")
                (.stdVecAt "a" (.var "r")))
          (.assign "wYes" (.uadd (.var "wYes")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ = .ok (ρ₂, .fellThrough) := by
    have hthen : evalProgStmt prog F
        (.seq (.vecSet "yes" (.var "wYes")
                (.stdVecAt "a" (.var "r")))
          (.assign "wYes" (.uadd (.var "wYes")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ = .ok (ρ₂, .fellThrough) := by
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
        hstep_w]
    exact (evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hthen
  have hif : evalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ = .ok (ρ₂, .fellThrough) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hsltV).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  refine ⟨ρ₃, ?_, ha₃, hyes₃, hno₃, hpiv₃, ⟨_, hr', hrN'⟩,
    ⟨_, hwYes', hwYesN'⟩, ⟨_, hwNo₃, hwNoN⟩⟩
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif, hstep_r]

/-- One body iteration (value level), dropper branch: the `slt`
    test fails, the `no` guard holds, the dropper stores at
    `wNo`, both the read cursor and `wNo` advance (`wYes`
    and the `yes` record thread untouched). -/
theorem valPartitionCopyBody_no (prog : Prog) (F : Nat)
    (ρ : Env) (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (y wOld : BitVec 32)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (_hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hdrop : (y.slt pivot) = false)
    (hwget : no[wNo]? = some wOld) :
    ∃ ρ', evalProgStmt prog F vecPartitionCopyBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "yes" = some (.stdVecVal yes) ∧
      envLookup ρ' "no" = some (.stdVecVal (no.set wNo y)) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wYesB', envLookup ρ' "wYes" = some (.u64 wYesB') ∧
        wYesB'.toNat = wYes) ∧
      (∃ wNoB', envLookup ρ' "wNo" = some (.u64 wNoB') ∧
        wNoB'.toNat = wNo + 1) := by
  have hwNoLt : wNo < no.length :=
    transformRead_lt no wNo wOld hwget
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwNoVar : evalExpr (.var "wNo") ρ = .ok (.u64 wNoB) :=
    evalExpr_var_hit _ _ _ hwNo
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : no[wNoB.toNat]? = some wOld := by
    rw [hwNoN]; exact hwget
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hsltF : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hatR hpivVar
    rwa [hdrop] at h
  have hlenN : (BitVec.ofNat 64 no.length).toNat = no.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hno64
  have hguardT : evalExpr
      (.ult (.var "wNo") (.stdVecLen "no")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "wNo") (.stdVecLen "no") ρ
      wNoB (BitVec.ofNat 64 no.length) hwNoVar
      (evalExpr_stdVecLen_some _ _ _ hno)
    have htb : (wNoB.ult (BitVec.ofNat 64 no.length)) = true := by
      rw [BitVec.ult_eq_decide, hwNoN, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hsetB : no.set wNoB.toNat y = no.set wNo y := by rw [hwNoN]
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "no"
    (.stdVecVal no) (.stdVecVal (no.set wNoB.toNat y)) hno
  have hstep_set := revVecSet prog F "no" (.var "wNo")
    (.stdVecAt "a" (.var "r")) ρ wNoB y no wOld ρ₁ hwNoVar hatR
    hno hgetW hu₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "no" _ ρ₁
      (show ("a" : String) ≠ "no" by decide) hu₁
    rw [h]; exact ha
  have hyes₁ : envLookup ρ₁ "yes" = some (.stdVecVal yes) := by
    have h := envLookup_update_miss ρ "yes" "no" _ ρ₁
      (show ("yes" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hyes
  have hpiv₁ : envLookup ρ₁ "pivot" = some (.i32 pivot) := by
    have h := envLookup_update_miss ρ "pivot" "no" _ ρ₁
      (show ("pivot" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hpiv
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "no" _ ρ₁
      (show ("r" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hr
  have hwYes₁ : envLookup ρ₁ "wYes" = some (.u64 wYesB) := by
    have h := envLookup_update_miss ρ "wYes" "no" _ ρ₁
      (show ("wYes" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hwYes
  have hevW : evalExpr (.uadd (.var "wNo")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wNoB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("wNo" : String) ≠ "no" by decide) hu₁]; exact hwNo))
      (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "wNo"
    (.u64 wNoB) (.u64 (wNoB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "no" by decide) hu₁]; exact hwNo)
  have hstep_w := revAssign prog F "wNo"
    (.uadd (.var "wNo") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (wNoB + 1)) ρ₂ hevW hu₂
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (rB + 1)) := by
    have hr₂' : envLookup ρ₂ "r" = some (.u64 rB) := by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide) hu₂]
      exact hr₁
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr₂') (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) (by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide) hu₂]
      exact hr₁)
  have hstep_r := revAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂
    (.u64 (rB + 1)) ρ₃ hevR hu₃
  have hno₃ : envLookup ρ₃ "no" =
      some (.stdVecVal (no.set wNo y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "wNo" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "wNo" by decide) hu₂]
    exact ha₁
  have hyes₃ : envLookup ρ₃ "yes" = some (.stdVecVal yes) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "wNo" by decide) hu₂]
    exact hyes₁
  have hpiv₃ : envLookup ρ₃ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "wNo" by decide) hu₂]
    exact hpiv₁
  have hwYes₃ : envLookup ρ₃ "wYes" = some (.u64 wYesB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "wNo" by decide) hu₂]
    exact hwYes₁
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwNoN' : (wNoB + 1).toNat = wNo + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwNoN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ₃ "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hwNo₂ : envLookup ρ₂ "wNo" = some (.u64 (wNoB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hwNo' : envLookup ρ₃ "wNo" = some (.u64 (wNoB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "r" by decide) hu₃]
    exact hwNo₂
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
        (.seq (.vecSet "no" (.var "wNo")
                (.stdVecAt "a" (.var "r")))
          (.assign "wNo" (.uadd (.var "wNo")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ = .ok (ρ₂, .fellThrough) := by
    have hthen : evalProgStmt prog F
        (.seq (.vecSet "no" (.var "wNo")
                (.stdVecAt "a" (.var "r")))
          (.assign "wNo" (.uadd (.var "wNo")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ = .ok (ρ₂, .fellThrough) := by
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
        hstep_w]
    exact (evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hthen
  have hif : evalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ = .ok (ρ₂, .fellThrough) :=
    (evalProgStmt_if_false _ _ _ _ _ _ hsltF).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  refine ⟨ρ₃, ?_, ha₃, hyes₃, hno₃, hpiv₃, ⟨_, hr', hrN'⟩,
    ⟨_, hwYes₃, hwYesN⟩, ⟨_, hwNo', hwNoN'⟩⟩
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hif, hstep_r]

/-- One body iteration (value level), short-`yes` branch: the
    `slt` test fires but `wYes` is past the record, so the
    inner guard fails and the loud `.fail` leg fires. -/
theorem valPartitionCopyBody_shortYes (prog : Prog) (F : Nat)
    (ρ : Env) (la yes : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes : Nat) (rB wYesB : BitVec 64) (y : BitVec 32)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hyes64 : yes.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (_hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hkeep : (y.slt pivot) = true)
    (hmiss : yes[wYes]? = none) :
    evalProgStmt prog F vecPartitionCopyBody ρ = .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwYesVar : evalExpr (.var "wYes") ρ = .ok (.u64 wYesB) :=
    evalExpr_var_hit _ _ _ hwYes
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hsltV : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hatR hpivVar
    rwa [hkeep] at h
  have hnl : ¬ wYes < yes.length := by
    intro h
    have hsome : yes[wYes]? = some yes[wYes] :=
      List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 yes.length).toNat = yes.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hyes64
  have hguardF : evalExpr
      (.ult (.var "wYes") (.stdVecLen "yes")) ρ =
      .ok (.b false) := by
    have hult := evalExpr_ult_u64 (.var "wYes") (.stdVecLen "yes") ρ
      wYesB (BitVec.ofNat 64 yes.length) hwYesVar
      (evalExpr_stdVecLen_some _ _ _ hyes)
    have hfb : (wYesB.ult (BitVec.ofNat 64 yes.length)) = false := by
      rw [BitVec.ult_eq_decide, hwYesN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hfail : evalProgStmt prog F .fail ρ = .error .AssertFail := by
    simpa [evalProgStmt] using (evalStmtFuel_fail F ρ)
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
        (.seq (.vecSet "yes" (.var "wYes")
                (.stdVecAt "a" (.var "r")))
          (.assign "wYes" (.uadd (.var "wYes")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ = .error .AssertFail :=
    (evalProgStmt_if_false _ _ _ _ _ _ hguardF).trans hfail
  have hif : evalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ = .error .AssertFail :=
    (evalProgStmt_if_true _ _ _ _ _ _ hsltV).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  exact evalProgStmt_seq_err _ _ _ _ _ _ hif

/-- One body iteration (value level), short-`no` branch: the
    `slt` test fails but `wNo` is past the record, so the
    inner guard fails and the loud `.fail` leg fires. -/
theorem valPartitionCopyBody_shortNo (prog : Prog) (F : Nat)
    (ρ : Env) (la no : List (BitVec 32)) (pivot : BitVec 32)
    (r wNo : Nat) (rB wNoB : BitVec 64) (y : BitVec 32)
    (hrN : rB.toNat = r) (hwNoN : wNoB.toNat = wNo)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (_hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hdrop : (y.slt pivot) = false)
    (hmiss : no[wNo]? = none) :
    evalProgStmt prog F vecPartitionCopyBody ρ = .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwNoVar : evalExpr (.var "wNo") ρ = .ok (.u64 wNoB) :=
    evalExpr_var_hit _ _ _ hwNo
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hatR : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hsltF : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hatR hpivVar
    rwa [hdrop] at h
  have hnl : ¬ wNo < no.length := by
    intro h
    have hsome : no[wNo]? = some no[wNo] :=
      List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 no.length).toNat = no.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hno64
  have hguardF : evalExpr
      (.ult (.var "wNo") (.stdVecLen "no")) ρ =
      .ok (.b false) := by
    have hult := evalExpr_ult_u64 (.var "wNo") (.stdVecLen "no") ρ
      wNoB (BitVec.ofNat 64 no.length) hwNoVar
      (evalExpr_stdVecLen_some _ _ _ hno)
    have hfb : (wNoB.ult (BitVec.ofNat 64 no.length)) = false := by
      rw [BitVec.ult_eq_decide, hwNoN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hfail : evalProgStmt prog F .fail ρ = .error .AssertFail := by
    simpa [evalProgStmt] using (evalStmtFuel_fail F ρ)
  have hinner : evalProgStmt prog F
      (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
        (.seq (.vecSet "no" (.var "wNo")
                (.stdVecAt "a" (.var "r")))
          (.assign "wNo" (.uadd (.var "wNo")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ = .error .AssertFail :=
    (evalProgStmt_if_false _ _ _ _ _ _ hguardF).trans hfail
  have hif : evalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ = .error .AssertFail :=
    (evalProgStmt_if_false _ _ _ _ _ _ hsltF).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  exact evalProgStmt_seq_err _ _ _ _ _ _ hif

/-! ## Value loop (bridges `evalProgStmt` to `partitionCopyFwd`) -/

/-- Loop bridge (value level), ok leg: the keeper/dropper
    counts and both record bounds thread through the loop to
    the forward model. -/
theorem valPartitionCopyLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (yes' no' : List (BitVec 32)) (r' wYes' wNo' : Nat)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length ≤ no.length)
    (hfwd : partitionCopyFwd pivot la yes no G r wYes wNo =
      .ok (r', wYes', wNo', yes', no')) :
    ∃ ρ', evalProgStmt prog F vecPartitionCopyLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "yes" = some (.stdVecVal yes') ∧
      envLookup ρ' "no" = some (.stdVecVal no') ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wYesB', envLookup ρ' "wYes" = some (.u64 wYesB') ∧
        wYesB'.toNat = wYes') ∧
      (∃ wNoB', envLookup ρ' "wNo" = some (.u64 wNoB') ∧
        wNoB'.toNat = wNo') := by
  induction F generalizing G ρ yes no r wYes wNo
    rB wYesB wNoB with
  | zero =>
    have him : r = la.length := by omega
    have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hguardF : evalExpr
        (.ult (.var "r") (.stdVecLen "a")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
        (BitVec.ofNat 64 la.length)
        (evalExpr_var_hit _ _ _ hr)
        (evalExpr_stdVecLen_some _ _ _ ha)
      have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt prog 0 vecPartitionCopyLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (r, wYes, wNo, yes, no) =
        (r', wYes', wNo', yes', no') := by
      cases G with
      | zero => simpa [partitionCopyFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < la.length := by omega
        simpa [partitionCopyFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hyes, hno, hpiv, ⟨rB, hr, hrN⟩,
      ⟨wYesB, hwYes, hwYesN⟩, ⟨wNoB, hwNo, hwNoN⟩⟩
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardT : evalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide, hrN, hlenN]
          exact decide_eq_true hlt
        rwa [htb] at hult
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y.slt pivot) = true
      · by_cases hmiss : yes[wYes]? = none
        · have hcon := hfwd
          simp only [partitionCopyFwd, dite_eq_left hlt, hy, hkeep,
            hmiss] at hcon
          exact absurd hcon (by simp)
        · have hsome : ∃ z, yes[wYes]? = some z := by
            match h : yes[wYes]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hstepY :=
            partFilterYes_take_succ pivot la r y hy hkeep
          have hlenY := congrArg List.length hstepY
          rw [List.length_append, hwcntYes,
            List.length_singleton] at hlenY
          have hwlt : wYes < yes.length := by
            have hsplit := partFilterYes_split pivot la r
              (by omega)
            omega
          have htake_set : (yes.set wYes y).take (wYes + 1)
              = (yes.take wYes) ++ [y] :=
            take_set_succ_self yes wYes y hwlt
          have hwcntYes' := hlenY
          have hdropNo : (!(y.slt pivot)) = false := by
            simp [hkeep]
          have hstepNo :=
            partFilterNo_take_succ_drop pivot la r y hy hdropNo
          have hwcntNo' := congrArg List.length hstepNo
          rw [hwcntNo] at hwcntNo'
          have hlenS : (yes.set wYes y).length = yes.length := by
            simp [List.length_set]
          have hcapYes' : (la.filter
              (fun y => y.slt pivot)).length ≤
              (yes.set wYes y).length := by
            rw [hlenS]; exact hcapYes
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la (yes.set wYes y)
              no G' (r + 1) (wYes + 1) wNo =
              .ok (r', wYes', wNo', yes', no') := by
            have h := hfwd
            simp only [partitionCopyFwd, dite_eq_left hlt, hy,
              hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩⟩ :=
            valPartitionCopyBody_yes prog F ρ la yes no pivot
              r wYes wNo rB wYesB wNoB y wOld
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hkeep hwget
          obtain ⟨ρ', hloop, ha', hyes', hno', hpiv',
              ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
              ⟨wNoB', hwNoB', hwNoN'⟩⟩ :=
            ih (G := G') (ρ := ρ₁) (yes := yes.set wYes y)
              (no := no) (r := r + 1) (wYes := wYes + 1)
              (wNo := wNo) (rB := rB₁) (wYesB := wYesB₁)
              (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := by rw [hlenS]; exact hyes64)
              (hno64 := hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hcapYes := hcapYes') (hcapNo := hcapNo)
              (hfwd := hfwd')
          refine ⟨ρ', ?_, ha', hyes', hno', hpiv',
            ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
            ⟨wNoB', hwNoB', hwNoN'⟩⟩
          have hwhile : evalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ =
              evalProgStmt prog F vecPartitionCopyLoop ρ₁ := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
          rw [hwhile]
          exact hloop
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        have hkeepNo : (!(y.slt pivot)) = true := by simp [hdrop]
        by_cases hmiss : no[wNo]? = none
        · have hcon := hfwd
          simp only [partitionCopyFwd, dite_eq_left hlt, hy, hdrop,
            hmiss] at hcon
          exact absurd hcon (by simp)
        · have hsome : ∃ z, no[wNo]? = some z := by
            match h : no[wNo]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hstepN :=
            partFilterNo_take_succ pivot la r y hy hkeepNo
          have hlenN := congrArg List.length hstepN
          rw [List.length_append, hwcntNo,
            List.length_singleton] at hlenN
          have hwlt : wNo < no.length := by
            have hsplit := partFilterNo_split pivot la r
              (by omega)
            omega
          have hwcntNo' := hlenN
          have hstepYd :=
            partFilterYes_take_succ_drop pivot la r y hy hdrop
          have hwcntYes' := congrArg List.length hstepYd
          rw [hwcntYes] at hwcntYes'
          have hlenS : (no.set wNo y).length = no.length := by
            simp [List.length_set]
          have hcapNo' : (la.filter
              (fun y => !(y.slt pivot))).length ≤
              (no.set wNo y).length := by
            rw [hlenS]; exact hcapNo
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la yes
              (no.set wNo y) G' (r + 1) wYes (wNo + 1) =
              .ok (r', wYes', wNo', yes', no') := by
            have h := hfwd
            simp only [partitionCopyFwd, dite_eq_left hlt, hy,
              hdrop, hwget] at h
            exact h
          obtain ⟨ρ₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩⟩ :=
            valPartitionCopyBody_no prog F ρ la yes no pivot
              r wYes wNo rB wYesB wNoB y wOld
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hdrop hwget
          obtain ⟨ρ', hloop, ha', hyes', hno', hpiv',
              ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
              ⟨wNoB', hwNoB', hwNoN'⟩⟩ :=
            ih (G := G') (ρ := ρ₁) (yes := yes)
              (no := no.set wNo y) (r := r + 1) (wYes := wYes)
              (wNo := wNo + 1) (rB := rB₁) (wYesB := wYesB₁)
              (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := hyes64)
              (hno64 := by rw [hlenS]; exact hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hcapYes := hcapYes) (hcapNo := hcapNo')
              (hfwd := hfwd')
          refine ⟨ρ', ?_, ha', hyes', hno', hpiv',
            ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
            ⟨wNoB', hwNoB', hwNoN'⟩⟩
          have hwhile : evalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ =
              evalProgStmt prog F vecPartitionCopyLoop ρ₁ := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
          rw [hwhile]
          exact hloop
    · have him : r = la.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardF : evalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt prog (F + 1) vecPartitionCopyLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (la.length, wYes, wNo, yes, no) =
          (r', wYes', wNo', yes', no') := by
        cases G with
        | zero => simpa [partitionCopyFwd] using hfwd
        | succ G =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [partitionCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hyes, hno, hpiv, ⟨rB, hr, hrN⟩,
        ⟨wYesB, hwYes, hwYesN⟩, ⟨wNoB, hwNo, hwNoN⟩⟩

/-- Loop bridge (value level), error leg: a short record on
    either side fails loud at the first overflowing store. -/
theorem valPartitionCopyLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hfwd : partitionCopyFwd pivot la yes no G r wYes wNo =
      .error .AssertFail) :
    evalProgStmt prog F vecPartitionCopyLoop ρ = .error .AssertFail := by
  induction F generalizing G ρ yes no r wYes wNo
    rB wYesB wNoB with
  | zero =>
    have him : r = la.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [partitionCopyFwd])
    | succ _ =>
      have hneg : ¬ la.length < la.length := by omega
      have hcon := hfwd
      simp only [partitionCopyFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardT : evalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide, hrN, hlenN]
          exact decide_eq_true hlt
        rwa [htb] at hult
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y.slt pivot) = true
      · by_cases hmiss : yes[wYes]? = none
        · have hshort := valPartitionCopyBody_shortYes prog F ρ
            la yes pivot r wYes rB wYesB y hrN hwYesN hyes64
            ha hyes hpiv hr hwYes hlt hy hkeep hmiss
          have hwhile : evalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ = .error .AssertFail := by
            have hloop : vecPartitionCopyLoop =
                (.while_ (.ult (.var "r") (.stdVecLen "a"))
                  vecPartitionCopyBody) := rfl
            rw [hloop, evalProgStmt_while_true prog F _ _ _
              hguardT, hshort]
          exact hwhile
        · have hsome : ∃ z, yes[wYes]? = some z := by
            match h : yes[wYes]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hstepY :=
            partFilterYes_take_succ pivot la r y hy hkeep
          have hlenY := congrArg List.length hstepY
          rw [List.length_append, hwcntYes,
            List.length_singleton] at hlenY
          have hwcntYes' := hlenY
          have hdropNo : (!(y.slt pivot)) = false := by
            simp [hkeep]
          have hstepNo :=
            partFilterNo_take_succ_drop pivot la r y hy hdropNo
          have hwcntNo' := congrArg List.length hstepNo
          rw [hwcntNo] at hwcntNo'
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la (yes.set wYes y)
              no G' (r + 1) (wYes + 1) wNo = .error .AssertFail := by
            have h := hfwd
            simp only [partitionCopyFwd, dite_eq_left hlt, hy,
              hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩⟩ :=
            valPartitionCopyBody_yes prog F ρ la yes no pivot
              r wYes wNo rB wYesB wNoB y wOld
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hkeep hwget
          have hloop : evalProgStmt prog F vecPartitionCopyLoop ρ₁ =
              .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (yes := yes.set wYes y)
              (no := no) (r := r + 1) (wYes := wYes + 1)
              (wNo := wNo) (rB := rB₁) (wYesB := wYesB₁)
              (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := by simpa [List.length_set] using hyes64)
              (hno64 := hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hfwd := hfwd')
          have hwhile : evalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ = .error .AssertFail := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
            exact hloop
          exact hwhile
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        by_cases hmiss : no[wNo]? = none
        · have hshort := valPartitionCopyBody_shortNo prog F ρ
            la no pivot r wNo rB wNoB y hrN hwNoN hno64
            ha hno hpiv hr hwNo hlt hy hdrop hmiss
          have hwhile : evalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ = .error .AssertFail := by
            have hloop : vecPartitionCopyLoop =
                (.while_ (.ult (.var "r") (.stdVecLen "a"))
                  vecPartitionCopyBody) := rfl
            rw [hloop, evalProgStmt_while_true prog F _ _ _
              hguardT, hshort]
          exact hwhile
        · have hsome : ∃ z, no[wNo]? = some z := by
            match h : no[wNo]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hstepN :=
            partFilterNo_take_succ pivot la r y hy
              (by simp [hdrop])
          have hlenN := congrArg List.length hstepN
          rw [List.length_append, hwcntNo,
            List.length_singleton] at hlenN
          have hwcntNo' := hlenN
          have hstepYd :=
            partFilterYes_take_succ_drop pivot la r y hy hdrop
          have hwcntYes' := congrArg List.length hstepYd
          rw [hwcntYes] at hwcntYes'
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la yes
              (no.set wNo y) G' (r + 1) wYes (wNo + 1) =
              .error .AssertFail := by
            have h := hfwd
            simp only [partitionCopyFwd, dite_eq_left hlt, hy,
              hdrop, hwget] at h
            exact h
          obtain ⟨ρ₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩⟩ :=
            valPartitionCopyBody_no prog F ρ la yes no pivot
              r wYes wNo rB wYesB wNoB y wOld
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hdrop hwget
          have hloop : evalProgStmt prog F vecPartitionCopyLoop ρ₁ =
              .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (yes := yes)
              (no := no.set wNo y) (r := r + 1) (wYes := wYes)
              (wNo := wNo + 1) (rB := rB₁) (wYesB := wYesB₁)
              (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := hyes64)
              (hno64 := by simpa [List.length_set] using hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hfwd := hfwd')
          have hwhile : evalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ = .error .AssertFail := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
            exact hloop
          exact hwhile
    · have him : r = la.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [partitionCopyFwd])
      | succ _ =>
        have hneg : ¬ la.length < la.length := by omega
        have hcon := hfwd
        simp only [partitionCopyFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)

/-! ## Value entries (the three lets, the loop, the return) -/

/-- Value entry, nil leg: the empty input binds the three
    zeroed cursors, the loop exits at once, the return is
    `0`. -/
theorem evalProgFunc_vecPartitionCopy_nil (F : Nat)
    (yes no : List (BitVec 32)) (pivot : BitVec 32)
    (hyes64 : yes.length < 2 ^ 64) (hno64 : no.length < 2 ^ 64) :
    evalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal yes, .stdVecVal no, .i32 pivot] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind : bindArgs vecPartitionCopyFunc.args
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal yes, .stdVecVal no, .i32 pivot] =
      some [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)] := rfl
  have hbody : vecPartitionCopyFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "wYes" (.u 64)
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "wNo" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecPartitionCopyLoop
              (.return_ (.var "wYes")))))) := rfl
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := revLet vecPartitionCopyProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("yes", .stdVecVal yes), ("no", .stdVecVal no),
      ("pivot", .i32 pivot)]
    (.u64 (BitVec.ofNat 64 0)) hlit
  have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := revLet vecPartitionCopyProg F "wYes" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal ([] : List (BitVec 32))),
      ("yes", .stdVecVal yes), ("no", .stdVecVal no),
      ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitW
  have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend
        [("a", .stdVecVal ([] : List (BitVec 32))),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletN := revLet vecPartitionCopyProg F "wNo" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitN
  have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
  have haN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal ([] : List (BitVec 32))) := by
    rw [envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "r" by decide)]
    simp [envLookup]
  have hyesN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "yes" =
      some (.stdVecVal yes) := by
    rw [envExtend_miss _ _ _ _
      (show ("yes" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("yes" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("yes" : String) ≠ "r" by decide)]
    simp [envLookup, show ("yes" : String) ≠ "a" by decide]
  have hnoN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "no" =
      some (.stdVecVal no) := by
    rw [envExtend_miss _ _ _ _
      (show ("no" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("no" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("no" : String) ≠ "r" by decide)]
    simp [envLookup, show ("no" : String) ≠ "a" by decide]
  have hpivN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "pivot" =
      some (.i32 pivot) := by
    rw [envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "r" by decide)]
    simp [envLookup, show ("pivot" : String) ≠ "a" by decide]
  have hrN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("r" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("r" : String) ≠ "wYes" by decide)]
    exact envExtend_hit _ _ _
  have hwYesN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "wYes" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("wYes" : String) ≠ "wNo" by decide)]
    exact envExtend_hit _ _ _
  have hwNoN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "wNo" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', hloop, -, -, -, -,
      ⟨rB', -, -⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
      ⟨wNoB', -, -⟩⟩ :=
    valPartitionCopyLoop_ok vecPartitionCopyProg F 0
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal ([] : List (BitVec 32))),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0)))
      ([] : List (BitVec 32)) yes no pivot 0 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      yes no 0 0 0 hw0N hw0N hw0N (by simp) hyes64 hno64
      haN hyesN hnoN hpivN hrN hwYesN hwNoN
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      (fun p hp => absurd hp (Nat.not_lt_zero p))
      (by simp) (by simp) (by simp) (by simp) rfl
  have hwEq : wYesB' = BitVec.ofNat 64 0 :=
    BitVec.eq_of_toNat_eq (by rw [hwYesN']; simp)
  have hevW : evalExpr (.var "wYes") ρ' =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    rw [← hwEq]; exact evalExpr_var_hit _ _ _ hwYesB'
  have hret := evalProgStmt_return vecPartitionCopyProg F
    (.var "wYes") ρ'
    (.u64 (BitVec.ofNat 64 0)) hevW
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletN,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]

/-- Value entry, ok leg: a nonempty input with fitting
    records binds the prelude, runs the loop, and returns the
    keeper count. -/
theorem evalProgFunc_vecPartitionCopy_ok (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (wYes' wNo' : Nat) (yes' no' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hle : 1 ≤ la.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length
      ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no.length)
    (hfwd : partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .ok (la.length, wYes', wNo', yes', no'))
    (hwlen : wYes' = (la.filter (fun y => y.slt pivot)).length) :
    evalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      .ok (.u64 (BitVec.ofNat 64 wYes')) := by
  have hbind : bindArgs vecPartitionCopyFunc.args
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      some [("a", .stdVecVal la), ("yes", .stdVecVal yes),
        ("no", .stdVecVal no), ("pivot", .i32 pivot)] := rfl
  have hbody : vecPartitionCopyFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "wYes" (.u 64)
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "wNo" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecPartitionCopyLoop
              (.return_ (.var "wYes")))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at hle
  | cons b0 ys =>
    subst hla
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletR := revLet vecPartitionCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
        ("no", .stdVecVal no), ("pivot", .i32 pivot)]
      (.u64 (BitVec.ofNat 64 0)) hlitR
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hletW := revLet vecPartitionCopyProg F "wYes" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal (b0 :: ys)),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
      (.u64 (BitVec.ofNat 64 0)) hlitW
    have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletN := revLet vecPartitionCopyProg F "wNo" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
      (.u64 (BitVec.ofNat 64 0)) hlitN
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have haA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal (b0 :: ys)) := by
      rw [        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide)]
      simp [envLookup]
    have hyesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "yes" =
      some (.stdVecVal yes) := by
      rw [envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "r" by decide)]
      simp [envLookup, show ("yes" : String) ≠ "a" by decide]
    have hnoA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "no" =
      some (.stdVecVal no) := by
      rw [envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "r" by decide)]
      simp [envLookup, show ("no" : String) ≠ "a" by decide,
        show ("no" : String) ≠ "yes" by decide]
    have hpivA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "pivot" =
      some (.i32 pivot) := by
      rw [envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "r" by decide)]
      simp [envLookup, show ("pivot" : String) ≠ "a" by decide,
        show ("pivot" : String) ≠ "yes" by decide,
        show ("pivot" : String) ≠ "no" by decide]
    have hrA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide)]
      exact envExtend_hit _ _ _
    have hwYesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "wYes" =
      some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("wYes" : String) ≠ "wNo" by decide)]
      exact envExtend_hit _ _ _
    have hwNoA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "wNo" =
      some (.u64 (BitVec.ofNat 64 0)) :=
      envExtend_hit _ _ _

    obtain ⟨ρ', hloop, ha', hyes', hno', hpiv',
        ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
        ⟨wNoB', hwNoB', hwNoN'⟩⟩ :=
      valPartitionCopyLoop_ok vecPartitionCopyProg F
        ((b0 :: ys).length)
        (envExtend (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0)))
          "wNo" (.u64 (BitVec.ofNat 64 0)))
        (b0 :: ys) yes no pivot 0 0 0
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0)
        yes' no' ((b0 :: ys).length) wYes' wNo'
        hw0N hw0N hw0N hla64 hyes64 hno64
        haA hyesA hnoA hpivA hrA hwYesA hwNoA
        (by omega) hF (Nat.le_refl _)
        hread (by simp) (by simp) hcapYes hcapNo hfwd
    have hwEq : wYesB' = BitVec.ofNat 64 wYes' := by
      apply BitVec.eq_of_toNat_eq
      rw [hwYesN', hwlen, BitVec.toNat_ofNat]
      have hlen : ((b0 :: ys).filter (fun y => y.slt pivot)).length
          < 2 ^ 64 := by omega
      exact (Nat.mod_eq_of_lt hlen).symm
    have hevW' : evalExpr (.var "wYes") ρ' =
        .ok (.u64 (BitVec.ofNat 64 wYes')) := by
      rw [← hwEq]; exact evalExpr_var_hit _ _ _ hwYesB'
    have hret := evalProgStmt_return vecPartitionCopyProg F
      (.var "wYes") ρ' (.u64 (BitVec.ofNat 64 wYes')) hevW'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletN,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
      hret]

/-- Value entry, err leg: a nonempty input with a short
    record on either side binds the prelude, then the loop
    fails loud (the `return` is unreachable). -/
theorem evalProgFunc_vecPartitionCopy_err (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : yes.length < (la.filter (fun y => y.slt pivot)).length ∨
      no.length < (la.filter (fun y => !(y.slt pivot))).length)
    (hfwd : partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .error .AssertFail) :
    evalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      .error .AssertFail := by
  have hbind : bindArgs vecPartitionCopyFunc.args
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      some [("a", .stdVecVal la), ("yes", .stdVecVal yes),
        ("no", .stdVecVal no), ("pivot", .i32 pivot)] := rfl
  have hbody : vecPartitionCopyFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "wYes" (.u 64)
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "wNo" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecPartitionCopyLoop
              (.return_ (.var "wYes")))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at hmore
  | cons b0 ys =>
    subst hla
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletR := revLet vecPartitionCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
        ("no", .stdVecVal no), ("pivot", .i32 pivot)]
      (.u64 (BitVec.ofNat 64 0)) hlitR
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hletW := revLet vecPartitionCopyProg F "wYes" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal (b0 :: ys)),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
      (.u64 (BitVec.ofNat 64 0)) hlitW
    have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletN := revLet vecPartitionCopyProg F "wNo" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
      (.u64 (BitVec.ofNat 64 0)) hlitN
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have heA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide)]
      simp [envLookup]
    have heYesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "yes" =
        some (.stdVecVal yes) := by
      rw [envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "r" by decide)]
      simp [envLookup, show ("yes" : String) ≠ "a" by decide]
    have heNoA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "no" =
        some (.stdVecVal no) := by
      rw [envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "r" by decide)]
      simp [envLookup, show ("no" : String) ≠ "a" by decide]
    have hepivA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "pivot" =
        some (.i32 pivot) := by
      rw [envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "r" by decide)]
      simp [envLookup, show ("pivot" : String) ≠ "a" by decide]
    have herA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "r" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide)]
      exact envExtend_hit _ _ _
    have hewYesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "wYes" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("wYes" : String) ≠ "wNo" by decide)]
      exact envExtend_hit _ _ _
    have hewNoA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "wNo" =
        some (.u64 (BitVec.ofNat 64 0)) :=
      envExtend_hit _ _ _
    have hloop : evalProgStmt vecPartitionCopyProg F
        vecPartitionCopyLoop
        (envExtend (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0)))
          "wNo" (.u64 (BitVec.ofNat 64 0))) =
        .error .AssertFail := by
      exact valPartitionCopyLoop_err vecPartitionCopyProg F
          ((b0 :: ys).length)
          (envExtend (envExtend (envExtend
            [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
              ("no", .stdVecVal no), ("pivot", .i32 pivot)]
            "r" (.u64 (BitVec.ofNat 64 0)))
            "wYes" (.u64 (BitVec.ofNat 64 0)))
            "wNo" (.u64 (BitVec.ofNat 64 0)))
          (b0 :: ys) yes no pivot 0 0 0
          (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
          (BitVec.ofNat 64 0)
          hw0N hw0N hw0N hla64 hyes64 hno64
          heA
          heYesA
          heNoA
          hepivA
          herA
          hewYesA
          (envExtend_hit _ _ _)
          (by omega) hF (Nat.le_refl _)
          hread (by simp) (by simp) hfwd
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletN,
      evalProgStmt_seq_err _ _ _ _ _ _ hloop]
