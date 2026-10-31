/-
Circe.Emit.VecRotate — R1 `std::vector<int32_t>` in-place left
rotation by `k` via three segment reversals (triple
entry-over-entry composition, no loop): `seg(v, 0, k)`,
`seg(v, k, n)`, `seg(v, 0, n)` over the frozen `size` leaf and the
admitted `vec_seg_reverse` entry.

The composer threads the words by `var` rebinding (`callProg`
returns the callee's words, the merge-sort precedent): `m ←
size(v)`, `z ← 0` (call args are vars, so the literal zero is
`let`-bound, the R-prelude precedent), three `callProg`s into
`vecSegReverseFunc`, return of the rotated words (the C++ `void`
functionalizes as words threading, the `vecAtSet` precedent).
Caller debt: `k ≤ length` (out-of-range is a loud `AssertFail`
leg inside the callee, unreachable under the contract).
-/
import Circe.Emit.VecSegReverse

/-! ## R1: rotate entry -/

/-- Mangled entry name in `tests/cpp/vec_rotate.cpp`. -/
def vecRotateName : String := "_Z10vec_rotateRSt6vectorIiSaIiEEm"

/-- Whole function: `m ← size(v)`, `z ← 0`, three window reversals
    (`[0, k)`, `[k, n)`, `[0, n)` — left rotation by `k`), return
    of the rotated words. -/
def vecRotateFunc : Func :=
  ⟨vecRotateName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "k", ty := .u 64, role := .owned }],
   stdVecObjTy,
   (.seq (.callRet "m" stdVecSizeName ["v"])
     (.seq (.let_ "z" (.u 64) (.lit (.u64 0)))
       (.seq (.callProg "v" vecSegReverseName ["v", "z", "k"])
         (.seq (.callProg "v" vecSegReverseName ["v", "k", "m"])
           (.seq (.callProg "v" vecSegReverseName ["v", "z", "m"])
             (.return_ (.var "v")))))))⟩

/-- Value-level forward for `vec_rotate`: left rotation under
    caller debt, loud `AssertFail` otherwise (the callee fails
    loudly past the end, so evaluation agrees). -/
def vecRotateFwd (l : List (BitVec 32)) (k : BitVec 64) :
    Result Value :=
  if k.toNat ≤ l.length then
    .ok (.stdVecVal ((l.drop k.toNat) ++ l.take k.toNat))
  else .error .AssertFail

/-- Program over which the entry evaluates (the admitted segment
    entry head, then the frozen leaves its body resolves). -/
abbrev vecRotateProg : Prog :=
  [vecSegReverseFunc, stdVecSizeFunc,
    { stdVecAtFunc with name := stdVecAtMutName },
    stdVecIndexFunc, stdVecRangeCheckFunc]

/-! ## R2: callee resolution + rotation identity -/

/-- `findFunc` resolves the admitted segment entry (program head). -/
theorem rotFindSeg :
    findFunc vecRotateProg vecSegReverseName = some vecSegReverseFunc := by
  show findFunc (vecSegReverseFunc :: _) _ = _
  exact findFunc_hit _ _

/-- `findFunc` resolves `size` (after the segment head). -/
theorem rotFindSize :
    findFunc vecRotateProg stdVecSizeName = some stdVecSizeFunc := by
  have hmiss : (vecSegReverseFunc.name == stdVecSizeName) = false := by rfl
  show findFunc (vecSegReverseFunc :: _) _ = _
  rw [findFunc_miss _ _ _ hmiss]
  exact findFunc_hit _ _

/-- `findFunc` resolves the renamed `at()` leaf (after the segment
    and `size` heads). -/
theorem rotFindAt :
    findFunc vecRotateProg stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName } := by
  have hmiss1 : (vecSegReverseFunc.name == stdVecAtMutName) = false := by
    rfl
  have hmiss2 : (stdVecSizeFunc.name == stdVecAtMutName) = false := by
    rfl
  show findFunc (vecSegReverseFunc :: _) _ = _
  rw [findFunc_miss _ _ _ hmiss1, findFunc_miss _ _ _ hmiss2]
  exact findFunc_hit _ _

/-- Window reversal preserves length. -/
theorem segReverseWindow_length (l : List (BitVec 32)) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ l.length) :
    (segReverseWindow l lo hi).length = l.length := by
  unfold segReverseWindow
  rw [List.length_append, List.length_append, List.length_take,
    List.length_reverse, List.length_take, List.length_drop,
    List.length_drop]
  omega

/-- Three window reversals rotate left: `[0, k)`, `[k, n)`,
    `[0, n)` is `drop k ++ take k`. -/
theorem segWindow_rotate3 (l : List (BitVec 32)) (k : Nat)
    (hk : k ≤ l.length) :
    segReverseWindow (segReverseWindow (segReverseWindow l 0 k) k l.length)
      0 l.length = (l.drop k) ++ l.take k := by
  have hkk : min k l.length = k := Nat.min_eq_left hk
  have h1 : segReverseWindow l 0 k
      = (l.take k).reverse ++ l.drop k := by
    unfold segReverseWindow; simp
  have hlen1 : (segReverseWindow l 0 k).length = l.length :=
    segReverseWindow_length l 0 k (Nat.zero_le _) hk
  have hA : ((l.take k).reverse).length = k := by
    rw [List.length_reverse, List.length_take, hkk]
  have hAdrop : ((l.take k).reverse).drop k = [] := by
    have h := List.drop_length (l := ((l.take k).reverse))
    rw [hA] at h
    exact h
  have hBtake : (l.drop k).take (l.length - k) = l.drop k :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  have htail1 : (((l.take k).reverse) ++ l.drop k).drop l.length = [] := by
    rw [show l.length = (((l.take k).reverse) ++ l.drop k).length from by
      rw [List.length_append, hA, List.length_drop]; omega]
    exact List.drop_length
  -- Second window `[k, n)`: prefix untouched, suffix mirrored.
  have h2 : segReverseWindow (segReverseWindow l 0 k) k l.length
      = ((l.take k).reverse) ++ (l.drop k).reverse := by
    rw [h1]
    unfold segReverseWindow
    rw [List.take_append_of_le_length
        (by omega : k ≤ ((l.take k).reverse).length),
      List.take_of_length_le
        (by omega : ((l.take k).reverse).length ≤ k),
      List.drop_append_of_le_length
        (by omega : k ≤ ((l.take k).reverse).length),
      hAdrop, List.nil_append, hBtake, htail1]
    simp
  have hlen2 : (segReverseWindow (segReverseWindow l 0 k) k l.length).length
      = l.length := by
    rw [h2, List.length_append, hA]
    have hBr : ((l.drop k).reverse).length = l.length - k := by
      rw [List.length_reverse, List.length_drop]
    omega
  -- Third window `[0, n)`: full reversal of the concatenation.
  have hABlen : (((l.take k).reverse) ++ (l.drop k).reverse).length =
      l.length := by
    rw [← h2]; exact hlen2
  have htail2 : ((((l.take k).reverse) ++ (l.drop k).reverse)).drop
      l.length = [] := by
    rw [show l.length =
        ((((l.take k).reverse) ++ (l.drop k).reverse)).length from
      hABlen.symm]
    exact List.drop_length
  rw [h2]
  unfold segReverseWindow
  rw [htail2]
  simp only [List.take_zero, List.drop_zero, Nat.sub_zero]
  rw [List.take_of_length_le (by omega :
      ((((l.take k).reverse) ++ (l.drop k).reverse)).length ≤ l.length),
    List.nil_append, List.append_nil,
    List.reverse_append, List.reverse_reverse,
    List.reverse_reverse]

/-! ## R2: entry evaluation -/

/-- `emit_correct` for `vec_rotate`: program evaluation over the
    frozen leaves threads three admitted segment reversals
    (`[0, k)`, `[k, n)`, `[0, n)`) and agrees with left rotation
    (fuel covers each countdown plus the composition step; caller
    debt `k ≤ length` selects the forward's loud-guard leg). -/
theorem evalProgFunc_vecRotate (F : Nat) (l : List (BitVec 32))
    (k : Nat) (kB : BitVec 64)
    (hkB : kB.toNat = k)
    (hk : k ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF : (revIters 0 k + 1) + (revIters k l.length + 1) +
      (revIters 0 l.length + 1) + 1 ≤ F) :
    evalProgFunc vecRotateProg F vecRotateFunc
      [.stdVecVal l, .u64 kB] =
      vecRotateFwd l kB := by
  obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
  have hbind : bindArgs vecRotateFunc.args
      [.stdVecVal l, .u64 kB] =
      some [("v", .stdVecVal l), ("k", .u64 kB)] := rfl
  have hbody : vecRotateFunc.body =
      (.seq (.callRet "m" stdVecSizeName ["v"])
        (.seq (.let_ "z" (.u 64) (.lit (.u64 0)))
          (.seq (.callProg "v" vecSegReverseName ["v", "z", "k"])
            (.seq (.callProg "v" vecSegReverseName ["v", "k", "m"])
              (.seq (.callProg "v" vecSegReverseName ["v", "z", "m"])
                (.return_ (.var "v"))))))) := rfl
  have hnN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen64
  have hz0 : (0 : BitVec 64).toNat = 0 := rfl
  -- `m ← size(v)`.
  have hargs_m : lookupArgs [("v", .stdVecVal l), ("k", .u64 kB)]
      ["v"] = some [.stdVecVal l] :=
    lookupArgs_cons_hit _ _ _ _ _
      (by simp [envLookup]) (lookupArgs_nil _)
  have hcall_m : evalFuncFuel (G + 1) stdVecSizeFunc [.stdVecVal l] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [evalFuncFuel_stdVecSize]
    rfl
  have hstep_m := evalProgStmt_callRet_ok vecRotateProg (G + 1) "m"
    stdVecSizeName ["v"] [("v", .stdVecVal l), ("k", .u64 kB)]
    [.stdVecVal l] stdVecSizeFunc (.u64 (BitVec.ofNat 64 l.length))
    hargs_m rotFindSize hcall_m
  have hm₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envExtend_hit _ _ _
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hk₁ : envLookup (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) "k" =
      some (.u64 kB) := by
    rw [envExtend_miss _ _ _ _
      (show ("k" : String) ≠ "m" by decide)]
    simp [envLookup]
  -- `z ← 0`.
  have hstep_z := revLet vecRotateProg (G + 1) "z" (.u 64)
    (.lit (.u64 0)) (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
      "m" (.u64 (BitVec.ofNat 64 l.length))) (.u64 0)
    (by simp [evalExpr, litVal])
  have hz₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "z" = some (.u64 0) :=
    envExtend_hit _ _ _
  have hm₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₁ (by decide)
  have hv₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "v" = some (.stdVecVal l) :=
    envLookup_extend_miss _ _ _ _ _ hv₁ (by decide)
  have hk₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "z" (.u64 0)) "k" = some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₁ (by decide)
  -- First window `[0, k)`.
  have hF₁ : revIters 0 k + 1 ≤ G := by omega
  have hcall1 := evalProgFunc_vecSegReverse vecRotateProg G l 0 k
    0 kB hz0 hkB (by omega) (by omega) hlen64 hF₁ rotFindAt
  have hfw1 : vecSegReverseFwd l 0 kB
      = .ok (.stdVecVal (segReverseWindow l 0 kB.toNat)) := by
    simp only [vecSegReverseFwd]
    rw [hz0, hkB, if_pos ⟨Nat.zero_le _, hk⟩]
  rw [hfw1, hkB] at hcall1
  have hargs_c1 : lookupArgs (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0))
      ["v", "z", "k"] =
      some [.stdVecVal l, .u64 0, .u64 kB] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₂
      (lookupArgs_cons_hit _ _ _ _ _ hz₂
        (lookupArgs_cons_hit _ _ _ _ _ hk₂ (lookupArgs_nil _)))
  have hstep_c1 : evalProgStmt vecRotateProg (G + 1)
      (.callProg "v" vecSegReverseName ["v", "z", "k"])
      (envExtend (envExtend [("v", .stdVecVal l), ("k", .u64 kB)]
        "m" (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) =
      .ok (envExtend (envExtend (envExtend [("v", .stdVecVal l),
        ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
        "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)), .fellThrough) :=
    evalProgStmt_callProg_ok vecRotateProg G "v" vecSegReverseName
      ["v", "z", "k"] (envExtend (envExtend [("v", .stdVecVal l),
        ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
        "z" (.u64 0))
      [.stdVecVal l, .u64 0, .u64 kB]
      vecSegReverseFunc (.stdVecVal (segReverseWindow l 0 k))
      hargs_c1 rotFindSeg hcall1
  have hv₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v" =
      some (.stdVecVal (segReverseWindow l 0 k)) :=
    envExtend_hit _ _ _
  have hz₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "z" =
      some (.u64 0) :=
    envLookup_extend_miss _ _ _ _ _ hz₂ (by decide)
  have hk₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "k" =
      some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₂ (by decide)
  -- Second window `[k, n)`.
  have hlen1w : (segReverseWindow l 0 k).length = l.length :=
    segReverseWindow_length l 0 k (Nat.zero_le _) hk
  have hlen64w1 : (segReverseWindow l 0 k).length < 2 ^ 64 := by
    rw [hlen1w]; exact hlen64
  have hF₂ : revIters k l.length + 1 ≤ G := by omega
  have hcall2 := evalProgFunc_vecSegReverse vecRotateProg G
    (segReverseWindow l 0 k) k l.length kB
    (BitVec.ofNat 64 l.length) hkB hnN (by omega)
    (by omega) hlen64w1 hF₂ rotFindAt
  have hfw2 : vecSegReverseFwd (segReverseWindow l 0 k) kB
      (BitVec.ofNat 64 l.length)
      = .ok (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        kB.toNat (BitVec.ofNat 64 l.length).toNat)) := by
    simp only [vecSegReverseFwd]
    rw [hkB, hnN, hlen1w, if_pos ⟨hk, Nat.le_refl _⟩]
  rw [hfw2, hkB, hnN] at hcall2
  have hm₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₂ (by decide)
  have hargs_c2 : lookupArgs (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) ["v", "k", "m"] =
      some [.stdVecVal (segReverseWindow l 0 k), .u64 kB,
        .u64 (BitVec.ofNat 64 l.length)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₃
      (lookupArgs_cons_hit _ _ _ _ _ hk₃
        (lookupArgs_cons_hit _ _ _ _ _ hm₃ (lookupArgs_nil _)))
  have hstep_c2 : evalProgStmt vecRotateProg (G + 1)
      (.callProg "v" vecSegReverseName ["v", "k", "m"])
      (envExtend (envExtend (envExtend [("v", .stdVecVal l),
        ("k", .u64 kB)] "m" (.u64 (BitVec.ofNat 64 l.length)))
        "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) =
      .ok (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length)), .fellThrough) :=
    evalProgStmt_callProg_ok vecRotateProg G "v" vecSegReverseName
      ["v", "k", "m"] (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k)))
      [.stdVecVal (segReverseWindow l 0 k), .u64 kB,
        .u64 (BitVec.ofNat 64 l.length)]
      vecSegReverseFunc
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))
      hargs_c2 rotFindSeg hcall2
  have hv₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "v" =
      some (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length)) :=
    envExtend_hit _ _ _
  have hk₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "k" = some (.u64 kB) :=
    envLookup_extend_miss _ _ _ _ _ hk₃ (by decide)
  have hz₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "z" = some (.u64 0) :=
    envLookup_extend_miss _ _ _ _ _ hz₃ (by decide)
  have hm₄ : envLookup (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envLookup_extend_miss _ _ _ _ _ hm₃ (by decide)
  -- Third window `[0, n)`.
  have hlen2w : (segReverseWindow (segReverseWindow l 0 k)
      k l.length).length = l.length := by
    have h := segReverseWindow_length (segReverseWindow l 0 k)
      k l.length hk (by omega)
    rwa [hlen1w] at h
  have hlen64w2 : (segReverseWindow (segReverseWindow l 0 k)
      k l.length).length < 2 ^ 64 := by
    rw [hlen2w]; exact hlen64
  have hF₃ : revIters 0 l.length + 1 ≤ G := by omega
  have hcall3 := evalProgFunc_vecSegReverse vecRotateProg G
    (segReverseWindow (segReverseWindow l 0 k) k l.length)
    0 l.length 0 (BitVec.ofNat 64 l.length) hz0 hnN
    (by omega) (by omega) hlen64w2 hF₃ rotFindAt
  have hfw3 : vecSegReverseFwd
      (segReverseWindow (segReverseWindow l 0 k) k l.length) 0
      (BitVec.ofNat 64 l.length)
      = .ok (.stdVecVal (segReverseWindow
        (segReverseWindow (segReverseWindow l 0 k) k l.length)
        0 (BitVec.ofNat 64 l.length).toNat)) := by
    simp only [vecSegReverseFwd]
    rw [hz0, hnN, hlen2w, if_pos ⟨Nat.zero_le _, Nat.le_refl _⟩]
  rw [hfw3, hnN] at hcall3
  have hargs_c3 : lookupArgs (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) ["v", "z", "m"] =
      some [.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length), .u64 0, .u64 (BitVec.ofNat 64 l.length)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₄
      (lookupArgs_cons_hit _ _ _ _ _ hz₄
        (lookupArgs_cons_hit _ _ _ _ _ hm₄ (lookupArgs_nil _)))
  have hstep_c3 : evalProgStmt vecRotateProg (G + 1)
      (.callProg "v" vecSegReverseName ["v", "z", "m"])
      (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length))) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow
          (segReverseWindow l 0 k) k l.length) 0 l.length)),
        .fellThrough) :=
    evalProgStmt_callProg_ok vecRotateProg G "v" vecSegReverseName
      ["v", "z", "m"] (envExtend (envExtend (envExtend (envExtend
        [("v", .stdVecVal l), ("k", .u64 kB)] "m"
        (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
        (.stdVecVal (segReverseWindow l 0 k))) "v"
        (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
          k l.length)))
      [.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length), .u64 0, .u64 (BitVec.ofNat 64 l.length)]
      vecSegReverseFunc
      (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length))
      hargs_c3 rotFindSeg hcall3
  -- `return v` over the thrice-reversed words.
  have hrot := segWindow_rotate3 l k hk
  have hv₅ : envLookup (envExtend (envExtend (envExtend (envExtend
      (envExtend [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length))) "v" =
      some (.stdVecVal ((l.drop kB.toNat) ++ l.take kB.toNat)) := by
    rw [hkB, ← hrot]
    exact envExtend_hit _ _ _
  have hret := evalProgStmt_return vecRotateProg (G + 1) (.var "v")
    (envExtend (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l), ("k", .u64 kB)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "z" (.u64 0)) "v"
      (.stdVecVal (segReverseWindow l 0 k))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow l 0 k)
        k l.length))) "v"
      (.stdVecVal (segReverseWindow (segReverseWindow
        (segReverseWindow l 0 k) k l.length) 0 l.length)))
    (.stdVecVal ((l.drop kB.toNat) ++ l.take kB.toNat))
    (evalExpr_var_hit _ _ _ hv₅)
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_m,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_z,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_c1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_c2,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_c3,
    hret]
  simp only [vecRotateFwd]
  rw [hkB, if_pos hk]
