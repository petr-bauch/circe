/-
Circe.Emit.VecReverse — R1 `std::vector<int32_t>` in-place reverse
(countdown two-pointer swaps): the entry composer over the frozen
`size` / checked-`at()` leaves.

Unlike the read loops (V1/V2: `at()` values consumed directly), the
four `at()` sites here split into two checked reads and two
address takes: the entry reads both words through the checked leaf
(the range guard lives in the callee, which fails loudly
out-of-range) and writes them back crossed through `.vecSet`. No
edge is fused away — this is the N4d-iv-b2 composer precedent
(prog-based composition over validated leaves, no inlining), not
the `vecAtSet` fusion precedent (single store, guard fused into the
entry). The loop invariant (R2) is the mirrored outer segments
with the untouched middle window; `--j` cannot underflow since the
guard gives `j >= i + 1 >= 1`, and `i + j = n` is preserved.
-/
import Circe.Emit.VecAtSet

/-! ## R1: countdown reverse entry -/

/-- Mangled entry name in `tests/cpp/vec_reverse.cpp`. -/
def vecReverseName : String := "_Z11vec_reverseRSt6vectorIiSaIiEE"

/-- Loop body: `--j`, checked reads of both ends, crossed `vecSet`
    writes, `++i`. The `t` spill is a pure `let_` (loads/stores of
    the CIR alloca fuse to the direct word flow). -/
def vecReverseBody : CStmt :=
  (.seq (.assign "j" (.usub (.var "j") (.lit (.u64 1))))
    (.seq (.callRet "a" stdVecAtMutName ["v", "i"])
      (.seq (.callRet "b" stdVecAtMutName ["v", "j"])
        (.seq (.vecSet "v" (.var "i") (.var "b"))
          (.seq (.vecSet "v" (.var "j") (.var "a"))
            (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))))))

/-- The swap loop `while (i < j) body`. -/
def vecReverseWhile : CStmt :=
  (.while_ (.ult (.var "i") (.var "j")) vecReverseBody)

/-- Whole function: `j` from the `size` call, `i`/`t` pre-bound
    (`assign` needs bound targets), loop, return of the updated
    words (the C++ `void` functionalizes as words threading, the
    `vecAtSet` precedent). -/
def vecReverseFunc : Func :=
  ⟨vecReverseName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 }],
   stdVecObjTy,
   (.seq (.callRet "m" stdVecSizeName ["v"])
     (.seq (.let_ "i" (.u 64) (.lit (.u64 0)))
       (.seq (.let_ "j" (.u 64) (.var "m"))
         (.seq (.let_ "t" (.i 32) (.lit (.i32 0)))
           (.seq vecReverseWhile
             (.return_ (.var "v")))))))⟩

/-- Value-level forward for `vec_reverse`: list reversal. -/
def vecReverseFwd (l : List (BitVec 32)) : Result Value :=
  .ok (.stdVecVal l.reverse)

/-! ## R2: loop proof (reference + invariant + agreement) -/

/-- Program over which the entry evaluates (frozen `size` /
    checked-`at()` leaves; the `at()` callee validates as
    `stdVecAtFunc` under its non-const mangled name). -/
abbrev vecReverseProg : Prog :=
  [stdVecSizeFunc, { stdVecAtFunc with name := stdVecAtMutName },
    stdVecIndexFunc, stdVecRangeCheckFunc]

/-- Reference countdown loop: fuel-bounded, returns the final
    `(words, i, j)`. The `none` arms are unreachable in-invariant
    (`i, j'` index live words); they forward to the current state,
    keeping the match non-dependent. -/
def revLoop (l : List (BitVec 32)) : Nat → Nat → Nat →
    List (BitVec 32) × Nat × Nat
  | 0, i, j => (l, i, j)
  | fuel + 1, i, j =>
    if _ : i < j then
      let j' := j - 1
      match l[i]?, l[j']? with
      | some a, some b =>
        revLoop ((l.set i b).set j' a) fuel (i + 1) j'
      | _, _ => (l, i, j)
    else (l, i, j)

/-- Remaining iterations from `(i, j)` (closed form: the window
    shrinks by two each step). -/
def revIters (i j : Nat) : Nat :=
  if i < j then (j - i + 1) / 2 else 0

/-- One step consumes exactly one iteration of budget. -/
theorem revIters_step (i j : Nat) (h : i < j) :
    revIters (i + 1) (j - 1) + 1 = revIters i j := by
  unfold revIters
  have h' : i + 1 < j - 1 + 2 := by omega
  rw [if_pos h]
  -- The shrunken window still overlaps (or touches), so its count
  -- is one less; `omega` closes the `/ 2` arithmetic.
  by_cases h2 : i + 1 < j - 1
  · rw [if_pos h2]; omega
  · rw [if_neg h2]
    -- Touching or crossed after one step: the window had ≤ 2 live
    -- slots, so the count was exactly one.
    have : j - i ≤ 2 := by omega
    omega

/-- Loop invariant at the condition check over the original words:
    the indices still sum to `n`, outer segments are mirrored into
    place, the middle window is untouched. -/
def RevInv (orig l : List (BitVec 32)) (n i j : Nat) : Prop :=
  l.length = n ∧ orig.length = n ∧
  i + j = n ∧ i ≤ n ∧ j ≤ n ∧
  (∀ p, p < i → l[p]? = orig[n - 1 - p]?) ∧
  (∀ p, j ≤ p → p < n → l[p]? = orig[n - 1 - p]?) ∧
  (∀ p, i ≤ p → p < j → l[p]? = orig[p]?)

/-- Reverse indexing through `getElem?`: position `p` of the
    reversal holds the word from `n - 1 - p`. -/
theorem revGetElem (orig : List (BitVec 32)) (n p : Nat)
    (horig : orig.length = n) (hp : p < n) :
    (orig.reverse)[p]? = orig[n - 1 - p]? := by
  have h1n : p < orig.length := by omega
  rw [List.getElem?_reverse h1n]
  congr 1
  omega

/-- One swap preserves the invariant (indices advance to
    `(i + 1, j - 1)` over the doubly-updated words). -/
theorem RevInv_step (orig l : List (BitVec 32)) (n i j : Nat)
    (a b : BitVec 32)
    (hinv : RevInv orig l n i j) (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b) :
    RevInv orig ((l.set i b).set (j - 1) a) n (i + 1) (j - 1) := by
  obtain ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ := hinv
  have hj1 : 1 ≤ j := by omega
  have hlen1 : (l.set i b).length = n := by rw [List.length_set, hlen]
  have hlen2 : ((l.set i b).set (j - 1) a).length = n := by
    rw [List.length_set, hlen1]
  have hiL : i < l.length := by omega
  have hji : j - 1 < (l.set i b).length := by omega
  -- Equal indices read equal words: when the window touches
  -- (`i = j - 1`), both reads see the same cell.
  have hab : i = j - 1 → a = b := by
    intro h
    have e2 : l[i]? = some b := by rw [h]; exact hb
    exact Option.some_inj.mp (ha.symm.trans e2)
  -- Characterize the doubly-updated words pointwise (each position
  -- is the `i`-write, the `j - 1`-write, or untouched).
  have hset : ∀ p, ((l.set i b).set (j - 1) a)[p]? =
      if p = i then some b
      else if p = j - 1 then some a else l[p]? := by
    intro p
    by_cases h1 : p = i <;> by_cases h2 : p = j - 1
    · have hij1 : i = j - 1 := by omega
      rw [List.getElem?_set, if_pos h2.symm, if_pos hji, if_pos h1,
        hab hij1]
    · have o1 : ¬ j - 1 = p := by omega
      rw [List.getElem?_set, if_neg o1, h1,
        List.getElem?_set_self hiL, if_pos rfl]
    · rw [List.getElem?_set, if_pos h2.symm, if_pos hji, if_neg h1,
        if_pos h2]
    · have o1 : ¬ j - 1 = p := Ne.symm h2
      have o2 : i ≠ p := Ne.symm h1
      rw [List.getElem?_set, if_neg o1, List.getElem?_set_ne o2,
        if_neg h1, if_neg h2]
  refine ⟨hlen2, horig, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · -- Left outer (`p < i + 1`): either `p < i` (old left) or
    -- `p = i` (the fresh `b`, which is the mirror word).
    intro p hp
    by_cases h1 : p = i
    · rw [h1, hset, if_pos rfl]
      -- `b` is the old word at `j - 1`, i.e. the mirror of `i`.
      have hbi : l[j - 1]? = orig[j - 1]? := hmid (j - 1) (by omega) (by omega)
      rw [hb] at hbi
      have hmir : orig[j - 1]? = orig[n - 1 - i]? := by congr 1; omega
      rw [hbi, hmir]
    · have hpi : p < i := by omega
      rw [hset, if_neg h1]
      by_cases h2 : p = j - 1
      · -- `p = j - 1` with `p < i < j`: `p < p`, impossible.
        omega
      · rw [if_neg h2, hleft p hpi]
  · -- Right outer (`j - 1 ≤ p`): either `p = j - 1` (the fresh `a`,
    -- the mirror word) or strictly right (old right).
    intro p hp hpn
    by_cases h1 : p = i
    · rw [h1, hset, if_pos rfl]
      have hbi : l[j - 1]? = orig[j - 1]? := hmid (j - 1) (by omega) (by omega)
      rw [hb] at hbi
      have hmir : orig[j - 1]? = orig[n - 1 - i]? := by congr 1; omega
      rw [hbi, hmir]
    · by_cases h2 : p = j - 1
      · rw [h2, hset]
        have o : ¬ j - 1 = i := by omega
        rw [if_neg o, if_pos rfl]
        have hai : l[i]? = orig[i]? := hmid i (by omega) (by omega)
        rw [ha] at hai
        have hmir : orig[i]? = orig[n - 1 - (j - 1)]? := by congr 1; omega
        rw [hai, hmir]
      · rw [hset, if_neg h1, if_neg h2]
        have hpj : j ≤ p := by omega
        rw [hright p hpj (by omega)]
  · -- Middle (`i + 1 ≤ p < j - 1`): both writes miss.
    intro p hp1 hp2
    rw [hset]
    have h1 : p ≠ i := by omega
    have h2 : p ≠ j - 1 := by omega
    rw [if_neg h1, if_neg h2, hmid p (by omega) (by omega)]

/-! ## R2 (cont.): program evaluation (countdown loop) -/

/-- Program-level `assign` (leaves delegate). -/
theorem revAssign (prog : Prog) (F : Nat) (x : String) (e : CExpr)
    (ρ : Env) (v : Value) (ρ' : Env)
    (h : evalExpr e ρ = .ok v) (hu : envUpdate ρ x v = some ρ') :
    evalProgStmt prog F (.assign x e) ρ = .ok (ρ', .fellThrough) := by
  simpa [evalProgStmt] using (evalStmtFuel_assign F x e ρ v ρ' h hu)

/-- Program-level borrowed store (leaves delegate). -/
theorem revVecSet (prog : Prog) (F : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i : BitVec 64) (xv : BitVec 32)
    (l : List (BitVec 32)) (w : BitVec 32) (ρ' : Env)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.i32 xv))
    (hvec : envLookup ρ x = some (.stdVecVal l))
    (hget : l[i.toNat]? = some w)
    (hu : envUpdate ρ x (.stdVecVal (l.set i.toNat xv)) = some ρ') :
    evalProgStmt prog F (.vecSet x ie ve) ρ =
      .ok (ρ', .fellThrough) := by
  simpa [evalProgStmt] using
    (evalStmtFuel_vecSet F x ie ve ρ i xv l w ρ' hi hv hvec hget hu)

/-- Program-level `let_` (binds, extends). -/
theorem revLet (prog : Prog) (F : Nat) (x : String) (ty : CType)
    (e : CExpr) (ρ : Env) (v : Value)
    (h : evalExpr e ρ = .ok v) :
    evalProgStmt prog F (.let_ x ty e) ρ =
      .ok (envExtend ρ x v, .fellThrough) := by
  simpa [evalProgStmt] using (evalStmtFuel_let_ F x ty e ρ v h)

/-- Wrapping increments stay exact below `2 ^ 64` (the V1 midpoint
    Nat-correctness idiom, restated locally to avoid a heavy import). -/
theorem revU64_succ_toNat (x : BitVec 64) (n : Nat)
    (h : x.toNat < n) (hn : n < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, h1]
  exact Nat.mod_eq_of_lt (by omega)

/-- Wrapping decrements stay exact away from zero. -/
theorem revU64_pred_toNat (x : BitVec 64) (h : 1 ≤ x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  have hsub := u64sub_toNat_exact x 1 (by rw [h1]; exact h)
  rwa [h1] at hsub

/-- `findFunc` resolves `size` (program head). -/
theorem revFindSize :
    findFunc vecReverseProg stdVecSizeName = some stdVecSizeFunc := by
  show findFunc (stdVecSizeFunc :: _) _ = _
  exact findFunc_hit _ _

/-- `findFunc` resolves the renamed `at()` leaf (after the `size` head). -/
theorem revFindAt :
    findFunc vecReverseProg stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName } := by
  have hmiss : (stdVecSizeFunc.name == stdVecAtMutName) = false := by rfl
  show findFunc (stdVecSizeFunc :: _) _ = _
  rw [findFunc_miss _ _ _ hmiss]
  exact findFunc_hit _ _

/-- The renamed `at()` leaf evaluates like `stdVecAtFunc` (only the
    name differs; `evalFuncFuel` never inspects it). -/
theorem revAtBridge (F : Nat) (l : List (BitVec 32)) (n : BitVec 64) :
    evalFuncFuel F { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 n] =
      evalFuncFuel F stdVecAtFunc [.stdVecVal l, .u64 n] := by
  cases F <;> rfl

/-- The renamed `at()` leaf agrees with `stdVecAtFwd`. -/
theorem revAtEval (F : Nat) (l : List (BitVec 32)) (n : BitVec 64)
    (hlen64 : l.length < 2 ^ 64) :
    evalFuncFuel F { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 n] = stdVecAtFwd l n := by
  rw [revAtBridge]
  exact evalFuncFuel_stdVecAt F l n hlen64

/-- One reference step unfolds the swap (the `none` arms are dead:
    both reads hit). -/
theorem revLoop_step (l : List (BitVec 32)) (fuel i j : Nat)
    (a b : BitVec 32) (h : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b) :
    revLoop l (fuel + 1) i j =
      revLoop ((l.set i b).set (j - 1) a) fuel (i + 1) (j - 1) := by
  conv => lhs; unfold revLoop
  rw [dite_eq_left h]
  show (match l[i]?, l[j - 1]? with
    | some a, some b => revLoop ((l.set i b).set (j - 1) a) fuel (i + 1) (j - 1)
    | _, _ => (l, i, j)) = _
  rw [ha, hb]

/-- One body iteration swaps the end words and advances the indices
    (checked reads hit in-invariant; stores thread through `vecSet`). -/
theorem revBody_hit (F : Nat) (ρ : Env)
    (orig l : List (BitVec 32)) (n i j : Nat)
    (iB jB : BitVec 64) (a b : BitVec 32)
    (hinv : RevInv orig l n i j)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b)
    (hn64 : n < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB)) :
    ∃ ρ', evalProgStmt vecReverseProg F vecReverseBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i b).set (j - 1) a)) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      envLookup ρ' "j" = some (.u64 (jB - 1)) ∧
      RevInv orig ((l.set i b).set (j - 1) a) n (i + 1) (j - 1) := by
  obtain ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ := hinv
  have hn : l.length = n := hlen
  have hlen64 : l.length < 2 ^ 64 := by omega
  -- `--j`.
  have hexpr_j : evalExpr (.usub (.var "j") (.lit (.u64 1))) ρ =
      .ok (.u64 (jB - 1)) :=
    evalExpr_u64_usub _ _ _ _
      (evalExpr_var_hit _ _ _ hj)
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "j" (.u64 jB)
    (.u64 (jB - 1)) hj
  have hstep_j := revAssign vecReverseProg F "j"
    (.usub (.var "j") (.lit (.u64 1))) ρ (.u64 (jB - 1)) ρ₁
    hexpr_j hu₁
  have hj₁ : envLookup ρ₁ "j" = some (.u64 (jB - 1)) :=
    envLookup_update_hit _ _ _ _ hu₁
  have hv₁ : envLookup ρ₁ "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "j" by decide) hu₁]
    exact hv
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "j" by decide) hu₁]
    exact hi
  -- `a ← at(v, i)`.
  have hai : l[iB.toNat]? = some a := by rw [hiN]; exact ha
  have hlt_i : iB.toNat < l.length := by omega
  have hargs_a : lookupArgs ρ₁ ["v", "i"] =
      some [.stdVecVal l, .u64 iB] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₁
      (lookupArgs_cons_hit _ _ _ _ _ hi₁ (lookupArgs_nil _))
  have hcall_a : evalFuncFuel F
      { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 iB] = .ok (.i32 a) := by
    rw [revAtEval F l iB hlen64]
    exact stdVecAtFwd_ok l iB a hlt_i hai
  have hstep_a := evalProgStmt_callRet_ok vecReverseProg F "a"
    stdVecAtMutName ["v", "i"] ρ₁ [.stdVecVal l, .u64 iB]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 a)
    hargs_a revFindAt hcall_a
  have ha₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "a" =
      some (.i32 a) :=
    envExtend_hit _ _ _
  have hv₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "a" by decide)]
    exact hv₁
  have hi₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "i" =
      some (.u64 iB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "a" by decide)]
    exact hi₁
  have hj₂ : envLookup (envExtend ρ₁ "a" (.i32 a)) "j" =
      some (.u64 (jB - 1)) := by
    rw [envExtend_miss _ _ _ _
      (show ("j" : String) ≠ "a" by decide)]
    exact hj₁
  -- `b ← at(v, j)` (`j` already decremented).
  have hpred : (jB - 1).toNat = j - 1 := by
    rw [revU64_pred_toNat jB (by omega), hjN]
  have hbj : l[(jB - 1).toNat]? = some b := by
    rw [hpred]; exact hb
  have hlt_j : (jB - 1).toNat < l.length := by omega
  have hargs_b : lookupArgs (envExtend ρ₁ "a" (.i32 a)) ["v", "j"] =
      some [.stdVecVal l, .u64 (jB - 1)] :=
    lookupArgs_cons_hit _ _ _ _ _ hv₂
      (lookupArgs_cons_hit _ _ _ _ _ hj₂ (lookupArgs_nil _))
  have hcall_b : evalFuncFuel F
      { stdVecAtFunc with name := stdVecAtMutName }
      [.stdVecVal l, .u64 (jB - 1)] = .ok (.i32 b) := by
    rw [revAtEval F l (jB - 1) hlen64]
    exact stdVecAtFwd_ok l (jB - 1) b hlt_j hbj
  have hstep_b := evalProgStmt_callRet_ok vecReverseProg F "b"
    stdVecAtMutName ["v", "j"] (envExtend ρ₁ "a" (.i32 a))
    [.stdVecVal l, .u64 (jB - 1)]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 b)
    hargs_b revFindAt hcall_b
  have hb₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "b" = some (.i32 b) :=
    envExtend_hit _ _ _
  have hv₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "b" by decide)]
    exact hv₂
  have hi₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "i" = some (.u64 iB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "b" by decide)]
    exact hi₂
  have hj₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "j" = some (.u64 (jB - 1)) := by
    rw [envExtend_miss _ _ _ _
      (show ("j" : String) ≠ "b" by decide)]
    exact hj₂
  have ha₃ : envLookup (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
      "a" = some (.i32 a) := by
    rw [envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "b" by decide)]
    exact ha₂
  -- `v[i] := b`.
  obtain ⟨ρ₄, hu₄⟩ := envUpdate_some_of_lookup
    (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b)) "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat b)) hv₃
  have hstep_s1 := revVecSet vecReverseProg F "v" (.var "i") (.var "b")
    (envExtend (envExtend ρ₁ "a" (.i32 a)) "b" (.i32 b))
    iB b l a ρ₄
    (evalExpr_var_hit _ _ _ hi₃) (evalExpr_var_hit _ _ _ hb₃)
    hv₃ hai hu₄
  have hv₄ : envLookup ρ₄ "v" =
      some (.stdVecVal (l.set iB.toNat b)) :=
    envLookup_update_hit _ _ _ _ hu₄
  have hi₄ : envLookup ρ₄ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₄]
    exact hi₃
  have hj₄ : envLookup ρ₄ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "v" by decide) hu₄]
    exact hj₃
  have ha₄ : envLookup ρ₄ "a" = some (.i32 a) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "v" by decide) hu₄]
    exact ha₃
  -- `v[j] := a` (the current word there is whatever the first
  -- store left; only its existence matters).
  have hlen1 : (l.set iB.toNat b).length = l.length := List.length_set
  have hjL1 : (jB - 1).toNat < (l.set iB.toNat b).length := by omega
  have hcur : (l.set iB.toNat b)[(jB - 1).toNat]? =
      some ((l.set iB.toNat b)[(jB - 1).toNat]) :=
    List.getElem?_eq_getElem hjL1
  obtain ⟨ρ₅, hu₅⟩ := envUpdate_some_of_lookup ρ₄ "v"
    (.stdVecVal (l.set iB.toNat b))
    (.stdVecVal ((l.set iB.toNat b).set (jB - 1).toNat a)) hv₄
  have hstep_s2 := revVecSet vecReverseProg F "v" (.var "j") (.var "a")
    ρ₄ (jB - 1) a (l.set iB.toNat b)
    ((l.set iB.toNat b)[(jB - 1).toNat]) ρ₅
    (evalExpr_var_hit _ _ _ hj₄) (evalExpr_var_hit _ _ _ ha₄)
    hv₄ hcur hu₅
  have hv₅ : envLookup ρ₅ "v" =
      some (.stdVecVal ((l.set iB.toNat b).set (jB - 1).toNat a)) :=
    envLookup_update_hit _ _ _ _ hu₅
  have hi₅ : envLookup ρ₅ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₅]
    exact hi₄
  have hj₅ : envLookup ρ₅ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "v" by decide) hu₅]
    exact hj₄
  -- `++i`.
  have hexpr_i : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₅ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi₅) (by simp [evalExpr, litVal])
  obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup ρ₅ "i" (.u64 iB)
    (.u64 (iB + 1)) hi₅
  have hstep_i := revAssign vecReverseProg F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₅ (.u64 (iB + 1)) ρ₆
    hexpr_i hu₆
  have hi₆ : envLookup ρ₆ "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₆
  have hv₆ : envLookup ρ₆ "v" =
      some (.stdVecVal ((l.set iB.toNat b).set (jB - 1).toNat a)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₆]
    exact hv₅
  have hj₆ : envLookup ρ₆ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "i" by decide) hu₆]
    exact hj₅
  -- Assemble the sequential body.
  have hbody : vecReverseBody =
      (.seq (.assign "j" (.usub (.var "j") (.lit (.u64 1))))
        (.seq (.callRet "a" stdVecAtMutName ["v", "i"])
          (.seq (.callRet "b" stdVecAtMutName ["v", "j"])
            (.seq (.vecSet "v" (.var "i") (.var "b"))
              (.seq (.vecSet "v" (.var "j") (.var "a"))
                (.assign "i"
                  (.uadd (.var "i") (.lit (.u64 1))))))))) := rfl
  have heval : evalProgStmt vecReverseProg F vecReverseBody ρ =
      .ok (ρ₆, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_j,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_a,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_b,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_s1,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_s2,
      hstep_i]
  -- BitVec indices back to Nat indices.
  have hsetI : l.set iB.toNat b = l.set i b := by rw [hiN]
  have hfinal : ((l.set iB.toNat b).set (jB - 1).toNat a) =
      ((l.set i b).set (j - 1) a) := by
    rw [hsetI, hpred]
  have hstep := RevInv_step orig l n i j a b
    ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ hlt ha hb
  refine ⟨ρ₆, heval, ?_, ?_, ?_, ?_⟩
  · exact hfinal ▸ hv₆
  · exact hi₆
  · exact hj₆
  · exact hfinal ▸ hstep

/-- Exit implies full reversal: every position is outer (the middle
    window is empty once `j ≤ i`). -/
theorem RevInv_exit (orig l : List (BitVec 32)) (n i j : Nat)
    (hinv : RevInv orig l n i j) (hexit : j ≤ i) :
    l = orig.reverse := by
  obtain ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ := hinv
  have hpt : ∀ p, p < n → l[p]? = (orig.reverse)[p]? := by
    intro p hp
    by_cases h1 : p < i
    · rw [hleft p h1, revGetElem orig n p horig hp]
    · by_cases h2 : j ≤ p
      · rw [hright p h2 hp, revGetElem orig n p horig hp]
      -- Middle window: `i ≤ p < j ≤ i` is contradictory.
      · have hmid' := hmid p (by omega) (by omega)
        omega
  exact List.ext_getElem? (fun p => by
    by_cases hp : p < n
    · rw [hpt p hp]
    · have h1 : l.length ≤ p := by omega
      have h2 : (orig.reverse).length ≤ p := by
        rw [List.length_reverse]; omega
      rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2])

/-- The countdown loop evaluates to the fully-reversed words (fuel
    induction against `revIters`: each live iteration steps the
    invariant through `revBody_hit`, the exit state closes through
    `RevInv_exit`). -/
theorem revWhile_ok (F : Nat) (ρ : Env)
    (orig l : List (BitVec 32)) (n i j : Nat)
    (iB jB : BitVec 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB)) (hiN : iB.toNat = i)
    (hj : envLookup ρ "j" = some (.u64 jB)) (hjN : jB.toNat = j)
    (hinv : RevInv orig l n i j)
    (hn64 : n < 2 ^ 64)
    (hF : revIters i j + 1 ≤ F) :
    ∃ ρ' l', evalProgStmt vecReverseProg F vecReverseWhile ρ =
        .ok (ρ', .fellThrough) ∧
      l' = orig.reverse ∧
      envLookup ρ' "v" = some (.stdVecVal l') := by
  induction F generalizing ρ l i j iB jB with
  | zero =>
    have hfalse : False := by
      have hpos : 0 < revIters i j + 1 := Nat.succ_pos _
      omega
    exact hfalse.elim
  | succ F ih =>
    by_cases h : i < j
    · -- Live iteration: guard true, body swaps, recurse on the window.
      have hguard : evalExpr (.ult (.var "i") (.var "j")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "j") ρ iB jB
          (evalExpr_var_hit _ _ _ hi) (evalExpr_var_hit _ _ _ hj)
        have htb : (iB.ult jB) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩ := hinv
      have hiL : i < l.length := by omega
      have hjL : j - 1 < l.length := by omega
      obtain ⟨ρ₆, heval, hv₆, hi₆, hj₆, hinv₆⟩ :=
        revBody_hit F ρ orig l n i j iB jB l[i] l[j - 1]
          ⟨hlen, horig, hij, hin, hjn, hleft, hright, hmid⟩
          hiN hjN h
          (List.getElem?_eq_getElem hiL)
          (List.getElem?_eq_getElem hjL)
          hn64 hv hi hj
      have hR : revIters i j = revIters (i + 1) (j - 1) + 1 :=
        (revIters_step i j h).symm
      have hF' : revIters (i + 1) (j - 1) + 1 ≤ F := by omega
      have hiN₆ : (iB + 1).toNat = i + 1 := by
        rw [revU64_succ_toNat iB n (by omega) hn64, hiN]
      have hjN₆ : (jB - 1).toNat = j - 1 := by
        rw [revU64_pred_toNat jB (by omega), hjN]
      obtain ⟨ρ', l', hloop, hrev, hv'⟩ :=
        ih ρ₆ ((l.set i l[j - 1]).set (j - 1) l[i]) (i + 1) (j - 1)
          (iB + 1) (jB - 1) hv₆ hi₆ hiN₆ hj₆ hjN₆ hinv₆ hF'
      refine ⟨ρ', l', ?_, hrev, hv'⟩
      have hwhile : evalProgStmt vecReverseProg (F + 1) vecReverseWhile ρ =
          evalProgStmt vecReverseProg F vecReverseWhile ρ₆ := by
        simp only [vecReverseWhile,
          evalProgStmt_while_true vecReverseProg F _ _ _ hguard, heval]
      rw [hwhile]
      exact hloop
    · -- Exit: guard false, state exits, invariant closes to `reverse`.
      have hguard : evalExpr (.ult (.var "i") (.var "j")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "j") ρ iB jB
          (evalExpr_var_hit _ _ _ hi) (evalExpr_var_hit _ _ _ hj)
        have hfb : (iB.ult jB) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt vecReverseProg (F + 1) vecReverseWhile ρ =
          .ok (ρ, .fellThrough) := by
        simp only [vecReverseWhile,
          evalProgStmt_while_false vecReverseProg _ _ _ _ hguard]
      have hrev : l = orig.reverse :=
        RevInv_exit orig l n i j hinv (by omega)
      exact ⟨ρ, l, hexit, hrev, hv⟩

/-- `emit_correct` for `vec_reverse`: program evaluation over the
    frozen `size` / checked-`at()` leaves agrees with list reversal
    (fuel must cover the countdown: `revIters 0 n + 1`). -/
theorem evalProgFunc_vecReverse (F : Nat) (l : List (BitVec 32))
    (hn64 : l.length < 2 ^ 64)
    (hF : revIters 0 l.length + 1 ≤ F) :
    evalProgFunc vecReverseProg F vecReverseFunc [.stdVecVal l] =
      vecReverseFwd l := by
  have hbind : bindArgs vecReverseFunc.args [.stdVecVal l] =
      some [("v", .stdVecVal l)] := rfl
  have hbody : vecReverseFunc.body =
      (.seq (.callRet "m" stdVecSizeName ["v"])
        (.seq (.let_ "i" (.u 64) (.lit (.u64 0)))
          (.seq (.let_ "j" (.u 64) (.var "m"))
            (.seq (.let_ "t" (.i 32) (.lit (.i32 0)))
              (.seq vecReverseWhile
                (.return_ (.var "v"))))))) := rfl
  -- `m ← size(v)`.
  have hargs_m : lookupArgs [("v", .stdVecVal l)] ["v"] =
      some [.stdVecVal l] :=
    lookupArgs_cons_hit _ _ _ _ _
      (by simp [envLookup]) (lookupArgs_nil _)
  have hcall_m : evalFuncFuel F stdVecSizeFunc [.stdVecVal l] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [evalFuncFuel_stdVecSize]
    rfl
  have hstep_m := evalProgStmt_callRet_ok vecReverseProg F "m"
    stdVecSizeName ["v"] [("v", .stdVecVal l)] [.stdVecVal l]
    stdVecSizeFunc (.u64 (BitVec.ofNat 64 l.length))
    hargs_m revFindSize hcall_m
  have hm₁ : envLookup (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envExtend_hit _ _ _
  -- `i ← 0`.
  have hstep_i := revLet vecReverseProg F "i" (.u 64)
    (.lit (.u64 0)) (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) (.u64 0)
    (by simp [evalExpr, litVal])
  have hi₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "i" (.u64 0)) "i" =
      some (.u64 0) :=
    envExtend_hit _ _ _
  have hm₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "i" (.u64 0)) "m" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("m" : String) ≠ "i" by decide)]
    exact hm₁
  -- `j ← m`.
  have hstep_j := revLet vecReverseProg F "j" (.u 64) (.var "m")
    (envExtend (envExtend [("v", .stdVecVal l)] "m"
      (.u64 (BitVec.ofNat 64 l.length))) "i" (.u64 0))
    (.u64 (BitVec.ofNat 64 l.length))
    (evalExpr_var_hit _ _ _ hm₂)
  have hj₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length))) "j" =
      some (.u64 (BitVec.ofNat 64 l.length)) :=
    envExtend_hit _ _ _
  have hv₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "j" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hi₃ : envLookup (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length))) "i" =
      some (.u64 0) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "j" by decide)]
    exact hi₂
  -- `t ← 0` (spill slot, pure `let_`).
  have hstep_t := revLet vecReverseProg F "t" (.i 32)
    (.lit (.i32 0)) (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length)))
    (.i32 0) (by simp [evalExpr, litVal])
  -- Loop from `(0, n)`: the invariant holds trivially at entry.
  have hjN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn64
  have hinv₀ : RevInv l l l.length 0 l.length :=
    ⟨rfl, rfl, by omega, Nat.zero_le _, Nat.le_refl _,
      fun p hp => (Nat.not_lt_zero p hp).elim,
      fun p hp hlt => absurd hlt (by omega),
      fun p _ _ => rfl⟩
  obtain ⟨ρ', l', hloop, hrev, hv'⟩ :=
    revWhile_ok F (envExtend (envExtend (envExtend (envExtend
      [("v", .stdVecVal l)] "m" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 0)) "j" (.u64 (BitVec.ofNat 64 l.length)))
      "t" (.i32 0))
      l l l.length 0 l.length
      0 (BitVec.ofNat 64 l.length)
      (by
        rw [envExtend_miss _ _ _ _
          (show ("v" : String) ≠ "t" by decide)]
        exact hv₃)
      hi₃ rfl hj₃ hjN hinv₀ hn64 hF
  -- `return v`.
  have hret := evalProgStmt_return vecReverseProg F (.var "v") ρ'
    (.stdVecVal l') (evalExpr_var_hit _ _ _ hv')
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_m,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_i,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_j,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_t,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]
  simp [vecReverseFwd, hrev]
