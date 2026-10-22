/-
Circe.Emit.VecSegReverse — S1 `std::vector<int32_t>` in-place
segment reverse (countdown two-pointer swaps over the half-open
range `[lo, hi)`): the entry composer over the frozen
checked-`at()` leaves.

This is the R shape with the window opened by two owned `u64`
params instead of `0`/`size`: the loop statement is *identical*
(`vecReverseBody`/`vecReverseWhile` are reused verbatim — same
`--j`, same two checked reads, same crossed `vecSet` writes,
`++i`), only the prelude binds `i ← lo`, `j ← hi` (pure `let`s,
no `size` call) and the forward reverses the window instead of
the whole list. Caller debt: `lo ≤ hi ≤ length` (out-of-range is
a loud `AssertFail` leg, unreachable under the contract — the
`at()` callees fail loudly past the end).
-/
import Circe.Emit.VecReverse
import Circe.Lemmas.CheckedIx

/-! ## S1: segment reverse entry -/

/-- Mangled entry name in `tests/cpp/vec_seg_reverse.cpp`. -/
def vecSegReverseName : String := "_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm"

/-- Window reversal on reified words (total: `take`/`drop` clip;
    the forward gates it behind the caller-debt check). -/
def segReverseWindow (l : List (BitVec 32)) (lo hi : Nat) :
    List (BitVec 32) :=
  l.take lo ++ ((l.drop lo).take (hi - lo)).reverse ++ l.drop hi

/-- Whole function: `i ← lo`, `j ← hi` (pure copies — `assign`
    needs bound targets, hence `let_` like the R prelude), the
    shared countdown loop, return of the updated words (the C++
    `void` functionalizes as words threading, the `vecAtSet`
    precedent). -/
def vecSegReverseFunc : Func :=
  ⟨vecSegReverseName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "lo", ty := .u 64, role := .owned },
    { name := "hi", ty := .u 64, role := .owned }],
   stdVecObjTy,
   (.seq (.let_ "i" (.u 64) (.var "lo"))
     (.seq (.let_ "j" (.u 64) (.var "hi"))
       (.seq vecReverseWhile
         (.return_ (.var "v")))))⟩

/-- Value-level forward for `vec_seg_reverse`: the window reverses
    under caller debt, loud `AssertFail` otherwise (the `at()`
    callees fail loudly past the end, so evaluation agrees). -/
def vecSegReverseFwd (l : List (BitVec 32)) (lo hi : BitVec 64) :
    Result Value :=
  if lo.toNat ≤ hi.toNat ∧ hi.toNat ≤ l.length then
    .ok (.stdVecVal (segReverseWindow l lo.toNat hi.toNat))
  else .error .AssertFail

/-- Program over which the entry evaluates (same frozen leaves as
    the whole-range reverse; only the non-const `at()` composer is
    called). -/
abbrev vecSegReverseProg : Prog :=
  [stdVecSizeFunc, { stdVecAtFunc with name := stdVecAtMutName },
    stdVecIndexFunc, stdVecRangeCheckFunc]

/-! ## S2: window invariant + loop proof -/

/-- `findFunc` resolves the renamed `at()` leaf (after the `size`
    head — same frozen-leaf order as `vecReverseProg`). -/
theorem segFindAt :
    findFunc vecSegReverseProg stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName } := by
  have hmiss : (stdVecSizeFunc.name == stdVecAtMutName) = false := by rfl
  show findFunc (stdVecSizeFunc :: _) _ = _
  rw [findFunc_miss _ _ _ hmiss]
  exact findFunc_hit _ _

/-- Loop invariant at the condition check over the original words:
    the indices sum to `lo + hi` (the window mirror), the finished
    outer window segments are mirrored into place, the live middle
    and everything outside `[lo, hi)` are untouched. -/
def SegInv (orig l : List (BitVec 32)) (lo hi i j : Nat) : Prop :=
  orig.length = l.length ∧ lo ≤ hi ∧ hi ≤ l.length ∧
  lo ≤ i ∧ j ≤ hi ∧ i + j = lo + hi ∧
  (∀ p, lo ≤ p → p < i → l[p]? = orig[lo + hi - 1 - p]?) ∧
  (∀ p, j ≤ p → p < hi → l[p]? = orig[lo + hi - 1 - p]?) ∧
  (∀ p, i ≤ p → p < j → l[p]? = orig[p]?) ∧
  (∀ p, p < lo → l[p]? = orig[p]?) ∧
  (∀ p, hi ≤ p → p < l.length → l[p]? = orig[p]?)

/-- One swap preserves the window invariant (indices advance to
    `(i + 1, j - 1)` over the doubly-updated words; the writes land
    strictly inside `[lo, hi)`, so the outside legs carry over). -/
theorem SegInv_step (orig l : List (BitVec 32)) (lo hi i j : Nat)
    (a b : BitVec 32)
    (hinv : SegInv orig l lo hi i j) (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b) :
    SegInv orig ((l.set i b).set (j - 1) a) lo hi (i + 1) (j - 1) := by
  obtain ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid,
    houtL, houtR⟩ := hinv
  have hj1 : 1 ≤ j := by omega
  have hlen1 : (l.set i b).length = l.length := List.length_set
  have hlen2 : ((l.set i b).set (j - 1) a).length = l.length := by
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
  -- is the `i`-write, the `j - 1`-write, or untouched): the U3 P1
  -- pack lemma; the touching case rides on `hab`.
  have hset : ∀ p, ((l.set i b).set (j - 1) a)[p]? =
      if p = i then some b
      else if p = j - 1 then some a else l[p]? :=
    fun p => doubleSet_read l i (j - 1) a b hiL hji hab p
  refine ⟨by rw [hlen2]; exact hlen, hlo, by omega,
    by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · -- Left outer (`lo ≤ p < i + 1`): either `p = i` (the fresh `b`,
    -- the mirror word) or strictly left (old left).
    intro p hloP hp
    by_cases h1 : p = i
    · rw [h1, hset, if_pos rfl]
      have hbi : l[j - 1]? = orig[j - 1]? :=
        hmid (j - 1) (by omega) (by omega)
      rw [hb] at hbi
      have hmir : orig[j - 1]? = orig[lo + hi - 1 - i]? := by
        congr 1; omega
      rw [hbi, hmir]
    · have hpi : p < i := by omega
      rw [hset, if_neg h1]
      by_cases h2 : p = j - 1
      · -- `p = j - 1` with `p < i < j`: `p < p`, impossible.
        omega
      · rw [if_neg h2, hleft p hloP hpi]
  · -- Right outer (`j - 1 ≤ p < hi`): either `p = j - 1` (the fresh
    -- `a`, the mirror word) or strictly right (old right).
    intro p hp hphi
    by_cases h1 : p = i
    · rw [h1, hset, if_pos rfl]
      have hbi : l[j - 1]? = orig[j - 1]? :=
        hmid (j - 1) (by omega) (by omega)
      rw [hb] at hbi
      have hmir : orig[j - 1]? = orig[lo + hi - 1 - i]? := by
        congr 1; omega
      rw [hbi, hmir]
    · by_cases h2 : p = j - 1
      · rw [h2, hset]
        have o : ¬ j - 1 = i := by omega
        rw [if_neg o, if_pos rfl]
        have hai : l[i]? = orig[i]? :=
          hmid i (by omega) (by omega)
        rw [ha] at hai
        have hmir : orig[i]? = orig[lo + hi - 1 - (j - 1)]? := by
          congr 1; omega
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
  · -- Outside left (`p < lo ≤ i, j - 1`): both writes miss.
    intro p hp
    rw [hset]
    have h1 : p ≠ i := by omega
    have h2 : p ≠ j - 1 := by omega
    rw [if_neg h1, if_neg h2, houtL p hp]
  · -- Outside right (`i, j - 1 < hi ≤ p`): both writes miss.
    intro p hp hplen
    rw [hset]
    have h1 : p ≠ i := by omega
    have h2 : p ≠ j - 1 := by omega
    rw [if_neg h1, if_neg h2, houtR p hp (by omega)]

/-- Window indexing through `getElem?`: position `p` of the window
    reversal holds the word from `lo + hi - 1 - p`. -/
theorem segGetElem (orig : List (BitVec 32)) (lo hi p : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ orig.length)
    (hlop : lo ≤ p) (hp : p < hi) :
    (segReverseWindow orig lo hi)[p]? = orig[lo + hi - 1 - p]? := by
  have htakeL : (orig.take lo).length = lo := by
    rw [List.length_take]; omega
  have hwinL : ((orig.drop lo).take (hi - lo)).length = hi - lo := by
    rw [List.length_take, List.length_drop]; omega
  unfold segReverseWindow
  rw [List.getElem?_append,
    if_pos (by rw [List.length_append, List.length_reverse, htakeL, hwinL]; omega :
      p < (orig.take lo ++
        ((orig.drop lo).take (hi - lo)).reverse).length),
    List.getElem?_append,
    if_neg (by omega : ¬ p < (orig.take lo).length), htakeL,
    List.getElem?_reverse (by rw [hwinL]; omega), hwinL,
    List.getElem?_take,
    if_pos (by omega : hi - lo - 1 - (p - lo) < hi - lo),
    List.getElem?_drop]
  congr 1
  omega

/-- Exit implies window reversal: every position is outer (the
    middle window is empty once `j ≤ i`), the outsides untouched. -/
theorem SegInv_exit (orig l : List (BitVec 32)) (lo hi i j : Nat)
    (hinv : SegInv orig l lo hi i j) (hexit : j ≤ i) :
    l = segReverseWindow orig lo hi := by
  obtain ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid,
    houtL, houtR⟩ := hinv
  have htakeL : (orig.take lo).length = lo := by
    rw [List.length_take]; omega
  have hwinL : ((orig.drop lo).take (hi - lo)).length = hi - lo := by
    rw [List.length_take, List.length_drop]; omega
  have hlenW : (segReverseWindow orig lo hi).length = l.length := by
    unfold segReverseWindow
    rw [List.length_append, List.length_append, List.length_take,
      List.length_reverse, List.length_take, List.length_drop,
      List.length_drop]
    omega
  have hpt : ∀ p, p < l.length →
      l[p]? = (segReverseWindow orig lo hi)[p]? := by
    intro p hp
    by_cases hloP : p < lo
    · rw [houtL p hloP]
      unfold segReverseWindow
      rw [List.getElem?_append,
        if_pos (by rw [List.length_append, List.length_reverse, htakeL, hwinL]; omega :
          p < (orig.take lo ++
            ((orig.drop lo).take (hi - lo)).reverse).length),
        List.getElem?_append,
        if_pos (by omega : p < (orig.take lo).length),
        List.getElem?_take, if_pos hloP]
    · by_cases hhiP : p < hi
      · have hmir : l[p]? = orig[lo + hi - 1 - p]? := by
          by_cases h1 : p < i
          · exact hleft p (by omega) h1
          · exact hright p (by omega) hhiP
        rw [hmir, segGetElem orig lo hi p hlo (by omega) (by omega)
          hhiP]
      · rw [houtR p (by omega) hp]
        unfold segReverseWindow
        rw [List.getElem?_append,
          if_neg (by rw [List.length_append, List.length_reverse, htakeL, hwinL]; omega :
            ¬ p < (orig.take lo ++
              ((orig.drop lo).take (hi - lo)).reverse).length),
          List.length_append, List.length_reverse, htakeL, hwinL,
          List.getElem?_drop]
        congr 1
        omega
  exact List.ext_getElem? (fun p => by
    by_cases hp : p < l.length
    · rw [hpt p hp]
    · have h1 : l.length ≤ p := by omega
      have h2 : (segReverseWindow orig lo hi).length ≤ p := by omega
      rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2])

/-- One body iteration swaps the end words and advances the indices
    (checked reads hit in-invariant; stores thread through `vecSet`;
    the evaluation is the R one, rerouted through the segment
    program's leaf table). -/
theorem segBody_hit (prog : Prog) (F : Nat) (ρ : Env)
    (orig l : List (BitVec 32)) (lo hiW i j : Nat)
    (iB jB : BitVec 64) (a b : BitVec 32)
    (hinv : SegInv orig l lo hiW i j)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (hlt : i < j)
    (ha : l[i]? = some a) (hb : l[j - 1]? = some b)
    (hlen64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hfind : findFunc prog stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName }) :
    ∃ ρ', evalProgStmt prog F vecReverseBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i b).set (j - 1) a)) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      envLookup ρ' "j" = some (.u64 (jB - 1)) ∧
      SegInv orig ((l.set i b).set (j - 1) a) lo hiW (i + 1)
        (j - 1) := by
  obtain ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid,
    houtL, houtR⟩ := hinv
  -- `--j`.
  have hexpr_j : evalExpr (.usub (.var "j") (.lit (.u64 1))) ρ =
      .ok (.u64 (jB - 1)) :=
    evalExpr_u64_usub _ _ _ _
      (evalExpr_var_hit _ _ _ hj)
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "j" (.u64 jB)
    (.u64 (jB - 1)) hj
  have hstep_j := revAssign prog F "j"
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
  have hstep_a := evalProgStmt_callRet_ok prog F "a"
    stdVecAtMutName ["v", "i"] ρ₁ [.stdVecVal l, .u64 iB]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 a)
    hargs_a hfind hcall_a
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
  have hstep_b := evalProgStmt_callRet_ok prog F "b"
    stdVecAtMutName ["v", "j"] (envExtend ρ₁ "a" (.i32 a))
    [.stdVecVal l, .u64 (jB - 1)]
    { stdVecAtFunc with name := stdVecAtMutName } (.i32 b)
    hargs_b hfind hcall_b
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
  have hstep_s1 := revVecSet prog F "v" (.var "i") (.var "b")
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
  have hstep_s2 := revVecSet prog F "v" (.var "j") (.var "a")
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
  have hstep_i := revAssign prog F "i"
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
  have heval : evalProgStmt prog F vecReverseBody ρ =
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
  have hstep := SegInv_step orig l lo hiW i j a b
    ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid, houtL,
      houtR⟩ hlt ha hb
  refine ⟨ρ₆, heval, ?_, ?_, ?_, ?_⟩
  · exact hfinal ▸ hv₆
  · exact hi₆
  · exact hj₆
  · exact hfinal ▸ hstep

/-- The countdown loop evaluates to the window-reversed words (fuel
    induction against `revIters`: each live iteration steps the
    invariant through `segBody_hit`, the exit state closes through
    `SegInv_exit`). -/
theorem segWhile_ok (prog : Prog) (F : Nat) (ρ : Env)
    (orig l : List (BitVec 32)) (lo hiW i j : Nat)
    (iB jB : BitVec 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB)) (hiN : iB.toNat = i)
    (hj : envLookup ρ "j" = some (.u64 jB)) (hjN : jB.toNat = j)
    (hinv : SegInv orig l lo hiW i j)
    (hlen64 : l.length < 2 ^ 64)
    (hF : revIters i j + 1 ≤ F)
    (hfind : findFunc prog stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName }) :
    ∃ ρ' l', evalProgStmt prog F vecReverseWhile ρ =
        .ok (ρ', .fellThrough) ∧
      l' = segReverseWindow orig lo hiW ∧
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
      obtain ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid,
        houtL, houtR⟩ := hinv
      have hiL : i < l.length := by omega
      have hjL : j - 1 < l.length := by omega
      obtain ⟨ρ₆, heval, hv₆, hi₆, hj₆, hinv₆⟩ :=
        segBody_hit prog F ρ orig l lo hiW i j iB jB l[i] l[j - 1]
          ⟨hlen, hlo, hhi, hloi, hjhi, hij, hleft, hright, hmid, houtL,
            houtR⟩
          hiN hjN h
          (List.getElem?_eq_getElem hiL)
          (List.getElem?_eq_getElem hjL)
          hlen64 hv hi hj hfind
      have hR : revIters i j = revIters (i + 1) (j - 1) + 1 :=
        (revIters_step i j h).symm
      have hF' : revIters (i + 1) (j - 1) + 1 ≤ F := by omega
      have hiN₆ : (iB + 1).toNat = i + 1 := by
        rw [revU64_succ_toNat iB l.length (by omega) hlen64, hiN]
      have hjN₆ : (jB - 1).toNat = j - 1 := by
        rw [revU64_pred_toNat jB (by omega), hjN]
      have hlen64' :
          ((l.set i l[j - 1]).set (j - 1) l[i]).length < 2 ^ 64 := by
        rw [List.length_set, List.length_set]
        exact hlen64
      obtain ⟨ρ', l', hloop, hwin, hv'⟩ :=
        ih ρ₆ ((l.set i l[j - 1]).set (j - 1) l[i]) (i + 1) (j - 1)
          (iB + 1) (jB - 1) hv₆ hi₆ hiN₆ hj₆ hjN₆ hinv₆ hlen64' hF'
      refine ⟨ρ', l', ?_, hwin, hv'⟩
      have hwhile :
          evalProgStmt prog (F + 1) vecReverseWhile ρ =
          evalProgStmt prog F vecReverseWhile ρ₆ := by
        cir_unfold_prog (vecReverseWhile, prog, F, hguard, heval)
      rw [hwhile]
      exact hloop
    · -- Exit: guard false, state exits, invariant closes to the window.
      have hguard : evalExpr (.ult (.var "i") (.var "j")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "j") ρ iB jB
          (evalExpr_var_hit _ _ _ hi) (evalExpr_var_hit _ _ _ hj)
        have hfb : (iB.ult jB) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit :
          evalProgStmt prog (F + 1) vecReverseWhile ρ =
          .ok (ρ, .fellThrough) := by
        simp only [vecReverseWhile,
          evalProgStmt_while_false prog _ _ _ _ hguard]
      have hwin : l = segReverseWindow orig lo hiW :=
        SegInv_exit orig l lo hiW i j hinv (by omega)
      exact ⟨ρ, l, hexit, hwin, hv⟩

/-- `emit_correct` for `vec_seg_reverse`: program evaluation over
    the frozen checked-`at()` leaves agrees with window reversal
    (fuel must cover the countdown: `revIters lo hi + 1`; caller
    debt `lo ≤ hi ≤ length` selects the forward's loud-guard leg). -/
theorem evalProgFunc_vecSegReverse (prog : Prog) (F : Nat)
    (l : List (BitVec 32))
    (lo hi : Nat) (loB hiB : BitVec 64)
    (hloB : loB.toNat = lo) (hhiB : hiB.toNat = hi)
    (hlo : lo ≤ hi) (hhi : hi ≤ l.length)
    (hlen64 : l.length < 2 ^ 64)
    (hF : revIters lo hi + 1 ≤ F)
    (hfind : findFunc prog stdVecAtMutName =
      some { stdVecAtFunc with name := stdVecAtMutName }) :
    evalProgFunc prog F vecSegReverseFunc
      [.stdVecVal l, .u64 loB, .u64 hiB] =
      vecSegReverseFwd l loB hiB := by
  have hbind : bindArgs vecSegReverseFunc.args
      [.stdVecVal l, .u64 loB, .u64 hiB] =
      some [("v", .stdVecVal l), ("lo", .u64 loB),
        ("hi", .u64 hiB)] := rfl
  have hbody : vecSegReverseFunc.body =
      (.seq (.let_ "i" (.u 64) (.var "lo"))
        (.seq (.let_ "j" (.u 64) (.var "hi"))
          (.seq vecReverseWhile
            (.return_ (.var "v"))))) := rfl
  -- `i ← lo`.
  have hlo₀ : envLookup [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "lo" = some (.u64 loB) := by
    simp [envLookup]
  have hstep_i := revLet prog F "i" (.u 64) (.var "lo")
    [("v", .stdVecVal l), ("lo", .u64 loB), ("hi", .u64 hiB)]
    (.u64 loB) (evalExpr_var_hit _ _ _ hlo₀)
  have hi₁ : envLookup (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "i" (.u64 loB)) "i" = some (.u64 loB) :=
    envExtend_hit _ _ _
  -- `j ← hi`.
  have hhi₀ : envLookup (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "i" (.u64 loB)) "hi" =
      some (.u64 hiB) := by
    rw [envExtend_miss _ _ _ _
      (show ("hi" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hstep_j := revLet prog F "j" (.u 64) (.var "hi")
    (envExtend [("v", .stdVecVal l), ("lo", .u64 loB),
      ("hi", .u64 hiB)] "i" (.u64 loB))
    (.u64 hiB) (evalExpr_var_hit _ _ _ hhi₀)
  have hj₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB)) "j" = some (.u64 hiB) :=
    envExtend_hit _ _ _
  have hv₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB)) "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "j" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₂ : envLookup (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB)) "i" = some (.u64 loB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "j" by decide)]
    exact hi₁
  -- Loop from `(lo, hi)`: the invariant holds trivially at entry.
  have hinv₀ : SegInv l l lo hi lo hi :=
    ⟨rfl, hlo, hhi, Nat.le_refl _, Nat.le_refl _, rfl,
      fun p _ hp => absurd hp (by omega),
      fun p hp hlt => absurd hlt (by omega),
      fun p _ _ => rfl,
      fun p _ => rfl,
      fun p _ _ => rfl⟩
  obtain ⟨ρ', l', hloop, hwin, hv'⟩ :=
    segWhile_ok prog F (envExtend (envExtend [("v", .stdVecVal l),
      ("lo", .u64 loB), ("hi", .u64 hiB)] "i" (.u64 loB)) "j"
      (.u64 hiB))
      l l lo hi lo hi loB hiB
      hv₂ hi₂ hloB hj₂ hhiB hinv₀ hlen64 hF hfind
  -- `return v`.
  have hret := evalProgStmt_return prog F (.var "v") ρ'
    (.stdVecVal l') (evalExpr_var_hit _ _ _ hv')
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_i,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_j,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]
  simp only [vecSegReverseFwd]
  rw [hloB, hhiB, if_pos ⟨hlo, hhi⟩, hwin]
