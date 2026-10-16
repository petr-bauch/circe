/-
C2b sort entry over `std::vector<int>` (bottom-up merge sort).

Corpus: `tests/cpp/vec_merge_sort.cpp` → `tests/cir/vec_merge_sort.cir`
(entry `_Z14vec_merge_sortRSt6vectorIiSaIiEES2_`: two `mutBorrow`
vectors `a` (sorted in place) and `tmp` (caller pre-sized), `void`
out; outer width-doubling loop, inner segment loop with a
`cir.call` to `merge_runs` per segment plus clamping `cir.if`s and
a fused copy-back loop).

Model: the segment loop's `callProg` rebinds `"tmp"` to the callee
result (`envExtend` shadow — the C-route core: calls in loop
bodies); everything else is first-order (`assign`/`if_`/`while_`,
`at()` fused to guards + `stdVecAt`/`vecSet`, clamps as
`if_/.skip`). Loop inductions are program-level with a
lookup-based invariant (`SortInv`) and existential post-envs (the
call conses one binding per iteration, so syntactic env equality
is unstatable). Forward models take the evaluation fuel as an
explicit budget (segment counts need division for exact measures,
so the fuel stays opaque with sufficiency premises instead).
-/
import Circe.Emit.VecMergeRuns

namespace VecMergeSort

/-- Function name (Itanium mangling of a `vec_merge_sort` free
function taking `vector<int>&` + `vector<int>&`, returning
`void`). -/
def vecMergeSortName : String :=
  "_Z14vec_merge_sortRSt6vectorIiSaIiEES2_"

/-- Clamp `mid` to `n` (no-op else-branch). -/
def sortClampMid : CStmt :=
  (.if_ (.ult (.var "n") (.var "mid"))
    (.assign "mid" (.var "n")) .skip)

/-- Clamp `hi` to `n` (no-op else-branch). -/
def sortClampHi : CStmt :=
  (.if_ (.ult (.var "n") (.var "hi"))
    (.assign "hi" (.var "n")) .skip)

/-- One segment call (rebinds `"tmp"` to the merged run). -/
def sortSegCall : CStmt :=
  (.callProg "tmp" VecMergeRuns.mergeRunsName ["a", "tmp", "lo", "mid", "hi"])

/-- Copy-back body: fused `tmp` read + `a` write, advance `t`. -/
def sortCopyBody : CStmt :=
  (.seq (.if_ (.ult (.var "t") (.stdVecLen "tmp"))
            (.vecSet "a" (.var "t") (.stdVecAt "tmp" (.var "t")))
            .fail)
    (.assign "t" (.uadd (.var "t") (.lit (.u64 1)))))

/-- Copy-back loop `while (t < hi) body`. -/
def sortCopyBack : CStmt :=
  (.while_ (.ult (.var "t") (.var "hi")) sortCopyBody)

/-- Segment-loop body: bounds, clamps, call, copy-back, advance. -/
def sortSegBody : CStmt :=
  (.seq (.assign "mid" (.uadd (.var "lo") (.var "width")))
    (.seq sortClampMid
      (.seq (.assign "hi"
              (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")))
        (.seq sortClampHi
          (.seq sortSegCall
            (.seq (.assign "t" (.var "lo"))
              (.seq sortCopyBack
                (.assign "lo"
                  (.uadd (.uadd (.var "lo") (.var "width"))
                    (.var "width"))))))))))

/-- Segment loop `while (lo < n) body`. -/
def sortSegLoop : CStmt :=
  (.while_ (.ult (.var "lo") (.var "n")) sortSegBody)

/-- Outer-loop body: reset `lo`, run the segments, double `width`. -/
def sortOuterBody : CStmt :=
  (.seq (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0))))
    (.seq sortSegLoop
      (.assign "width"
        (.uadd (.var "width") (.var "width")))))

/-- Outer loop `while (width < n) body`. -/
def sortOuterLoop : CStmt :=
  (.while_ (.ult (.var "width") (.var "n")) sortOuterBody)

/-- Whole function: `let_`-prelude binds all locals, outer loop,
    the sorted `a` words return (`xor_n` out-param idiom). -/
def vecMergeSortFunc : Func :=
  ⟨vecMergeSortName,
   [{ name := "a", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "tmp", ty := stdVecObjTy, role := .mutBorrow 1 }],
   stdVecObjTy,
   (.seq (.let_ "n" (.u 64) (.stdVecLen "a"))
     (.seq (.let_ "width" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
       (.seq (.let_ "lo" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq (.let_ "mid" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
           (.seq (.let_ "hi" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
             (.seq (.let_ "t" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
               (.seq sortOuterLoop
                 (.return_ (.var "a")))))))))⟩

/-- The sort program (callee before entry, the `arraySortProg`
    precedent). -/
def vecMergeSortProg : Prog := [VecMergeRuns.mergeRunsFunc, vecMergeSortFunc]

/-- Loop environment, in prelude `let_` cons order, so the entry
    bridge is `rfl`. -/
def mkSortEnv (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) : Env :=
  [("t", .u64 t), ("hi", .u64 hi), ("mid", .u64 mid),
   ("lo", .u64 lo), ("width", .u64 w), ("n", .u64 n),
   ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]

theorem mkSortEnv_a (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "a" =
      some (.stdVecVal la) := by
  simp [mkSortEnv, envLookup, show ("a" : String) ≠ "t" by decide,
    show ("a" : String) ≠ "hi" by decide,
    show ("a" : String) ≠ "mid" by decide,
    show ("a" : String) ≠ "lo" by decide,
    show ("a" : String) ≠ "width" by decide,
    show ("a" : String) ≠ "n" by decide]

theorem mkSortEnv_tmp (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "tmp" =
      some (.stdVecVal lt) := by
  simp [mkSortEnv, envLookup, show ("tmp" : String) ≠ "t" by decide,
    show ("tmp" : String) ≠ "hi" by decide,
    show ("tmp" : String) ≠ "mid" by decide,
    show ("tmp" : String) ≠ "lo" by decide,
    show ("tmp" : String) ≠ "width" by decide,
    show ("tmp" : String) ≠ "n" by decide,
    show ("tmp" : String) ≠ "a" by decide]

theorem mkSortEnv_n (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "n" =
      some (.u64 n) := by
  simp [mkSortEnv, envLookup, show ("n" : String) ≠ "t" by decide,
    show ("n" : String) ≠ "hi" by decide,
    show ("n" : String) ≠ "mid" by decide,
    show ("n" : String) ≠ "lo" by decide,
    show ("n" : String) ≠ "width" by decide]

theorem mkSortEnv_width (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "width" =
      some (.u64 w) := by
  simp [mkSortEnv, envLookup, show ("width" : String) ≠ "t" by decide,
    show ("width" : String) ≠ "hi" by decide,
    show ("width" : String) ≠ "mid" by decide,
    show ("width" : String) ≠ "lo" by decide]

theorem mkSortEnv_lo (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "lo" =
      some (.u64 lo) := by
  simp [mkSortEnv, envLookup, show ("lo" : String) ≠ "t" by decide,
    show ("lo" : String) ≠ "hi" by decide,
    show ("lo" : String) ≠ "mid" by decide]

theorem mkSortEnv_mid (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "mid" =
      some (.u64 mid) := by
  simp [mkSortEnv, envLookup, show ("mid" : String) ≠ "t" by decide,
    show ("mid" : String) ≠ "hi" by decide]

theorem mkSortEnv_hi (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "hi" =
      some (.u64 hi) := by
  simp [mkSortEnv, envLookup, show ("hi" : String) ≠ "t" by decide]

theorem mkSortEnv_t (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    envLookup (mkSortEnv la lt n w lo mid hi t) "t" =
      some (.u64 t) := by
  simp [mkSortEnv, envLookup]

/-- Lookup-based loop invariant (shadow-tolerant: the segment call
    conses a `"tmp"` binding, so syntactic env equality is
    unstatable — all reasoning goes through lookups). -/
def SortInv (ρ : Env) (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) : Prop :=
  envLookup ρ "a" = some (.stdVecVal la) ∧
  envLookup ρ "tmp" = some (.stdVecVal lt) ∧
  envLookup ρ "n" = some (.u64 n) ∧
  envLookup ρ "width" = some (.u64 w) ∧
  envLookup ρ "lo" = some (.u64 lo) ∧
  envLookup ρ "mid" = some (.u64 mid) ∧
  envLookup ρ "hi" = some (.u64 hi) ∧
  envLookup ρ "t" = some (.u64 t)

/-- The prelude environment satisfies the invariant. -/
theorem mkSortEnv_inv (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) :
    SortInv (mkSortEnv la lt n w lo mid hi t) la lt
      n w lo mid hi t :=
  ⟨mkSortEnv_a _ _ _ _ _ _ _ _, mkSortEnv_tmp _ _ _ _ _ _ _ _,
   mkSortEnv_n _ _ _ _ _ _ _ _, mkSortEnv_width _ _ _ _ _ _ _ _,
   mkSortEnv_lo _ _ _ _ _ _ _ _, mkSortEnv_mid _ _ _ _ _ _ _ _,
   mkSortEnv_hi _ _ _ _ _ _ _ _, mkSortEnv_t _ _ _ _ _ _ _ _⟩

/-! ## Small helpers -/

/-- Wrapping adds stay exact below `2 ^ 64`. -/
theorem bv64_add_toNat (x y : BitVec 64)
    (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt h

/-- Program-level `skip` (leaves delegate). -/
theorem evalProgStmt_skip (prog : Prog) (F : Nat) (ρ : Env) :
    evalProgStmt prog F .skip ρ = .ok (ρ, .fellThrough) := by
  simpa [evalProgStmt] using
    (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
      cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])

/-- Invariant preservation across `assign` (one lemma per assigned
    variable; `n`/`a`/`tmp` are never assigned). -/
theorem sortInv_update_lo (ρ ρ' : Env) (la lt : List (BitVec 32))
    (n w lo lo' mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hu : envUpdate ρ "lo" (.u64 lo') = some ρ') :
    SortInv ρ' la lt n w lo' mid hi t := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "lo" by decide) hu]; exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("tmp" : String) ≠ "lo" by decide) hu]; exact htmp
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "lo" by decide) hu]; exact hn
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("width" : String) ≠ "lo" by decide) hu]; exact hw
  · exact envLookup_update_hit _ _ _ _ hu
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("mid" : String) ≠ "lo" by decide) hu]; exact hmid
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "lo" by decide) hu]; exact hhi
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "lo" by decide) hu]; exact htt

theorem sortInv_update_mid (ρ ρ' : Env) (la lt : List (BitVec 32))
    (n w lo mid mid' hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hu : envUpdate ρ "mid" (.u64 mid') = some ρ') :
    SortInv ρ' la lt n w lo mid' hi t := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "mid" by decide) hu]; exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("tmp" : String) ≠ "mid" by decide) hu]; exact htmp
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "mid" by decide) hu]; exact hn
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("width" : String) ≠ "mid" by decide) hu]; exact hw
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "mid" by decide) hu]; exact hlo
  · exact envLookup_update_hit _ _ _ _ hu
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "mid" by decide) hu]; exact hhi
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "mid" by decide) hu]; exact htt

theorem sortInv_update_hi (ρ ρ' : Env) (la lt : List (BitVec 32))
    (n w lo mid hi hi' t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hu : envUpdate ρ "hi" (.u64 hi') = some ρ') :
    SortInv ρ' la lt n w lo mid hi' t := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "hi" by decide) hu]; exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("tmp" : String) ≠ "hi" by decide) hu]; exact htmp
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "hi" by decide) hu]; exact hn
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("width" : String) ≠ "hi" by decide) hu]; exact hw
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "hi" by decide) hu]; exact hlo
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("mid" : String) ≠ "hi" by decide) hu]; exact hmid
  · exact envLookup_update_hit _ _ _ _ hu
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "hi" by decide) hu]; exact htt

theorem sortInv_update_t (ρ ρ' : Env) (la lt : List (BitVec 32))
    (n w lo mid hi t t' : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hu : envUpdate ρ "t" (.u64 t') = some ρ') :
    SortInv ρ' la lt n w lo mid hi t' := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "t" by decide) hu]; exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("tmp" : String) ≠ "t" by decide) hu]; exact htmp
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "t" by decide) hu]; exact hn
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("width" : String) ≠ "t" by decide) hu]; exact hw
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "t" by decide) hu]; exact hlo
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("mid" : String) ≠ "t" by decide) hu]; exact hmid
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "t" by decide) hu]; exact hhi
  · exact envLookup_update_hit _ _ _ _ hu

theorem sortInv_update_width (ρ ρ' : Env) (la lt : List (BitVec 32))
    (n w w' lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hu : envUpdate ρ "width" (.u64 w') = some ρ') :
    SortInv ρ' la lt n w' lo mid hi t := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "width" by decide) hu]; exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("tmp" : String) ≠ "width" by decide) hu]; exact htmp
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "width" by decide) hu]; exact hn
  · exact envLookup_update_hit _ _ _ _ hu
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("lo" : String) ≠ "width" by decide) hu]; exact hlo
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("mid" : String) ≠ "width" by decide) hu]; exact hmid
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("hi" : String) ≠ "width" by decide) hu]; exact hhi
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "width" by decide) hu]; exact htt

/-- Invariant preservation across the segment call (rebinds
    `"tmp"`, everything else passes through). -/
theorem sortInv_extend_tmp (ρ : Env) (la lt lt' : List (BitVec 32))
    (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t) :
    SortInv (envExtend ρ "tmp" (.stdVecVal lt')) la lt'
      n w lo mid hi t := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [envExtend_miss _ _ _ _ (show ("a" : String) ≠ "tmp" by decide)];
    exact ha
  · exact envExtend_hit _ _ _
  · rw [envExtend_miss _ _ _ _ (show ("n" : String) ≠ "tmp" by decide)];
    exact hn
  · rw [envExtend_miss _ _ _ _
      (show ("width" : String) ≠ "tmp" by decide)]; exact hw
  · rw [envExtend_miss _ _ _ _ (show ("lo" : String) ≠ "tmp" by decide)];
    exact hlo
  · rw [envExtend_miss _ _ _ _
      (show ("mid" : String) ≠ "tmp" by decide)]; exact hmid
  · rw [envExtend_miss _ _ _ _ (show ("hi" : String) ≠ "tmp" by decide)];
    exact hhi
  · rw [envExtend_miss _ _ _ _ (show ("t" : String) ≠ "tmp" by decide)];
    exact htt

/-! ## Forward models (fuel-budgeted, mirroring the loops) -/

/-- Copy-back model: exact fuel (one step per element). -/
def sortCopyFwd (lt : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Result (List (BitVec 32) × Nat)
  | la, 0, t, _ => .ok (la, t)
  | la, fuel + 1, t, hi =>
    if _ : t < hi then
      match lt[t]? with
      | none => .error .AssertFail
      | some x =>
        match la[t]? with
        | none => .error .AssertFail
        | some _ => sortCopyFwd lt (la.set t x) fuel (t + 1) hi
    else .ok (la, t)

/-- Segment-loop model: the evaluation fuel doubles as the model
    budget (segment counts need division for exact measures, so the
    fuel stays opaque with a sufficiency premise at each use). -/
def sortSegFwd (la lt : List (BitVec 32))
    (F w lo n : Nat) : Result (List (BitVec 32) × List (BitVec 32)) :=
  match F with
  | 0 => .ok (la, lt)
  | fuel + 1 =>
    if _ : lo < n then
      match VecMergeRuns.mergeRunsFwd la lt lo (Nat.min (lo + w) n)
          (Nat.min (lo + w + w) n) with
      | .error e => .error e
      | .ok (.stdVecVal lt') =>
        match sortCopyFwd lt' la
            (Nat.min (lo + w + w) n - lo) lo
            (Nat.min (lo + w + w) n) with
        | .error e => .error e
        | .ok (la', _) => sortSegFwd la' lt' fuel w (lo + w + w) n
      | .ok _ => .error .AssertFail
    else .ok (la, lt)

/-- Outer-loop model: same fuel-budget discipline. -/
def sortOuterFwd (la lt : List (BitVec 32))
    (F w n : Nat) : Result (List (BitVec 32) × List (BitVec 32)) :=
  match F with
  | 0 => .ok (la, lt)
  | fuel + 1 =>
    if _ : w < n then
      match sortSegFwd la lt fuel w 0 n with
      | .error e => .error e
      | .ok (la', lt') => sortOuterFwd la' lt' fuel (w + w) n
    else .ok (la, lt)

/-- Whole-entry forward: outer passes over `(a, tmp)`, then the
    sorted `a` words. -/
def vecMergeSortFwd (la lt : List (BitVec 32))
    (F : Nat) : Result Value :=
  match sortOuterFwd la lt F 1 la.length with
  | .error e => .error e
  | .ok (la', _) => .ok (.stdVecVal la')

/-! ## Copy-back loop -/

theorem sortCopyGuard_eval (ρ : Env) (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64) :
    evalExpr (.ult (.var "t") (.stdVecLen "tmp")) ρ =
      .ok (.b (decide (t.toNat < lt.length))) := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hsize : evalExpr (.stdVecLen "tmp") ρ =
      .ok (.u64 (BitVec.ofNat 64 lt.length)) :=
    evalExpr_stdVecLen_some "tmp" _ lt htmp
  have hnv : evalExpr (.var "t") ρ = .ok (.u64 t) :=
    evalExpr_var_hit _ _ _ htt
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len t lt.length hlent] at hult
  exact hult

theorem sortCopyGuardT_eval (ρ : Env) (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t) :
    evalExpr (.ult (.var "t") (.var "hi")) ρ =
      .ok (.b (decide (t.toNat < hi.toNat))) := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hnv : evalExpr (.var "t") ρ = .ok (.u64 t) :=
    evalExpr_var_hit _ _ _ htt
  have hmv : evalExpr (.var "hi") ρ = .ok (.u64 hi) :=
    evalExpr_var_hit _ _ _ hhi
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
  rw [VecMergeRuns.bv64_ult_toNat t hi] at hult
  exact hult

theorem sortCopyRead_hit (ρ : Env) (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64) (x : BitVec 32)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hget : lt[t.toNat]? = some x) :
    evalExpr (.stdVecAt "tmp" (.var "t")) ρ = .ok (.i32 x) := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  exact evalExpr_stdVecAt_some "tmp" _ _ _ _ _
    htmp (evalExpr_var_hit _ _ _ htt) hget

theorem copyIncrT (prog : Prog) (F : Nat) (ρ ρ' : Env)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hu : envUpdate ρ "t" (.u64 (t + 1)) = some ρ') :
    evalProgStmt prog F
      (.assign "t" (.uadd (.var "t") (.lit (.u64 1)))) ρ =
      .ok (ρ', .fellThrough) ∧
      SortInv ρ' la lt n w lo mid hi (t + 1) := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have ht : evalExpr (.uadd (.var "t") (.lit (.u64 1))) ρ =
      .ok (.u64 (t + 1)) := by
    have h1 : evalExpr (.lit (.u64 1)) ρ = .ok (.u64 1) := by
      simp [evalExpr, litVal]
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ htt) h1
  have hstmt := evalStmtFuel_assign F _ _ _ _ _ ht hu
  have hprog : evalProgStmt prog F
      (.assign "t" (.uadd (.var "t") (.lit (.u64 1)))) ρ =
      .ok (ρ', .fellThrough) := by
    simpa [evalProgStmt] using hstmt
  exact ⟨hprog, sortInv_update_t _ _ _ _ _ _ _ _ _ _ _
    ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hu⟩

/-- Copy-back body hit: `t` live in `tmp` (and in `a` by the
    segment invariant), store + advance. -/
theorem sortCopyBody_hit (prog : Prog) (F : Nat) (ρ ρ' ρ'' : Env)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (x v : BitVec 32)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64)
    (hgetT : lt[t.toNat]? = some x)
    (hgetA : la[t.toNat]? = some v)
    (hltT : t.toNat < lt.length)
    (hwr : envUpdate ρ "a" (.stdVecVal (la.set t.toNat x)) = some ρ')
    (hu : envUpdate ρ' "t" (.u64 (t + 1)) = some ρ'') :
    evalProgStmt prog F sortCopyBody ρ = .ok (ρ'', .fellThrough) ∧
      SortInv ρ'' (la.set t.toNat x) lt n w lo mid hi (t + 1) := by
  have hbody : sortCopyBody =
      (.seq (.if_ (.ult (.var "t") (.stdVecLen "tmp"))
                (.vecSet "a" (.var "t")
                  (.stdVecAt "tmp" (.var "t")))
                .fail)
        (.assign "t" (.uadd (.var "t") (.lit (.u64 1))))) := rfl
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hcT : evalExpr (.ult (.var "t") (.stdVecLen "tmp")) ρ =
      .ok (.b true) := by
    have h := sortCopyGuard_eval ρ la lt n w lo mid hi t
      ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hlent
    rwa [decide_eq_true hltT] at h
  have hrT := sortCopyRead_hit ρ la lt n w lo mid hi t x
    ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hgetT
  have hvec : evalProgStmt prog F
      (.vecSet "a" (.var "t") (.stdVecAt "tmp" (.var "t"))) ρ =
      .ok (ρ', .fellThrough) :=
    VecMergeRuns.evalProgStmt_vecSet prog F "a" (.var "t")
      (.stdVecAt "tmp" (.var "t")) ρ t x la v ρ'
      (evalExpr_var_hit _ _ _ htt) hrT ha hgetA hwr
  have hwrite := ((evalProgStmt_if_true prog F _ _ .fail _ hcT).trans hvec)
  have hinv' : SortInv ρ' (la.set t.toNat x) lt n w lo mid hi t :=
    ⟨by rw [envLookup_update_hit _ _ _ _ hwr],
     by rw [envLookup_update_miss _ _ _ _ _
       (show ("tmp" : String) ≠ "a" by decide) hwr]; exact htmp,
     by rw [envLookup_update_miss _ _ _ _ _
       (show ("n" : String) ≠ "a" by decide) hwr]; exact hn,
     by rw [envLookup_update_miss _ _ _ _ _
       (show ("width" : String) ≠ "a" by decide) hwr]; exact hw,
     by rw [envLookup_update_miss _ _ _ _ _
       (show ("lo" : String) ≠ "a" by decide) hwr]; exact hlo,
     by rw [envLookup_update_miss _ _ _ _ _
       (show ("mid" : String) ≠ "a" by decide) hwr]; exact hmid,
     by rw [envLookup_update_miss _ _ _ _ _
       (show ("hi" : String) ≠ "a" by decide) hwr]; exact hhi,
     by rw [envLookup_update_miss _ _ _ _ _
       (show ("t" : String) ≠ "a" by decide) hwr]; exact htt⟩
  obtain ⟨hincr, hinv''⟩ :=
    copyIncrT prog F ρ' ρ'' (la.set t.toNat x) lt n w lo mid hi t
      hinv' hu
  rw [hbody]
  exact ⟨(evalProgStmt_seq_fallthrough prog F _ _ _ _ hwrite).trans
    hincr, hinv''⟩

/-- Copy-back body miss (short `tmp`): loud abort. -/
theorem sortCopyBody_miss (prog : Prog) (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64)
    (hltT : ¬ t.toNat < lt.length) :
    evalProgStmt prog F sortCopyBody ρ = .error .AssertFail := by
  have hbody : sortCopyBody =
      (.seq (.if_ (.ult (.var "t") (.stdVecLen "tmp"))
                (.vecSet "a" (.var "t")
                  (.stdVecAt "tmp" (.var "t")))
                .fail)
        (.assign "t" (.uadd (.var "t") (.lit (.u64 1))))) := rfl
  have hcT : evalExpr (.ult (.var "t") (.stdVecLen "tmp")) ρ =
      .ok (.b false) := by
    have h := sortCopyGuard_eval ρ la lt n w lo mid hi t hinv hlent
    rwa [decide_eq_false hltT] at h
  have hfail := (evalProgStmt_if_false prog F _
      (.vecSet "a" (.var "t") (.stdVecAt "tmp" (.var "t"))) _ _ hcT).trans
    (VecMergeRuns.evalProgStmt_fail prog F _)
  rw [hbody]
  exact evalProgStmt_seq_err prog F _ _ _ _ hfail

/-- Copy-back ok soundness (taken steps always hit: `t < hi`
    keeps both reads live). -/
theorem sortCopy_ok (prog : Prog) (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (la' : List (BitVec 32)) (t' : Nat)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hhi_la : hi.toNat ≤ la.length) (hhi_lt : hi.toNat ≤ lt.length)
    (ht_le : t.toNat ≤ hi.toNat)
    (hF : (hi.toNat - t.toNat) + 1 ≤ F)
    (hfwd : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat hi.toNat =
      .ok (la', t')) :
    ∃ ρ', evalProgStmt prog F sortCopyBack ρ =
      .ok (ρ', .fellThrough) ∧
      SortInv ρ' la' lt n w lo mid hi (BitVec.ofNat 64 t') := by
  induction F generalizing ρ la lt n w lo mid hi t la' t' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hT : t.toNat < hi.toNat
    · have hcond : evalExpr (.ult (.var "t") (.var "hi")) ρ =
          .ok (.b true) := by
        have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t hinv
        rwa [decide_eq_true hT] at h
      have hM : (hi.toNat - t.toNat) =
          ((hi.toNat - t.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetT : lt[t.toNat]? = some lt[t.toNat] :=
        List.getElem?_eq_getElem
          (Nat.lt_of_lt_of_le hT hhi_lt)
      have hgetA : la[t.toNat]? = some la[t.toNat] :=
        List.getElem?_eq_getElem
          (Nat.lt_of_lt_of_le hT hhi_la)
      have hfwdT : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          ((hi.toNat - t.toNat) - 1)
          (t.toNat + 1) hi.toNat = .ok (la', t') := by
        have h := hfwd
        simp only [sortCopyFwd, dite_eq_left hT, hgetT, hgetA] at h
        exact h
      obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
      obtain ⟨ρ', hwr⟩ := envUpdate_some_of_lookup ρ "a"
        (.stdVecVal la) (.stdVecVal (la.set t.toNat lt[t.toNat])) ha
      have htt' : envLookup ρ' "t" = some (.u64 t) := by
        rw [envLookup_update_miss _ _ _ _ _
          (show ("t" : String) ≠ "a" by decide) hwr]
        exact htt
      obtain ⟨ρ'', hu⟩ := envUpdate_some_of_lookup ρ' "t"
        (.u64 t) (.u64 (t + 1)) htt'
      obtain ⟨heval, hinv'⟩ := sortCopyBody_hit prog F ρ ρ' ρ''
        la lt n w lo mid hi t lt[t.toNat] la[t.toNat]
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hlent
        hgetT hgetA (Nat.lt_of_lt_of_le hT hhi_lt) hwr hu
      have hloop : evalProgStmt prog (F + 1) sortCopyBack ρ =
          evalProgStmt prog F sortCopyBack ρ'' := by
        simp only [sortCopyBack,
          evalProgStmt_while_true prog F _ _ _ hcond, heval]
      have h1t : (t + 1).toNat = t.toNat + 1 :=
        bv64_succ_toNat t _ hT (by omega)
      have hlena' : (la.set t.toNat lt[t.toNat]).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlena
      have hhi_la' : hi.toNat ≤
          (la.set t.toNat lt[t.toNat]).length := by
        rw [List.length_set]; exact hhi_la
      have ht_le' : (t + 1).toNat ≤ hi.toNat := by omega
      have hF' : (hi.toNat - (t + 1).toNat) + 1 ≤ F := by omega
      have hfwd' : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          (hi.toNat - (t + 1).toNat) ((t + 1).toNat) hi.toNat =
          .ok (la', t') := by
        have hM' : (hi.toNat - t.toNat) - 1 =
            (hi.toNat - (t + 1).toNat) := by omega
        rw [← h1t, hM'] at hfwdT
        exact hfwdT
      rw [hloop]
      exact ih _ _ _ _ _ _ _ _ _ _ _ hinv' hlent hlena'
        hhi_la' hhi_lt ht_le' hF' hfwd'
    · have hcond : evalExpr (.ult (.var "t") (.var "hi")) ρ =
          .ok (.b false) := by
        have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t hinv
        rwa [decide_eq_false hT] at h
      have hfwd0 : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat
          hi.toNat = .ok (la, t.toNat) := by
        match hm : (hi.toNat - t.toNat) with
        | 0 => simp only [sortCopyFwd]
        | _ + 1 => simp only [sortCopyFwd, dite_eq_right hT]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hexit : evalProgStmt prog (F + 1) sortCopyBack ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog _ _ _ _ hcond
      refine ⟨_, hexit, ?_⟩
      rwa [bv64_ofNat_toNat t]

/-- Copy-back err soundness. -/
theorem sortCopy_err (prog : Prog) (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (e : Panic)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hhi_la : hi.toNat ≤ la.length) (hhi_lt : hi.toNat ≤ lt.length)
    (ht_le : t.toNat ≤ hi.toNat)
    (hF : (hi.toNat - t.toNat) + 1 ≤ F)
    (hfwd : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat hi.toNat =
      .error e) :
    evalProgStmt prog F sortCopyBack ρ = .error e := by
  induction F generalizing ρ la lt n w lo mid hi t e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hT : t.toNat < hi.toNat
    · have hcond : evalExpr (.ult (.var "t") (.var "hi")) ρ =
          .ok (.b true) := by
        have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t hinv
        rwa [decide_eq_true hT] at h
      have hM : (hi.toNat - t.toNat) =
          ((hi.toNat - t.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetT : lt[t.toNat]? = some lt[t.toNat] :=
        List.getElem?_eq_getElem
          (Nat.lt_of_lt_of_le hT hhi_lt)
      have hgetA : la[t.toNat]? = some la[t.toNat] :=
        List.getElem?_eq_getElem
          (Nat.lt_of_lt_of_le hT hhi_la)
      have hfwdT : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          ((hi.toNat - t.toNat) - 1)
          (t.toNat + 1) hi.toNat = .error e := by
        have h := hfwd
        simp only [sortCopyFwd, dite_eq_left hT, hgetT, hgetA] at h
        exact h
      obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
      obtain ⟨ρ', hwr⟩ := envUpdate_some_of_lookup ρ "a"
        (.stdVecVal la) (.stdVecVal (la.set t.toNat lt[t.toNat])) ha
      have htt' : envLookup ρ' "t" = some (.u64 t) := by
        rw [envLookup_update_miss _ _ _ _ _
          (show ("t" : String) ≠ "a" by decide) hwr]
        exact htt
      obtain ⟨ρ'', hu⟩ := envUpdate_some_of_lookup ρ' "t"
        (.u64 t) (.u64 (t + 1)) htt'
      obtain ⟨heval, hinv'⟩ := sortCopyBody_hit prog F ρ ρ' ρ''
        la lt n w lo mid hi t lt[t.toNat] la[t.toNat]
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hlent
        hgetT hgetA (Nat.lt_of_lt_of_le hT hhi_lt) hwr hu
      have herr : evalProgStmt prog (F + 1) sortCopyBack ρ =
          evalProgStmt prog F sortCopyBack ρ'' := by
        simp only [sortCopyBack,
          evalProgStmt_while_true prog F _ _ _ hcond, heval]
      have h1t : (t + 1).toNat = t.toNat + 1 :=
        bv64_succ_toNat t _ hT (by omega)
      have hlena' : (la.set t.toNat lt[t.toNat]).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlena
      have hhi_la' : hi.toNat ≤
          (la.set t.toNat lt[t.toNat]).length := by
        rw [List.length_set]; exact hhi_la
      have ht_le' : (t + 1).toNat ≤ hi.toNat := by omega
      have hF' : (hi.toNat - (t + 1).toNat) + 1 ≤ F := by omega
      have hfwd' : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          (hi.toNat - (t + 1).toNat) ((t + 1).toNat) hi.toNat =
          .error e := by
        have hM' : (hi.toNat - t.toNat) - 1 =
            (hi.toNat - (t + 1).toNat) := by omega
        rw [← h1t, hM'] at hfwdT
        exact hfwdT
      rw [herr]
      exact ih _ _ _ _ _ _ _ _ _ _ hinv' hlent hlena'
        hhi_la' hhi_lt ht_le' hF' hfwd'
    · have hcond : evalExpr (.ult (.var "t") (.var "hi")) ρ =
          .ok (.b false) := by
        have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t hinv
        rwa [decide_eq_false hT] at h
      have hfwd0 : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat
          hi.toNat = .ok (la, t.toNat) := by
        match hm : (hi.toNat - t.toNat) with
        | 0 => simp only [sortCopyFwd]
        | _ + 1 => simp only [sortCopyFwd, dite_eq_right hT]
      rw [hfwd0] at hfwd
      cases hfwd

/-- Copy-back preserves `a` length (sets only). -/
theorem sortCopyFwd_length (lt la : List (BitVec 32))
    (F t hi : Nat) (la' : List (BitVec 32)) (t' : Nat)
    (h : sortCopyFwd lt la F t hi = .ok (la', t')) :
    la'.length = la.length := by
  induction F generalizing la t la' t' with
  | zero =>
    simp only [sortCopyFwd, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ F ih =>
    by_cases hT : t < hi
    · simp only [sortCopyFwd, dite_eq_left hT] at h
      match hT' : lt[t]? with
      | none => simp [hT'] at h
      | some x =>
        simp only [hT'] at h
        match hA : la[t]? with
        | none => simp [hA] at h
        | some _ =>
          simp only [hA] at h
          have hlen := ih _ _ _ _ h
          exact hlen.trans List.length_set
    · simp only [sortCopyFwd, dite_eq_right hT, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-! ## Segment loop -/

theorem sortSegGuardLo_eval (ρ : Env) (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t) :
    evalExpr (.ult (.var "lo") (.var "n")) ρ =
      .ok (.b (decide (lo.toNat < n.toNat))) := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hnv : evalExpr (.var "lo") ρ = .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ hlo
  have hmv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
    evalExpr_var_hit _ _ _ hn
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
  rw [VecMergeRuns.bv64_ult_toNat lo n] at hult
  exact hult

/-- Clamp-`mid` step: `mid := min mid n` (the caller supplies
    `mid = lo + w`). -/
theorem sortClampMid_step (prog : Prog) (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hmid_eq : mid.toNat = lo.toNat + w.toNat) :
    ∃ ρ' mid', evalProgStmt prog F sortClampMid ρ =
      .ok (ρ', .fellThrough) ∧
      SortInv ρ' la lt n w lo mid' hi t ∧
      mid'.toNat = Nat.min (lo.toNat + w.toNat) n.toNat := by
  have hbody : sortClampMid =
      (.if_ (.ult (.var "n") (.var "mid"))
        (.assign "mid" (.var "n")) .skip) := rfl
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hguard : evalExpr (.ult (.var "n") (.var "mid")) ρ =
      .ok (.b (decide (n.toNat < lo.toNat + w.toNat))) := by
    have hnv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ hn
    have hmv : evalExpr (.var "mid") ρ = .ok (.u64 mid) :=
      evalExpr_var_hit _ _ _ hmid
    have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
    rw [VecMergeRuns.bv64_ult_toNat n mid, hmid_eq] at hult
    exact hult
  by_cases hC : n.toNat < lo.toNat + w.toNat
  · have hcond : evalExpr (.ult (.var "n") (.var "mid")) ρ =
        .ok (.b true) := by
      rwa [decide_eq_true hC] at hguard
    obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "mid"
      (.u64 mid) (.u64 n) hmid
    have hassign : evalProgStmt prog F
        (.assign "mid" (.var "n")) ρ = .ok (ρ', .fellThrough) := by
      have hv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
        evalExpr_var_hit _ _ _ hn
      have hstmt := evalStmtFuel_assign F _ _ _ _ _ hv hu
      simpa [evalProgStmt] using hstmt
    refine ⟨ρ', n, ?_, ?_, ?_⟩
    · rw [hbody]
      exact (evalProgStmt_if_true prog F _ _ _ _ hcond).trans hassign
    · exact sortInv_update_mid _ _ _ _ _ _ _ _ _ _ _
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hu
    · show n.toNat = Nat.min (lo.toNat + w.toNat) n.toNat
      exact (Nat.min_eq_right (Nat.le_of_lt hC)).symm
  · have hcond : evalExpr (.ult (.var "n") (.var "mid")) ρ =
        .ok (.b false) := by
      rwa [decide_eq_false hC] at hguard
    refine ⟨ρ, mid, ?_, ?_, ?_⟩
    · rw [hbody]
      exact (evalProgStmt_if_false prog F _ _ _ _ hcond).trans
        (evalProgStmt_skip prog F ρ)
    · exact ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
    · show mid.toNat = Nat.min (lo.toNat + w.toNat) n.toNat
      rw [hmid_eq]
      exact (Nat.min_eq_left (Nat.le_of_not_gt hC)).symm

/-- Clamp-`hi` step: `hi := min hi n` (the caller supplies
    `hi = (lo + w) + w`). -/
theorem sortClampHi_step (prog : Prog) (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hhi_eq : hi.toNat = lo.toNat + w.toNat + w.toNat) :
    ∃ ρ' hi', evalProgStmt prog F sortClampHi ρ =
      .ok (ρ', .fellThrough) ∧
      SortInv ρ' la lt n w lo mid hi' t ∧
      hi'.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat := by
  have hbody : sortClampHi =
      (.if_ (.ult (.var "n") (.var "hi"))
        (.assign "hi" (.var "n")) .skip) := rfl
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hguard : evalExpr (.ult (.var "n") (.var "hi")) ρ =
      .ok (.b (decide (n.toNat < lo.toNat + w.toNat + w.toNat))) := by
    have hnv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ hn
    have hmv : evalExpr (.var "hi") ρ = .ok (.u64 hi) :=
      evalExpr_var_hit _ _ _ hhi
    have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
    rw [VecMergeRuns.bv64_ult_toNat n hi, hhi_eq] at hult
    exact hult
  by_cases hC : n.toNat < lo.toNat + w.toNat + w.toNat
  · have hcond : evalExpr (.ult (.var "n") (.var "hi")) ρ =
        .ok (.b true) := by
      rwa [decide_eq_true hC] at hguard
    obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "hi"
      (.u64 hi) (.u64 n) hhi
    have hassign : evalProgStmt prog F
        (.assign "hi" (.var "n")) ρ = .ok (ρ', .fellThrough) := by
      have hv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
        evalExpr_var_hit _ _ _ hn
      have hstmt := evalStmtFuel_assign F _ _ _ _ _ hv hu
      simpa [evalProgStmt] using hstmt
    refine ⟨ρ', n, ?_, ?_, ?_⟩
    · rw [hbody]
      exact (evalProgStmt_if_true prog F _ _ _ _ hcond).trans hassign
    · exact sortInv_update_hi _ _ _ _ _ _ _ _ _ _ _
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hu
    · show n.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat
      exact (Nat.min_eq_right (Nat.le_of_lt hC)).symm
  · have hcond : evalExpr (.ult (.var "n") (.var "hi")) ρ =
        .ok (.b false) := by
      rwa [decide_eq_false hC] at hguard
    refine ⟨ρ, hi, ?_, ?_, ?_⟩
    · rw [hbody]
      exact (evalProgStmt_if_false prog F _ _ _ _ hcond).trans
        (evalProgStmt_skip prog F ρ)
    · exact ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
    · show hi.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat
      rw [hhi_eq]
      exact (Nat.min_eq_left (Nat.le_of_not_gt hC)).symm

/-- Callee resolution in the sort program. -/
theorem findFunc_mergeRuns :
    findFunc vecMergeSortProg VecMergeRuns.mergeRunsName = some VecMergeRuns.mergeRunsFunc :=
  findFunc_hit VecMergeRuns.mergeRunsFunc [vecMergeSortFunc]

/-- Segment clamps prefix (model-independent: bounds + clamps only,
    shared by the ok body-step and the err induction). -/
theorem sortSegClamps_step (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hLo : lo.toNat < n.toNat) :
    ∃ ρ₁ ρ₂ ρ₃ ρ₄ mid₂ hi₂,
      evalProgStmt vecMergeSortProg F
        (.assign "mid" (.uadd (.var "lo") (.var "width"))) ρ =
        .ok (ρ₁, .fellThrough) ∧
      evalProgStmt vecMergeSortProg F sortClampMid ρ₁ =
        .ok (ρ₂, .fellThrough) ∧
      evalProgStmt vecMergeSortProg F
        (.assign "hi"
          (.uadd (.uadd (.var "lo") (.var "width"))
            (.var "width"))) ρ₂ = .ok (ρ₃, .fellThrough) ∧
      evalProgStmt vecMergeSortProg F sortClampHi ρ₃ =
        .ok (ρ₄, .fellThrough) ∧
      SortInv ρ₄ la lt n w lo mid₂ hi₂ t₀ ∧
      mid₂.toNat = Nat.min (lo.toNat + w.toNat) n.toNat ∧
      hi₂.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat := by
  obtain ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ := hinv
  have hadd1 : (lo + w).toNat = lo.toNat + w.toNat :=
    bv64_add_toNat lo w (by omega)
  have heval_mw : evalExpr (.uadd (.var "lo") (.var "width")) ρ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo) (evalExpr_var_hit _ _ _ hw)
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "mid"
    (.u64 mid₀) (.u64 (lo + w)) hmid₀
  have hstep₁ : evalProgStmt vecMergeSortProg F
      (.assign "mid" (.uadd (.var "lo") (.var "width"))) ρ =
      .ok (ρ₁, .fellThrough) := by
    have hstmt := evalStmtFuel_assign F _ _ _ _ _ heval_mw hu₁
    simpa [evalProgStmt] using hstmt
  have hinv₁ : SortInv ρ₁ la lt n w lo (lo + w) hi₀ t₀ :=
    sortInv_update_mid _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ hu₁
  obtain ⟨ρ₂, mid₂, heval₂, hinv₂, hmid₂⟩ :=
    sortClampMid_step vecMergeSortProg F ρ₁ la lt n w lo (lo + w)
      hi₀ t₀ hinv₁ hadd1
  obtain ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ := hinv₂
  have heval_lw : evalExpr (.uadd (.var "lo") (.var "width")) ρ₂ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo₂) (evalExpr_var_hit _ _ _ hw₂)
  have heval_ww : evalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₂ =
      .ok (.u64 ((lo + w) + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _ heval_lw
      (evalExpr_var_hit _ _ _ hw₂)
  have hadd2 : ((lo + w) + w).toNat =
      lo.toNat + w.toNat + w.toNat := by
    have h2 : ((lo + w) + w).toNat = (lo + w).toNat + w.toNat :=
      bv64_add_toNat _ _ (by omega)
    omega
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "hi"
    (.u64 hi₀) (.u64 ((lo + w) + w)) hhi₂
  have hstep₃ : evalProgStmt vecMergeSortProg F
      (.assign "hi"
        (.uadd (.uadd (.var "lo") (.var "width")) (.var "width"))) ρ₂ =
      .ok (ρ₃, .fellThrough) := by
    have hstmt := evalStmtFuel_assign F _ _ _ _ _ heval_ww hu₃
    simpa [evalProgStmt] using hstmt
  have hinv₃ : SortInv ρ₃ la lt n w lo mid₂ ((lo + w) + w) t₀ :=
    sortInv_update_hi _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ hu₃
  obtain ⟨ρ₄, hi₂, heval₄, hinv₄, hhi₂⟩ :=
    sortClampHi_step vecMergeSortProg F ρ₃ la lt n w lo mid₂
      ((lo + w) + w) t₀ hinv₃ hadd2
  exact ⟨ρ₁, ρ₂, ρ₃, ρ₄, mid₂, hi₂, hstep₁, heval₂, hstep₃,
    heval₄, hinv₄, hmid₂, hhi₂⟩

/-- Segment-body step: bounds, clamps, the call, copy-back,
    advance. The model equations for the call and the copy come
    from the unrolled segment forward (supplied as premises). -/
theorem sortSegBody_step (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (la_next : List (BitVec 32)) (lt' : List (BitVec 32))
    (t_next : Nat)
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hLo : lo.toNat < n.toNat)
    (hF1 : 1 ≤ F)
    (hF : 2 * (n.toNat - lo.toNat) + 8 ≤ F)
    (hmr : VecMergeRuns.mergeRunsFwd la lt lo.toNat
      (Nat.min (lo.toNat + w.toNat) n.toNat)
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) =
      .ok (.stdVecVal lt'))
    (hcp : sortCopyFwd lt' la
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat - lo.toNat)
      lo.toNat
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) =
      .ok (la_next, t_next)) :
    ∃ ρ' lo' mid' hi' t',
      evalProgStmt vecMergeSortProg F sortSegBody ρ =
        .ok (ρ', .fellThrough) ∧
      SortInv ρ' la_next lt' n w lo' mid' hi' t' ∧
      lo'.toNat = lo.toNat + w.toNat + w.toNat ∧
      lt'.length = lt.length ∧ la_next.length = la.length := by
  obtain ⟨G, rfl, _⟩ := fuel_step_down 0 hF1
  obtain ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ := hinv
  -- `mid ← lo + width`.
  have hadd1 : (lo + w).toNat = lo.toNat + w.toNat :=
    bv64_add_toNat lo w (by omega)
  have heval_mw : evalExpr (.uadd (.var "lo") (.var "width")) ρ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo) (evalExpr_var_hit _ _ _ hw)
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "mid"
    (.u64 mid₀) (.u64 (lo + w)) hmid₀
  have hstep₁ : evalProgStmt vecMergeSortProg (G + 1)
      (.assign "mid" (.uadd (.var "lo") (.var "width"))) ρ =
      .ok (ρ₁, .fellThrough) := by
    have hstmt := evalStmtFuel_assign (G + 1) _ _ _ _ _ heval_mw hu₁
    simpa [evalProgStmt] using hstmt
  have hinv₁ : SortInv ρ₁ la lt n w lo (lo + w) hi₀ t₀ :=
    sortInv_update_mid _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ hu₁
  -- Clamp `mid`.
  obtain ⟨ρ₂, mid₂, heval₂, hinv₂, hmid₂⟩ :=
    sortClampMid_step vecMergeSortProg (G + 1) ρ₁ la lt n w lo (lo + w) hi₀ t₀
      hinv₁ hadd1
  obtain ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ := hinv₂
  -- `hi ← (lo + width) + width`.
  have heval_lw : evalExpr (.uadd (.var "lo") (.var "width")) ρ₂ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo₂) (evalExpr_var_hit _ _ _ hw₂)
  have heval_ww : evalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₂ =
      .ok (.u64 ((lo + w) + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _ heval_lw
      (evalExpr_var_hit _ _ _ hw₂)
  have hadd2 : ((lo + w) + w).toNat =
      lo.toNat + w.toNat + w.toNat := by
    have h2 : ((lo + w) + w).toNat = (lo + w).toNat + w.toNat :=
      bv64_add_toNat _ _ (by omega)
    omega
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "hi"
    (.u64 hi₀) (.u64 ((lo + w) + w)) hhi₂
  have hstep₃ : evalProgStmt vecMergeSortProg (G + 1)
      (.assign "hi"
        (.uadd (.uadd (.var "lo") (.var "width")) (.var "width"))) ρ₂ =
      .ok (ρ₃, .fellThrough) := by
    have hstmt := evalStmtFuel_assign (G + 1) _ _ _ _ _ heval_ww hu₃
    simpa [evalProgStmt] using hstmt
  have hinv₃ : SortInv ρ₃ la lt n w lo mid₂ ((lo + w) + w) t₀ :=
    sortInv_update_hi _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ hu₃
  -- Clamp `hi`.
  obtain ⟨ρ₄, hi₂, heval₄, hinv₄, hhi₂⟩ :=
    sortClampHi_step vecMergeSortProg (G + 1) ρ₃ la lt n w lo mid₂
      ((lo + w) + w) t₀ hinv₃ hadd2
  obtain ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩ := hinv₄
  -- Clamp facts.
  have hmid_le_n : mid₂.toNat ≤ n.toNat := by
    rw [hmid₂]; exact Nat.min_le_right _ _
  have hhi_le_n : hi₂.toNat ≤ n.toNat := by
    rw [hhi₂]; exact Nat.min_le_right _ _
  have hlo_mid : lo.toNat ≤ mid₂.toNat := by
    rw [hmid₂]
    exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, Nat.le_of_lt hLo⟩
  have hmid_hi : mid₂.toNat ≤ hi₂.toNat := by
    rw [hhi₂]
    refine Nat.le_min.mpr ⟨?_, hmid_le_n⟩
    have h1 : mid₂.toNat ≤ lo.toNat + w.toNat := by
      rw [hmid₂]; exact Nat.min_le_left _ _
    omega
  have hhi_n : hi₂.toNat ≤ n.toNat := hhi_le_n
  have hmid_le : mid₂.toNat ≤ la.length := by omega
  have hhi_le : hi₂.toNat ≤ la.length := by omega
  have hlo_lt : lo.toNat ≤ lt.length := by omega
  -- The call.
  have hargs : lookupArgs ρ₄ ["a", "tmp", "lo", "mid", "hi"] =
      some [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
        .u64 hi₂] := by
    simp [lookupArgs, ha₄, htmp₄, hlo₄, hmid₄, hhi₄]
  have hF_cal : ((mid₂.toNat - lo.toNat) + (hi₂.toNat - lo.toNat)) + 1 ≤
      G := by
    omega
  have hcall_fwd := VecMergeRuns.evalProgFunc_mergeRuns vecMergeSortProg G la lt
    lo mid₂ hi₂ hlent hlo_mid hmid_hi hmid_le hhi_le hlo_lt hF_cal
  rw [hmid₂, hhi₂] at hcall_fwd
  have hcall : evalProgFunc vecMergeSortProg G VecMergeRuns.mergeRunsFunc
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂, .u64 hi₂] =
      .ok (.stdVecVal lt') := by
    rw [hcall_fwd]; exact hmr
  have hstep_call : evalProgStmt vecMergeSortProg (G + 1) sortSegCall
      ρ₄ = .ok (envExtend ρ₄ "tmp" (.stdVecVal lt'), .fellThrough) :=
    evalProgStmt_callProg_ok vecMergeSortProg G "tmp" VecMergeRuns.mergeRunsName
      ["a", "tmp", "lo", "mid", "hi"] ρ₄
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂, .u64 hi₂]
      VecMergeRuns.mergeRunsFunc (.stdVecVal lt') hargs findFunc_mergeRuns hcall
  have hlen' : lt'.length = lt.length := by
    have hmr' : VecMergeRuns.mergeRunsFwd la lt lo.toNat mid₂.toNat hi₂.toNat =
        .ok (.stdVecVal lt') := by
      rwa [← hmid₂, ← hhi₂] at hmr
    exact VecMergeRuns.mergeRunsFwd_length la lt lo.toNat mid₂.toNat hi₂.toNat lt'
      hlo_mid hmid_hi hlo_lt hmr'
  have hlent' : lt'.length < 2 ^ 64 := by rw [hlen']; exact hlent
  have hinv₅ : SortInv (envExtend ρ₄ "tmp" (.stdVecVal lt')) la lt'
      n w lo mid₂ hi₂ t₀ :=
    sortInv_extend_tmp ρ₄ la lt lt' n w lo mid₂ hi₂ t₀
      ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩
  -- `t ← lo`.
  obtain ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ := hinv₅
  have heval_tlo : evalExpr (.var "lo")
      (envExtend ρ₄ "tmp" (.stdVecVal lt')) = .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ hlo₅
  obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup
    (envExtend ρ₄ "tmp" (.stdVecVal lt')) "t" (.u64 t₀) (.u64 lo) htt₅
  have hstep_t : evalProgStmt vecMergeSortProg (G + 1)
      (.assign "t" (.var "lo"))
      (envExtend ρ₄ "tmp" (.stdVecVal lt')) =
      .ok (ρ₆, .fellThrough) := by
    have hstmt := evalStmtFuel_assign (G + 1) _ _ _ _ _ heval_tlo hu₆
    simpa [evalProgStmt] using hstmt
  have hinv₆ : SortInv ρ₆ la lt' n w lo mid₂ hi₂ lo :=
    sortInv_update_t _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ hu₆
  -- Copy-back.
  have hhi_lt' : hi₂.toNat ≤ lt'.length := by omega
  have hF_copy : (hi₂.toNat - lo.toNat) + 1 ≤ G + 1 := by omega
  have hcp' : sortCopyFwd lt' la (hi₂.toNat - lo.toNat) lo.toNat
      hi₂.toNat = .ok (la_next, t_next) := by
    rwa [← hhi₂] at hcp
  obtain ⟨ρ₇, heval_copy, hinv₇⟩ := sortCopy_ok vecMergeSortProg
    (G + 1) ρ₆
    la lt' n w lo mid₂ hi₂ lo la_next t_next hinv₆ hlent'
    hlena hhi_le hhi_lt' (by omega) hF_copy hcp'
  obtain ⟨ha₇, htmp₇, hnL₇, hw₇, hlo₇, hmid₇, hhi₇, htt₇⟩ := hinv₇
  -- `lo ← (lo + width) + width`.
  have heval_lw7 : evalExpr (.uadd (.var "lo") (.var "width")) ρ₇ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo₇) (evalExpr_var_hit _ _ _ hw₇)
  have heval_ww7 : evalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₇ =
      .ok (.u64 ((lo + w) + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _ heval_lw7
      (evalExpr_var_hit _ _ _ hw₇)
  obtain ⟨ρ₈, hu₈⟩ := envUpdate_some_of_lookup ρ₇ "lo"
    (.u64 lo) (.u64 ((lo + w) + w)) hlo₇
  have hstep_lo : evalProgStmt vecMergeSortProg (G + 1)
      (.assign "lo"
        (.uadd (.uadd (.var "lo") (.var "width")) (.var "width"))) ρ₇ =
      .ok (ρ₈, .fellThrough) := by
    have hstmt := evalStmtFuel_assign (G + 1) _ _ _ _ _ heval_ww7 hu₈
    simpa [evalProgStmt] using hstmt
  have hinv₈ : SortInv ρ₈ la_next lt' n w ((lo + w) + w) mid₂ hi₂
      (BitVec.ofNat 64 t_next) :=
    sortInv_update_lo _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₇, htmp₇, hnL₇, hw₇, hlo₇, hmid₇, hhi₇, htt₇⟩ hu₈
  -- Assemble.
  have hbody : sortSegBody =
      (.seq (.assign "mid" (.uadd (.var "lo") (.var "width")))
        (.seq sortClampMid
          (.seq (.assign "hi"
                  (.uadd (.uadd (.var "lo") (.var "width"))
                    (.var "width")))
            (.seq sortClampHi
              (.seq sortSegCall
                (.seq (.assign "t" (.var "lo"))
                  (.seq sortCopyBack
                    (.assign "lo"
                      (.uadd (.uadd (.var "lo") (.var "width"))
                        (.var "width")))))))))) := rfl
  have hlen_copy : la_next.length = la.length :=
    sortCopyFwd_length lt' la
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat - lo.toNat)
      lo.toNat
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat)
      la_next t_next hcp
  refine ⟨ρ₈, ((lo + w) + w), mid₂, hi₂, (BitVec.ofNat 64 t_next),
    ?_, hinv₈, hadd2, hlen', hlen_copy⟩
  rw [hbody,
    evalProgStmt_seq_fallthrough _ (G + 1) _ _ _ _ hstep₁,
    evalProgStmt_seq_fallthrough _ (G + 1) _ _ _ _ heval₂,
    evalProgStmt_seq_fallthrough _ (G + 1) _ _ _ _ hstep₃,
    evalProgStmt_seq_fallthrough _ (G + 1) _ _ _ _ heval₄,
    evalProgStmt_seq_fallthrough _ (G + 1) _ _ _ _ hstep_call,
    evalProgStmt_seq_fallthrough _ (G + 1) _ _ _ _ hstep_t,
    evalProgStmt_seq_fallthrough _ (G + 1) _ _ _ _ heval_copy]
  exact hstep_lo

/-- Segment-loop ok soundness: the first genuine calls-in-loops
    induction (the body calls `merge_runs` every iteration). -/
theorem sortSeg_ok (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (la' lt' : List (BitVec 32))
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * (n.toNat - lo.toNat) + 9 ≤ F)
    (hfwd : sortSegFwd la lt F w.toNat lo.toNat n.toNat =
      .ok (la', lt')) :
    ∃ ρ' lo' mid' hi' t',
      evalProgStmt vecMergeSortProg F sortSegLoop ρ =
        .ok (ρ', .fellThrough) ∧
      SortInv ρ' la' lt' n w lo' mid' hi' t' := by
  induction F generalizing ρ la lt n w lo mid₀ hi₀ t₀ la' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hLo : lo.toNat < n.toNat
    · have hcond : evalExpr (.ult (.var "lo") (.var "n")) ρ =
          .ok (.b true) := by
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_true hLo] at h
      simp only [sortSegFwd, dite_eq_left hLo] at hfwd
      match hmr : VecMergeRuns.mergeRunsFwd la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
      | .error e => simp [hmr] at hfwd
      | .ok v =>
        obtain ⟨lt₁, rfl⟩ := VecMergeRuns.mergeRunsFwd_ok_shape la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) v hmr
        simp only [hmr] at hfwd
        match hcp : sortCopyFwd lt₁ la
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat -
              lo.toNat)
            lo.toNat
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
        | .error e => simp [hcp] at hfwd
        | .ok (la₁, t₁) =>
          simp only [hcp] at hfwd
          obtain ⟨ρ₁, lo₁, mid₁, hi₁, t₁', heval_body, hinv₁,
              hlo₁eq, hlen₁', hlen_copy₁⟩ :=
            sortSegBody_step F ρ la lt n w lo mid₀ hi₀ t₀ la₁ lt₁ t₁
              hinv hn hlent hlena hlen62 htmp_ge hw1 hw_lt hLo
              (by omega) (by omega) hmr hcp
          have hlent₁ : lt₁.length < 2 ^ 64 := by
            rw [hlen₁']; exact hlent
          have hn₁ : n.toNat = la₁.length := by
            rw [hlen_copy₁]; exact hn
          have hlena₁ : la₁.length < 2 ^ 64 := by
            rw [hlen_copy₁]; exact hlena
          have hlen62₁ : la₁.length < 2 ^ 62 := by
            rw [hlen_copy₁]; exact hlen62
          have htmp_ge₁ : la₁.length ≤ lt₁.length := by
            rw [hlen_copy₁, hlen₁']; exact htmp_ge
          have hloop : evalProgStmt vecMergeSortProg (F + 1)
              sortSegLoop ρ =
              evalProgStmt vecMergeSortProg F sortSegLoop ρ₁ := by
            simp only [sortSegLoop,
              evalProgStmt_while_true vecMergeSortProg F _ _ _
                hcond, heval_body]
          have hF' : 2 * (n.toNat - lo₁.toNat) + 9 ≤ F := by omega
          have hfwd' : sortSegFwd la₁ lt₁ F w.toNat lo₁.toNat
              n.toNat = .ok (la', lt') := by
            rw [hlo₁eq]; exact hfwd
          rw [hloop]
          obtain ⟨ρ', lo', mid', hi', t', hev, hinv'⟩ :=
            ih _ _ _ _ _ _ _ _ _ _ _ hinv₁ hn₁ hlent₁ hlena₁ hlen62₁
              htmp_ge₁ hw1 hw_lt hF' hfwd'
          exact ⟨ρ', lo', mid', hi', t', hev, hinv'⟩
    · have hcond : evalExpr (.ult (.var "lo") (.var "n")) ρ =
          .ok (.b false) := by
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_false hLo] at h
      have hfwd0 : sortSegFwd la lt (F + 1) w.toNat lo.toNat
          n.toNat = .ok (la, lt) := by
        simp only [sortSegFwd, dite_eq_right hLo]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hexit : evalProgStmt vecMergeSortProg (F + 1) sortSegLoop
          ρ = .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false vecMergeSortProg _ _ _ _ hcond
      exact ⟨ρ, lo, mid₀, hi₀, t₀, hexit, hinv⟩

/-- Segment-loop err soundness. -/
theorem sortSeg_err (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (e : Panic)
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * (n.toNat - lo.toNat) + 9 ≤ F)
    (hfwd : sortSegFwd la lt F w.toNat lo.toNat n.toNat = .error e) :
    evalProgStmt vecMergeSortProg F sortSegLoop ρ = .error e := by
  induction F generalizing ρ la lt n w lo mid₀ hi₀ t₀ e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hLo : lo.toNat < n.toNat
    · have hcond : evalExpr (.ult (.var "lo") (.var "n")) ρ =
          .ok (.b true) := by
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_true hLo] at h
      have hF8 : 2 * (n.toNat - lo.toNat) + 8 ≤ F :=
        Nat.le_of_succ_le_succ hF
      obtain ⟨G, rfl, _⟩ :=
        fuel_step_down (2 * (n.toNat - lo.toNat) + 7) hF8
      obtain ⟨ρ₁, ρ₂, ρ₃, ρ₄, mid₂, hi₂, hstep₁, heval₂,
          hstep₃, heval₄, hinv₄, hmid₂, hhi₂⟩ :=
        sortSegClamps_step (G + 1) ρ la lt n w lo mid₀ hi₀ t₀ hinv hn
          hlent hlena hlen62 htmp_ge hw1 hw_lt hLo
      have hbody : sortSegBody =
          (.seq (.assign "mid" (.uadd (.var "lo") (.var "width")))
            (.seq sortClampMid
              (.seq (.assign "hi"
                      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")))
                (.seq sortClampHi
                  (.seq sortSegCall
                    (.seq (.assign "t" (.var "lo"))
                      (.seq sortCopyBack
                        (.assign "lo"
                          (.uadd (.uadd (.var "lo") (.var "width"))
                            (.var "width")))))))))) := rfl
      have hpre : evalProgStmt vecMergeSortProg (G + 1) sortSegBody
          ρ = evalProgStmt vecMergeSortProg (G + 1)
          (.seq sortSegCall
            (.seq (.assign "t" (.var "lo"))
              (.seq sortCopyBack
                (.assign "lo"
                  (.uadd (.uadd (.var "lo") (.var "width"))
                    (.var "width")))))) ρ₄ := by
        rw [hbody,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep₁,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ heval₂,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep₃,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ heval₄]
      obtain ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩ := hinv₄
      have hlo_mid : lo.toNat ≤ mid₂.toNat := by
        rw [hmid₂]
        exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, Nat.le_of_lt hLo⟩
      have hmid_hi : mid₂.toNat ≤ hi₂.toNat := by
        rw [hhi₂]
        refine Nat.le_min.mpr ⟨?_, ?_⟩
        · have h1 : mid₂.toNat ≤ lo.toNat + w.toNat := by
            rw [hmid₂]; exact Nat.min_le_left _ _
          omega
        · rw [hmid₂]; exact Nat.min_le_right _ _
      have hmid_le : mid₂.toNat ≤ la.length := by
        rw [hmid₂, hn]
        exact Nat.min_le_right _ _
      have hhi_le : hi₂.toNat ≤ la.length := by
        rw [hhi₂, hn]
        exact Nat.min_le_right _ _
      have hlo_lt : lo.toNat ≤ lt.length := by omega
      have hargs : lookupArgs ρ₄ ["a", "tmp", "lo", "mid", "hi"] =
          some [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
            .u64 hi₂] := by
        simp [lookupArgs, ha₄, htmp₄, hlo₄, hmid₄, hhi₄]
      have hF_cal : ((mid₂.toNat - lo.toNat) +
          (hi₂.toNat - lo.toNat)) + 1 ≤ G := by
        omega
      have hcall_fwd := VecMergeRuns.evalProgFunc_mergeRuns vecMergeSortProg G
        la lt lo mid₂ hi₂ hlent hlo_mid hmid_hi hmid_le hhi_le hlo_lt
        hF_cal
      rw [hmid₂, hhi₂] at hcall_fwd
      simp only [sortSegFwd, dite_eq_left hLo] at hfwd
      match hmr : VecMergeRuns.mergeRunsFwd la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
      | .error e' =>
        simp [hmr] at hfwd
        cases hfwd
        have hcall : evalProgFunc vecMergeSortProg G VecMergeRuns.mergeRunsFunc
            [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
              .u64 hi₂] = .error e := by
          rw [hcall_fwd]; exact hmr
        have hstep_call := evalProgStmt_callProg_err vecMergeSortProg
          G "tmp" VecMergeRuns.mergeRunsName ["a", "tmp", "lo", "mid", "hi"] ρ₄
          [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂, .u64 hi₂]
          VecMergeRuns.mergeRunsFunc e hargs findFunc_mergeRuns hcall
        have hfull : evalProgStmt vecMergeSortProg (G + 1)
            sortSegBody ρ = .error e := by
          rw [hpre]
          exact evalProgStmt_seq_err _ _ _ _ _ _ hstep_call
        have hloop : evalProgStmt vecMergeSortProg ((G + 1) + 1)
            sortSegLoop ρ = .error e := by
          simp only [sortSegLoop,
            evalProgStmt_while_true vecMergeSortProg (G + 1) _ _ _
              hcond, hfull]
        exact hloop
      | .ok v =>
        obtain ⟨lt₁, rfl⟩ := VecMergeRuns.mergeRunsFwd_ok_shape la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) v hmr
        simp only [hmr] at hfwd
        have hcall : evalProgFunc vecMergeSortProg G VecMergeRuns.mergeRunsFunc
            [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
              .u64 hi₂] = .ok (.stdVecVal lt₁) := by
          rw [hcall_fwd]; exact hmr
        have hstep_call : evalProgStmt vecMergeSortProg (G + 1)
            sortSegCall ρ₄ =
            .ok (envExtend ρ₄ "tmp" (.stdVecVal lt₁),
              .fellThrough) :=
          evalProgStmt_callProg_ok vecMergeSortProg G "tmp"
            VecMergeRuns.mergeRunsName ["a", "tmp", "lo", "mid", "hi"] ρ₄
            [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
              .u64 hi₂]
            VecMergeRuns.mergeRunsFunc (.stdVecVal lt₁) hargs findFunc_mergeRuns
            hcall
        have hlen₁' : lt₁.length = lt.length := by
          have hmr' : VecMergeRuns.mergeRunsFwd la lt lo.toNat mid₂.toNat
              hi₂.toNat = .ok (.stdVecVal lt₁) := by
            rwa [← hmid₂, ← hhi₂] at hmr
          exact VecMergeRuns.mergeRunsFwd_length la lt lo.toNat mid₂.toNat hi₂.toNat
            lt₁ hlo_mid hmid_hi hlo_lt hmr'
        have hlent₁ : lt₁.length < 2 ^ 64 := by
          rw [hlen₁']; exact hlent
        have hinv₅ : SortInv
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) la lt₁ n w lo mid₂
            hi₂ t₀ :=
          sortInv_extend_tmp ρ₄ la lt lt₁ n w lo mid₂ hi₂ t₀
            ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩
        obtain ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ :=
          hinv₅
        have heval_tlo : evalExpr (.var "lo")
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) = .ok (.u64 lo) :=
          evalExpr_var_hit _ _ _ hlo₅
        obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup
          (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) "t" (.u64 t₀)
          (.u64 lo) htt₅
        have hstep_t : evalProgStmt vecMergeSortProg (G + 1)
            (.assign "t" (.var "lo"))
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) =
            .ok (ρ₆, .fellThrough) := by
          have hstmt := evalStmtFuel_assign (G + 1) _ _ _ _ _
            heval_tlo hu₆
          simpa [evalProgStmt] using hstmt
        have hinv₆ : SortInv ρ₆ la lt₁ n w lo mid₂ hi₂ lo :=
          sortInv_update_t _ _ _ _ _ _ _ _ _ _ _
            ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ hu₆
        match hcp : sortCopyFwd lt₁ la
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat -
              lo.toNat)
            lo.toNat
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
        | .error e' =>
          simp [hcp] at hfwd
          cases hfwd
          have hhi_lt₁ : hi₂.toNat ≤ lt₁.length := by omega
          have hF_copy : (hi₂.toNat - lo.toNat) + 1 ≤ G + 1 := by
            omega
          have hcp' : sortCopyFwd lt₁ la (hi₂.toNat - lo.toNat)
              lo.toNat hi₂.toNat = .error e := by
            rwa [← hhi₂] at hcp
          have hcp_err := sortCopy_err vecMergeSortProg (G + 1) ρ₆
            la lt₁ n w lo mid₂ hi₂ lo e hinv₆ hlent₁ hlena hhi_le
            hhi_lt₁ (by omega) hF_copy hcp'
          have hrest : evalProgStmt vecMergeSortProg (G + 1)
              (.seq sortSegCall
                (.seq (.assign "t" (.var "lo"))
                  (.seq sortCopyBack
                    (.assign "lo"
                      (.uadd (.uadd (.var "lo") (.var "width"))
                        (.var "width")))))) ρ₄ = .error e := by
            rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _
                hstep_call,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_t]
            exact evalProgStmt_seq_err _ _ _ _ _ _ hcp_err
          have hfull : evalProgStmt vecMergeSortProg (G + 1)
              sortSegBody ρ = .error e := by
            rw [hpre]
            exact hrest
          have hloop : evalProgStmt vecMergeSortProg ((G + 1) + 1)
              sortSegLoop ρ = .error e := by
            simp only [sortSegLoop,
              evalProgStmt_while_true vecMergeSortProg (G + 1) _ _ _
                hcond, hfull]
          exact hloop
        | .ok (la₁, t₁) =>
          simp only [hcp] at hfwd
          obtain ⟨ρ₈, lo₈, mid₈, hi₈, t₈, heval_ok, hinv₈, hlo₈eq,
              hlen₈', hlen_copy₈⟩ :=
            sortSegBody_step (G + 1) ρ la lt n w lo mid₀ hi₀ t₀ la₁
              lt₁ t₁ hinv hn hlent hlena hlen62 htmp_ge hw1 hw_lt hLo
              (by omega) (by omega) hmr hcp
          have hlent₈ : lt₁.length < 2 ^ 64 := by
            rw [hlen₈']; exact hlent
          have hn₈ : n.toNat = la₁.length := by
            rw [hlen_copy₈]; exact hn
          have hlena₈ : la₁.length < 2 ^ 64 := by
            rw [hlen_copy₈]; exact hlena
          have hlen62₈ : la₁.length < 2 ^ 62 := by
            rw [hlen_copy₈]; exact hlen62
          have htmp_ge₈ : la₁.length ≤ lt₁.length := by
            rw [hlen_copy₈, hlen₈']; exact htmp_ge
          have hF' : 2 * (n.toNat - lo₈.toNat) + 9 ≤ G + 1 := by
            omega
          have hfwd' : sortSegFwd la₁ lt₁ (G + 1) w.toNat lo₈.toNat
              n.toNat = .error e := by
            rw [hlo₈eq]; exact hfwd
          have hloop : evalProgStmt vecMergeSortProg ((G + 1) + 1)
              sortSegLoop ρ =
              evalProgStmt vecMergeSortProg (G + 1) sortSegLoop
                ρ₈ := by
            simp only [sortSegLoop,
              evalProgStmt_while_true vecMergeSortProg (G + 1) _ _ _
                hcond, heval_ok]
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ _ hinv₈ hn₈ hlent₈ hlena₈
            hlen62₈ htmp_ge₈ hw1 hw_lt hF' hfwd'
    · have hcond : evalExpr (.ult (.var "lo") (.var "n")) ρ =
          .ok (.b false) := by
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_false hLo] at h
      have hfwd0 : sortSegFwd la lt (F + 1) w.toNat lo.toNat
          n.toNat = .ok (la, lt) := by
        simp only [sortSegFwd, dite_eq_right hLo]
      rw [hfwd0] at hfwd
      cases hfwd

/-! ## Outer loop -/

/-- Segments preserve `a` length (the callee never touches `a`,
    the copy only sets). -/
theorem sortSegFwd_length_la (la lt : List (BitVec 32))
    (F w lo n : Nat) (la' lt' : List (BitVec 32))
    (h : sortSegFwd la lt F w lo n = .ok (la', lt')) :
    la'.length = la.length := by
  induction F generalizing la lt w lo la' lt' with
  | zero =>
    simp only [sortSegFwd, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ F ih =>
    simp only [sortSegFwd] at h
    by_cases hLo : lo < n
    · simp only [dite_eq_left hLo] at h
      match hmr : VecMergeRuns.mergeRunsFwd la lt lo (Nat.min (lo + w) n)
          (Nat.min (lo + w + w) n) with
      | .error e => simp [hmr] at h
      | .ok v =>
        obtain ⟨lt₁, rfl⟩ := VecMergeRuns.mergeRunsFwd_ok_shape la lt lo
          (Nat.min (lo + w) n) (Nat.min (lo + w + w) n) v hmr
        simp only [hmr] at h
        match hcp : sortCopyFwd lt₁ la
            (Nat.min (lo + w + w) n - lo) lo
            (Nat.min (lo + w + w) n) with
        | .error e => simp [hcp] at h
        | .ok (la₁, t₁) =>
          simp only [hcp] at h
          have h1 := sortCopyFwd_length lt₁ la _ _ _ _ _ hcp
          have h2 := ih _ _ _ _ _ _ h
          exact h2.trans h1
    · simp only [dite_eq_right hLo, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- Segments preserve `tmp` length (given `a`-length facts, which
    the caller threads). -/
theorem sortSegFwd_length_lt (la lt : List (BitVec 32))
    (F w lo n : Nat) (la' lt' : List (BitVec 32))
    (hn : n = la.length) (hge : la.length ≤ lt.length)
    (h : sortSegFwd la lt F w lo n = .ok (la', lt')) :
    lt'.length = lt.length := by
  induction F generalizing la lt w lo la' lt' with
  | zero =>
    simp only [sortSegFwd, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ F ih =>
    simp only [sortSegFwd] at h
    by_cases hLo : lo < n
    · simp only [dite_eq_left hLo] at h
      match hmr : VecMergeRuns.mergeRunsFwd la lt lo (Nat.min (lo + w) n)
          (Nat.min (lo + w + w) n) with
      | .error e => simp [hmr] at h
      | .ok v =>
        obtain ⟨lt₁, rfl⟩ := VecMergeRuns.mergeRunsFwd_ok_shape la lt lo
          (Nat.min (lo + w) n) (Nat.min (lo + w + w) n) v hmr
        simp only [hmr] at h
        have hlo_mid : lo ≤ Nat.min (lo + w) n :=
          Nat.le_min.mpr ⟨Nat.le_add_right _ _, by omega⟩
        have hmid_hi : Nat.min (lo + w) n ≤
            Nat.min (lo + w + w) n :=
          Nat.le_min.mpr
            ⟨Nat.le_trans (Nat.min_le_left _ _) (by omega),
             Nat.min_le_right _ _⟩
        have hlo_lt : lo ≤ lt.length := by omega
        have hlen_c : lt₁.length = lt.length :=
          VecMergeRuns.mergeRunsFwd_length la lt lo (Nat.min (lo + w) n)
            (Nat.min (lo + w + w) n) lt₁ hlo_mid hmid_hi hlo_lt hmr
        match hcp : sortCopyFwd lt₁ la
            (Nat.min (lo + w + w) n - lo) lo
            (Nat.min (lo + w + w) n) with
        | .error e => simp [hcp] at h
        | .ok (la₁, t₁) =>
          simp only [hcp] at h
          have hlen_a : la₁.length = la.length :=
            sortCopyFwd_length lt₁ la _ _ _ _ _ hcp
          have hge₁ : la₁.length ≤ lt₁.length := by
            rw [hlen_a, hlen_c]; exact hge
          have hn₁ : n = la₁.length := by
            rw [hlen_a]; exact hn
          have h2 := ih _ _ _ _ _ _ hn₁ hge₁ h
          exact h2.trans hlen_c
    · simp only [dite_eq_right hLo, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-! ## Outer loop -/

/-- Outer-body error step: a segment failure fails the pass. -/
theorem sortOuterBody_err (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (e : Panic)
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * n.toNat + 9 ≤ F)
    (hseg : sortSegFwd la lt F w.toNat 0 n.toNat = .error e) :
    evalProgStmt vecMergeSortProg F sortOuterBody ρ = .error e := by
  obtain ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ := hinv
  have heval_z : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  obtain ⟨ρ_a, hu_a⟩ := envUpdate_some_of_lookup ρ "lo"
    (.u64 lo₀) (.u64 (BitVec.ofNat 64 0)) hlo₀
  have hstep_a : evalProgStmt vecMergeSortProg F
      (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
      .ok (ρ_a, .fellThrough) := by
    have hstmt := evalStmtFuel_assign F _ _ _ _ _ heval_z hu_a
    simpa [evalProgStmt] using hstmt
  have hinv_a : SortInv ρ_a la lt n w (BitVec.ofNat 64 0) mid₀ hi₀
      t₀ :=
    sortInv_update_lo _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ hu_a
  have hz : (BitVec.ofNat 64 0).toNat = 0 := bv64_toNat_ofNat 0
    (by omega)
  have hF_seg : 2 * (n.toNat - 0) + 9 ≤ F := by omega
  have hseg' : sortSegFwd la lt F w.toNat
      (BitVec.ofNat 64 0).toNat n.toNat = .error e := by
    rw [hz]; exact hseg
  have heval_seg : evalProgStmt vecMergeSortProg F sortSegLoop ρ_a =
      .error e :=
    sortSeg_err F ρ_a la lt n w (BitVec.ofNat 64 0) mid₀ hi₀ t₀ e
      hinv_a hn hlent hlena hlen62 htmp_ge hw1 hw_lt hF_seg hseg'
  have hbody : sortOuterBody =
      (.seq (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq sortSegLoop
          (.assign "width"
            (.uadd (.var "width") (.var "width"))))) := rfl
  rw [hbody,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_a]
  exact evalProgStmt_seq_err _ _ _ _ _ _ heval_seg

theorem sortOuterGuardW_eval (ρ : Env) (la lt : List (BitVec 32))
    (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t) :
    evalExpr (.ult (.var "width") (.var "n")) ρ =
      .ok (.b (decide (w.toNat < n.toNat))) := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hnv : evalExpr (.var "width") ρ = .ok (.u64 w) :=
    evalExpr_var_hit _ _ _ hw
  have hmv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
    evalExpr_var_hit _ _ _ hn
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
  rw [VecMergeRuns.bv64_ult_toNat w n] at hult
  exact hult

/-- Outer-body step: reset `lo`, run the segments, double `width`. -/
theorem sortOuterBody_step (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (la₁ lt₁ : List (BitVec 32))
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * n.toNat + 9 ≤ F)
    (hseg : sortSegFwd la lt F w.toNat 0 n.toNat = .ok (la₁, lt₁)) :
    ∃ ρ' w' lo' mid' hi' t',
      evalProgStmt vecMergeSortProg F sortOuterBody ρ =
        .ok (ρ', .fellThrough) ∧
      SortInv ρ' la₁ lt₁ n w' lo' mid' hi' t' ∧
      w'.toNat = w.toNat + w.toNat := by
  obtain ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ := hinv
  -- `lo ← 0`.
  have heval_z : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  obtain ⟨ρ_a, hu_a⟩ := envUpdate_some_of_lookup ρ "lo"
    (.u64 lo₀) (.u64 (BitVec.ofNat 64 0)) hlo₀
  have hstep_a : evalProgStmt vecMergeSortProg F
      (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
      .ok (ρ_a, .fellThrough) := by
    have hstmt := evalStmtFuel_assign F _ _ _ _ _ heval_z hu_a
    simpa [evalProgStmt] using hstmt
  have hinv_a : SortInv ρ_a la lt n w (BitVec.ofNat 64 0) mid₀ hi₀
      t₀ :=
    sortInv_update_lo _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ hu_a
  -- Segments from `lo = 0`.
  have hz : (BitVec.ofNat 64 0).toNat = 0 := bv64_toNat_ofNat 0
    (by omega)
  have hF_seg : 2 * (n.toNat - 0) + 9 ≤ F := by omega
  have hseg' : sortSegFwd la lt F w.toNat
      (BitVec.ofNat 64 0).toNat n.toNat = .ok (la₁, lt₁) := by
    rw [hz]; exact hseg
  obtain ⟨ρ_b, lo_b, mid_b, hi_b, t_b, heval_seg, hinv_b⟩ :=
    sortSeg_ok F ρ_a la lt n w (BitVec.ofNat 64 0) mid₀ hi₀ t₀ la₁
      lt₁ hinv_a hn hlent hlena hlen62 htmp_ge hw1 hw_lt hF_seg hseg'
  obtain ⟨ha_b, htmp_b, hnL_b, hw_b, hlo_b, hmid_b, hhi_b,
      htt_b⟩ := hinv_b
  -- `width ← width + width`.
  have hw2 : (w + w).toNat = w.toNat + w.toNat :=
    bv64_add_toNat w w (by omega)
  have heval_ww : evalExpr
      (.uadd (.var "width") (.var "width")) ρ_b =
      .ok (.u64 (w + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hw_b) (evalExpr_var_hit _ _ _ hw_b)
  obtain ⟨ρ_c, hu_c⟩ := envUpdate_some_of_lookup ρ_b "width"
    (.u64 w) (.u64 (w + w)) hw_b
  have hstep_c : evalProgStmt vecMergeSortProg F
      (.assign "width" (.uadd (.var "width") (.var "width"))) ρ_b =
      .ok (ρ_c, .fellThrough) := by
    have hstmt := evalStmtFuel_assign F _ _ _ _ _ heval_ww hu_c
    simpa [evalProgStmt] using hstmt
  have hinv_c : SortInv ρ_c la₁ lt₁ n (w + w) lo_b mid_b hi_b t_b :=
    sortInv_update_width _ _ _ _ _ _ _ _ _ _ _
      ⟨ha_b, htmp_b, hnL_b, hw_b, hlo_b, hmid_b, hhi_b, htt_b⟩ hu_c
  -- Assemble.
  have hbody : sortOuterBody =
      (.seq (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq sortSegLoop
          (.assign "width"
            (.uadd (.var "width") (.var "width"))))) := rfl
  refine ⟨ρ_c, (w + w), lo_b, mid_b, hi_b, t_b, ?_, hinv_c,
    hw2⟩
  rw [hbody,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_a,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ heval_seg]
  exact hstep_c

/-- Outer-loop ok soundness. -/
theorem sortOuter_ok (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (la' lt' : List (BitVec 32))
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat)
    (hF : 2 * (n.toNat - w.toNat) + 2 * n.toNat + 10 ≤ F)
    (hfwd : sortOuterFwd la lt F w.toNat n.toNat = .ok (la', lt')) :
    ∃ ρ' w' lo' mid' hi' t',
      evalProgStmt vecMergeSortProg F sortOuterLoop ρ =
        .ok (ρ', .fellThrough) ∧
      SortInv ρ' la' lt' n w' lo' mid' hi' t' := by
  induction F generalizing ρ la lt n w lo₀ mid₀ hi₀ t₀ la' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hW : w.toNat < n.toNat
    · have hcond : evalExpr (.ult (.var "width") (.var "n")) ρ =
          .ok (.b true) := by
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_true hW] at h
      simp only [sortOuterFwd, dite_eq_left hW] at hfwd
      match hseg : sortSegFwd la lt F w.toNat 0 n.toNat with
      | .error e => simp [hseg] at hfwd
      | .ok (la₁, lt₁) =>
        simp only [hseg] at hfwd
        obtain ⟨ρ₁, w₁, lo₁, mid₁, hi₁, t₁, heval_body, hinv₁,
            hw₁eq⟩ :=
          sortOuterBody_step F ρ la lt n w lo₀ mid₀ hi₀ t₀ la₁ lt₁
            hinv hn hlent hlena hlen62 htmp_ge hw1 hW (by omega) hseg
        have hloop : evalProgStmt vecMergeSortProg (F + 1)
            sortOuterLoop ρ =
            evalProgStmt vecMergeSortProg F sortOuterLoop ρ₁ := by
          simp only [sortOuterLoop,
            evalProgStmt_while_true vecMergeSortProg F _ _ _ hcond,
            heval_body]
        have hw1' : 1 ≤ w₁.toNat := by omega
        have hF' : 2 * (n.toNat - w₁.toNat) + 2 * n.toNat + 10 ≤
            F := by
          omega
        have hfwd' : sortOuterFwd la₁ lt₁ F w₁.toNat n.toNat =
            .ok (la', lt') := by
          rw [hw₁eq]; exact hfwd
        rw [hloop]
        have hlen_la : la₁.length = la.length :=
          sortSegFwd_length_la la lt F w.toNat 0 n.toNat la₁ lt₁ hseg
        have hlen_lt : lt₁.length = lt.length :=
          sortSegFwd_length_lt la lt F w.toNat 0 n.toNat la₁ lt₁
            hn htmp_ge hseg
        have hn₁ : n.toNat = la₁.length := by
          rw [hlen_la]; exact hn
        have hlent₁ : lt₁.length < 2 ^ 64 := by
          rw [hlen_lt]; exact hlent
        have hlena₁ : la₁.length < 2 ^ 64 := by
          rw [hlen_la]; exact hlena
        have hlen62₁ : la₁.length < 2 ^ 62 := by
          rw [hlen_la]; exact hlen62
        have htmp_ge₁ : la₁.length ≤ lt₁.length := by
          rw [hlen_la, hlen_lt]; exact htmp_ge
        obtain ⟨ρ', w', lo', mid', hi', t', hev, hinv'⟩ :=
          ih _ _ _ _ _ _ _ _ _ _ _ hinv₁ hn₁ hlent₁ hlena₁ hlen62₁
            htmp_ge₁ hw1' hF' hfwd'
        exact ⟨ρ', w', lo', mid', hi', t', hev, hinv'⟩
    · have hcond : evalExpr (.ult (.var "width") (.var "n")) ρ =
          .ok (.b false) := by
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_false hW] at h
      have hfwd0 : sortOuterFwd la lt (F + 1) w.toNat n.toNat =
          .ok (la, lt) := by
        simp only [sortOuterFwd, dite_eq_right hW]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hexit : evalProgStmt vecMergeSortProg (F + 1)
          sortOuterLoop ρ = .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false vecMergeSortProg _ _ _ _ hcond
      exact ⟨ρ, w, lo₀, mid₀, hi₀, t₀, hexit, hinv⟩

/-- Outer-loop error soundness. -/
theorem sortOuter_err (F : Nat) (ρ : Env)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (e : Panic)
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat)
    (hF : 2 * (n.toNat - w.toNat) + 2 * n.toNat + 10 ≤ F)
    (hfwd : sortOuterFwd la lt F w.toNat n.toNat = .error e) :
    evalProgStmt vecMergeSortProg F sortOuterLoop ρ = .error e := by
  induction F generalizing ρ la lt n w lo₀ mid₀ hi₀ t₀ e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hW : w.toNat < n.toNat
    · have hcond : evalExpr (.ult (.var "width") (.var "n")) ρ =
          .ok (.b true) := by
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_true hW] at h
      simp only [sortOuterFwd, dite_eq_left hW] at hfwd
      match hseg : sortSegFwd la lt F w.toNat 0 n.toNat with
      | .error e' =>
        simp [hseg] at hfwd
        cases hfwd
        have heval_body : evalProgStmt vecMergeSortProg F
            sortOuterBody ρ = .error e :=
          sortOuterBody_err F ρ la lt n w lo₀ mid₀ hi₀ t₀ e
            hinv hn hlent hlena hlen62 htmp_ge hw1 hW (by omega)
            hseg
        simp only [sortOuterLoop,
          evalProgStmt_while_true vecMergeSortProg F _ _ _ hcond,
          heval_body]
      | .ok (la₁, lt₁) =>
        simp only [hseg] at hfwd
        obtain ⟨ρ₁, w₁, lo₁, mid₁, hi₁, t₁, heval_body, hinv₁,
            hw₁eq⟩ :=
          sortOuterBody_step F ρ la lt n w lo₀ mid₀ hi₀ t₀ la₁ lt₁
            hinv hn hlent hlena hlen62 htmp_ge hw1 hW (by omega) hseg
        have hloop : evalProgStmt vecMergeSortProg (F + 1)
            sortOuterLoop ρ =
            evalProgStmt vecMergeSortProg F sortOuterLoop ρ₁ := by
          simp only [sortOuterLoop,
            evalProgStmt_while_true vecMergeSortProg F _ _ _ hcond,
            heval_body]
        have hw1' : 1 ≤ w₁.toNat := by omega
        have hF' : 2 * (n.toNat - w₁.toNat) + 2 * n.toNat + 10 ≤
            F := by
          omega
        have hfwd' : sortOuterFwd la₁ lt₁ F w₁.toNat n.toNat =
            .error e := by
          rw [hw₁eq]; exact hfwd
        rw [hloop]
        have hlen_la : la₁.length = la.length :=
          sortSegFwd_length_la la lt F w.toNat 0 n.toNat la₁ lt₁ hseg
        have hlen_lt : lt₁.length = lt.length :=
          sortSegFwd_length_lt la lt F w.toNat 0 n.toNat la₁ lt₁
            hn htmp_ge hseg
        have hn₁ : n.toNat = la₁.length := by
          rw [hlen_la]; exact hn
        have hlent₁ : lt₁.length < 2 ^ 64 := by
          rw [hlen_lt]; exact hlent
        have hlena₁ : la₁.length < 2 ^ 64 := by
          rw [hlen_la]; exact hlena
        have hlen62₁ : la₁.length < 2 ^ 62 := by
          rw [hlen_la]; exact hlen62
        have htmp_ge₁ : la₁.length ≤ lt₁.length := by
          rw [hlen_la, hlen_lt]; exact htmp_ge
        exact ih _ _ _ _ _ _ _ _ _ _ hinv₁ hn₁ hlent₁ hlena₁
          hlen62₁ htmp_ge₁ hw1' hF' hfwd'
    · have hcond : evalExpr (.ult (.var "width") (.var "n")) ρ =
          .ok (.b false) := by
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_false hW] at h
      simp only [sortOuterFwd, dite_eq_right hW] at hfwd
      simp at hfwd

/-- Entry bridge: the sort function equals its forward model. -/
theorem evalProgFunc_vecMergeSort (F : Nat)
    (la lt : List (BitVec 32))
    (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (hlent : lt.length < 2 ^ 64)
    (htmp_ge : la.length ≤ lt.length)
    (hF : 2 * (la.length - 1) + 2 * la.length + 10 ≤ F) :
    evalProgFunc vecMergeSortProg F vecMergeSortFunc
      [.stdVecVal la, .stdVecVal lt] =
      vecMergeSortFwd la lt F := by
  have hn64 : (BitVec.ofNat 64 la.length).toNat = la.length :=
    bv64_toNat_ofNat _ hlena
  have hw64 : (BitVec.ofNat 64 1).toNat = 1 :=
    bv64_toNat_ofNat 1 (by omega)
  have hbind : bindArgs vecMergeSortFunc.args
      [.stdVecVal la, .stdVecVal lt] =
      some [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] := rfl
  have hbody : vecMergeSortFunc.body =
      (.seq (.let_ "n" (.u 64) (.stdVecLen "a"))
        (.seq (.let_ "width" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 1))))
          (.seq (.let_ "lo" (.u 64)
              (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq (.let_ "mid" (.u 64)
                (.lit (.u64 (BitVec.ofNat 64 0))))
              (.seq (.let_ "hi" (.u 64)
                  (.lit (.u64 (BitVec.ofNat 64 0))))
                (.seq (.let_ "t" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                  (.seq sortOuterLoop
                    (.return_ (.var "a"))))))))) := rfl
  have hlen_n : evalExpr (.stdVecLen "a")
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some "a" _ la rfl
  have hlet_n : evalProgStmt vecMergeSortProg F
      (.let_ "n" (.u 64) (.stdVecLen "a"))
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok ([("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)],
        .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hlen_n)
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      ([("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]) =
      .ok (.u64 (BitVec.ofNat 64 1)) :=
    evalExpr_lit _ _
  have hlet_width : evalProgStmt vecMergeSortProg F
      (.let_ "width" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok ([("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)],
        .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hone)
  have hzero_w : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      ([("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hlet_lo : evalProgStmt vecMergeSortProg F
      (.let_ "lo" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok ([("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)],
        .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hzero_w)
  have hzero_l : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      ([("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hlet_mid : evalProgStmt vecMergeSortProg F
      (.let_ "mid" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok ([("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)],
        .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hzero_l)
  have hzero_m : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      ([("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hlet_hi : evalProgStmt vecMergeSortProg F
      (.let_ "hi" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok ([("hi", .u64 (BitVec.ofNat 64 0)),
        ("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)],
        .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hzero_m)
  have hzero_h : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      ([("hi", .u64 (BitVec.ofNat 64 0)),
        ("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hlet_t : evalProgStmt vecMergeSortProg F
      (.let_ "t" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("hi", .u64 (BitVec.ofNat 64 0)),
        ("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok ([("t", .u64 (BitVec.ofNat 64 0)),
        ("hi", .u64 (BitVec.ofNat 64 0)),
        ("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)],
        .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hzero_h)
  have henv : [("t", .u64 (BitVec.ofNat 64 0)),
        ("hi", .u64 (BitVec.ofNat 64 0)),
        ("mid", .u64 (BitVec.ofNat 64 0)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("width", .u64 (BitVec.ofNat 64 1)),
        ("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      mkSortEnv la lt (BitVec.ofNat 64 la.length)
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) := rfl
  have hinv : SortInv
      (mkSortEnv la lt (BitVec.ofNat 64 la.length)
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0))
      la lt (BitVec.ofNat 64 la.length) (BitVec.ofNat 64 1)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) :=
    mkSortEnv_inv _ _ _ _ _ _ _ _
  have hw1 : 1 ≤ (BitVec.ofNat 64 1).toNat := by simp [hw64]
  have hF' : 2 * ((BitVec.ofNat 64 la.length).toNat -
      (BitVec.ofNat 64 1).toNat) +
      2 * (BitVec.ofNat 64 la.length).toNat + 10 ≤ F := by
    rw [hn64, hw64]; exact hF
  match houter : sortOuterFwd la lt F 1 la.length with
  | .error e =>
    have houter' : sortOuterFwd la lt F
        (BitVec.ofNat 64 1).toNat
        (BitVec.ofNat 64 la.length).toNat = .error e := by
      rw [hw64, hn64]; exact houter
    have hO := sortOuter_err F
      (mkSortEnv la lt (BitVec.ofNat 64 la.length)
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0))
      la lt (BitVec.ofNat 64 la.length) (BitVec.ofNat 64 1)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) e
      hinv hn64 hlent hlena hlen62 htmp_ge hw1 hF' houter'
    have hfwd : vecMergeSortFwd la lt F = .error e := by
      simp [vecMergeSortFwd, houter]
    have hstmt : evalProgStmt vecMergeSortProg F
        vecMergeSortFunc.body
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
        .error e := by
      rw [hbody,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_n,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_width,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_lo,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_mid,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_hi,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_t, henv,
        evalProgStmt_seq_err vecMergeSortProg F _ _ _ _ hO]
    simp [evalProgFunc, hbind, hstmt, hfwd]
  | .ok (la', lt') =>
    have houter' : sortOuterFwd la lt F
        (BitVec.ofNat 64 1).toNat
        (BitVec.ofNat 64 la.length).toNat = .ok (la', lt') := by
      rw [hw64, hn64]; exact houter
    obtain ⟨ρ', w', lo', mid', hi', t', heval_O, hinv'⟩ :=
      sortOuter_ok F
        (mkSortEnv la lt (BitVec.ofNat 64 la.length)
          (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
          (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
          (BitVec.ofNat 64 0))
        la lt (BitVec.ofNat 64 la.length) (BitVec.ofNat 64 1)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) la' lt'
        hinv hn64 hlent hlena hlen62 htmp_ge hw1 hF' houter'
    obtain ⟨ha', htmp', hn', hw', hlo', hmid', hhi', htt'⟩ := hinv'
    have hret : evalProgStmt vecMergeSortProg F
        (.return_ (.var "a")) ρ' =
        .ok (ρ', .returned (.stdVecVal la')) :=
      evalProgStmt_return vecMergeSortProg F (.var "a") ρ'
        (.stdVecVal la') (evalExpr_var_hit _ _ _ ha')
    have hfwd : vecMergeSortFwd la lt F = .ok (.stdVecVal la') := by
      simp [vecMergeSortFwd, houter]
    have hstmt : evalProgStmt vecMergeSortProg F
        vecMergeSortFunc.body
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
        .ok (ρ', .returned (.stdVecVal la')) := by
      rw [hbody,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_n,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_width,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_lo,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_mid,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_hi,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          hlet_t, henv,
        evalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _
          heval_O]
      exact hret
    simp [evalProgFunc, hbind, hstmt, hfwd]

end VecMergeSort
