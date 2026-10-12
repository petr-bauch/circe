/-
Circe.Emit.SumTwo — `sum_two`: bounded loop over two length-paired
readonly arrays (the two-reader admission resting on the N2a
model-side discipline, `Circe.ReadOnly`).

The corpus (`tests/c/sum_two.c`: `s += a[i] + b[i]` over `n`) mirrors
`sum_array` with a second reader: two `cir.ptr_stride` reads and two
plain `cir.add` per iteration. Readers never write, so aliasing
(`a == b`) is value-sound — entry binding pins two fresh blocks
(`bindMemArgs_twoShared`, disjoint by construction) and reads through
either pin agree (`twoShared_alias_sound`).

The forward folds the pairwise wrapping sums; `OOB` fires past
*either* array (both reads are UB in C there). Loop + transfer proofs
mirror `Circe.Emit.Sum` / `Circe.Transfer.Core` with the pair carried
through every environment.
-/
import Circe.Emit.Fragment
import Circe.Emit.Sum
import Circe.ReadOnly

/-! ## Pairwise wrapping fold -/

/-- Wrapping pairwise sum of the first `k` elements (stops at the
    shorter list; `sum_two` accumulates `uint32_t`, so addition wraps
    mod 2^32 and never fails). -/
def pairSum : List (BitVec 32) → List (BitVec 32) → Nat → BitVec 32
  | x :: xs, y :: ys, k + 1 => (x + y) + pairSum xs ys k
  | _, _, _ => 0

theorem pairSum_cons (x y : BitVec 32) (xs ys : List (BitVec 32))
    (k : Nat) :
    pairSum (x :: xs) (y :: ys) (k + 1) = (x + y) + pairSum xs ys k := rfl

theorem pairSum_zero (l₁ l₂ : List (BitVec 32)) :
    pairSum l₁ l₂ 0 = 0 := by
  cases l₁ <;> cases l₂ <;> rfl

/-- Splitting both drops at a valid index exposes both heads. -/
theorem drop_pair_cons_getElem (l₁ l₂ : List (BitVec 32)) (k : Nat)
    (h₁ : k < l₁.length) (h₂ : k < l₂.length) :
    l₁.drop k = l₁[k] :: l₁.drop (k + 1) ∧
      l₂.drop k = l₂[k] :: l₂.drop (k + 1) :=
  ⟨drop_cons_getElem l₁ k h₁, drop_cons_getElem l₂ k h₂⟩

/-- Bridge to the spec world: under a shared bound the pairwise fold
    is the sum of the two prefix sums (so `List.sum` lemmas apply via
    `prefixSumU32_take_sum`). -/
theorem pairSum_distrib (l₁ : List (BitVec 32)) (l₂ : List (BitVec 32))
    (k : Nat) (h₁ : k ≤ l₁.length) (h₂ : k ≤ l₂.length) :
    pairSum l₁ l₂ k = prefixSumU32 l₁ k + prefixSumU32 l₂ k := by
  induction l₁ generalizing l₂ k with
  | nil =>
    have hk : k = 0 := by simpa using h₁
    subst hk
    simp [pairSum, prefixSumU32_zero]
  | cons x xs ih =>
    cases l₂ with
    | nil =>
      have hk : k = 0 := by simpa using h₂
      subst hk
      simp [pairSum, prefixSumU32]
    | cons y ys =>
      cases k with
      | zero => simp [pairSum, prefixSumU32]
      | succ k =>
        simp only [List.length_cons] at h₁ h₂
        have hrec := ih ys k (by omega) (by omega)
        rw [pairSum_cons, prefixSumU32_cons, prefixSumU32_cons, hrec,
          BitVec.add_assoc x y (prefixSumU32 xs k + prefixSumU32 ys k),
          ← BitVec.add_assoc y (prefixSumU32 xs k) (prefixSumU32 ys k),
          BitVec.add_comm y (prefixSumU32 xs k),
          BitVec.add_assoc (prefixSumU32 xs k) y (prefixSumU32 ys k),
          ← BitVec.add_assoc x (prefixSumU32 xs k)
            (y + prefixSumU32 ys k)]

/-! ### Canonical CoreIR + verified forward function -/

/-- Loop body: `s = s + (a[i] + b[i]); i = i + 1` (wrapping `u32`,
    plain `cir.add`; the two `cir.ptr_stride` reads fuse into the two
    `idx` subterms). -/
def sumTwoBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s")
    (.uadd (.idx "a" (.var "i")) (.idx "b" (.var "i")))))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Loop: `while (i < n) { ... }` (`cir.for` cond region). -/
def sumTwoWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) sumTwoBody

/-- Canonical CoreIR for `tests/c/sum_two.c`. Params are exactly
    `twoReaderParams` (two `sharedBorrow` arrays + owned length), so
    the N2a footprint lemmas apply directly. -/
def sumTwoFunc : Func :=
  ⟨"sum_two", twoReaderParams, .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq sumTwoWhile
         (.return_ (.var "s"))))⟩

/-- Value-level forward function for `sum_two`: wrapping pairwise sum
    of the first `n` elements; `OOB` past either array. -/
def sumTwoFwd (l₁ l₂ : List (BitVec 32)) (n : BitVec 32) : Result Value :=
  if n.toNat ≤ l₁.length ∧ n.toNat ≤ l₂.length then
    .ok (.u32 (pairSum l₁ l₂ n.toNat))
  else .error .OOB

/-- OOB corollary helper: `sumTwoFwd` reports `OOB` exactly off-range. -/
theorem sumTwoFwd_oob (l₁ l₂ : List (BitVec 32)) (n : BitVec 32)
    (h : ¬ (n.toNat ≤ l₁.length ∧ n.toNat ≤ l₂.length)) :
    sumTwoFwd l₁ l₂ n = .error .OOB := by
  simp [sumTwoFwd, h]

theorem sumTwoFwd_ok (l₁ l₂ : List (BitVec 32)) (n : BitVec 32)
    (h : n.toNat ≤ l₁.length ∧ n.toNat ≤ l₂.length) :
    sumTwoFwd l₁ l₂ n = .ok (.u32 (pairSum l₁ l₂ n.toNat)) := by
  simp [sumTwoFwd, h]

/-! ### Loop invariant -/

/-- Loop environments: index `k` and accumulator, both arrays and the
    bound fixed. -/
def mkSumTwoEnv (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) : Env :=
  [("i", .u32 (BitVec.ofNat 32 k)), ("s", .u32 acc),
   ("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]

theorem mkSumTwoEnv_i (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkSumTwoEnv, envLookup]

theorem mkSumTwoEnv_s (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "s" = some (.u32 acc) := by
  simp [mkSumTwoEnv, envLookup, show ("s" : String) ≠ "i" by decide]

theorem mkSumTwoEnv_a (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "a" = some (.arr32 l₁) := by
  simp [mkSumTwoEnv, envLookup, show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "s" by decide]

theorem mkSumTwoEnv_b (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "b" = some (.arr32 l₂) := by
  simp [mkSumTwoEnv, envLookup, show ("b" : String) ≠ "i" by decide,
    show ("b" : String) ≠ "s" by decide,
    show ("b" : String) ≠ "a" by decide]

theorem mkSumTwoEnv_n (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumTwoEnv l₁ l₂ nv k acc) "n" = some (.u32 nv) := by
  simp [mkSumTwoEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "a" by decide,
    show ("n" : String) ≠ "b" by decide]

/-- Updating `s` in a loop env stays a loop env. -/
theorem sumTwoEnv_update_s (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (k : Nat) (acc v : BitVec 32) :
    envUpdate (mkSumTwoEnv l₁ l₂ nv k acc) "s" (.u32 v) =
      some (mkSumTwoEnv l₁ l₂ nv k v) := by
  simp [mkSumTwoEnv, envUpdate, show ("s" : String) ≠ "i" by decide]

/-- Updating `i` in a loop env stays a loop env. -/
theorem sumTwoEnv_update_i (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (k k' : Nat) (acc : BitVec 32) :
    envUpdate (mkSumTwoEnv l₁ l₂ nv k acc) "i" (.u32 (BitVec.ofNat 32 k')) =
      some (mkSumTwoEnv l₁ l₂ nv k' acc) := by
  simp [mkSumTwoEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem sumTwoCond_eval (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (k : Nat) (acc : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkSumTwoEnv l₁ l₂ nv k acc) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSumTwoEnv_i l₁ l₂ nv k acc
  have hn := mkSumTwoEnv_n l₁ l₂ nv k acc
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- One body step advances index and accumulator (any fuel: loop-free). -/
theorem sumTwoBody_eval (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (hklen₁ : k < l₁.length) (hklen₂ : k < l₂.length)
    (hk32 : k < 2 ^ 32) :
    evalStmtFuel F sumTwoBody (mkSumTwoEnv l₁ l₂ nv k acc) =
      .ok (mkSumTwoEnv l₁ l₂ nv (k + 1) (acc + (l₁[k] + l₂[k])),
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hget₁ : l₁[k]? = some l₁[k] := List.getElem?_eq_getElem hklen₁
  have hget₂ : l₂[k]? = some l₂[k] := List.getElem?_eq_getElem hklen₂
  have hs : evalExpr (.uadd (.var "s")
        (.uadd (.idx "a" (.var "i")) (.idx "b" (.var "i"))))
        (mkSumTwoEnv l₁ l₂ nv k acc) =
        .ok (.u32 (acc + (l₁[k] + l₂[k]))) := by
    have h1 := mkSumTwoEnv_s l₁ l₂ nv k acc
    have ha := mkSumTwoEnv_a l₁ l₂ nv k acc
    have hb := mkSumTwoEnv_b l₁ l₂ nv k acc
    have hii := mkSumTwoEnv_i l₁ l₂ nv k acc
    simp only [evalExpr, h1, ha, hb, hii, hkk, hget₁, hget₂]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkSumTwoEnv l₁ l₂ nv k (acc + (l₁[k] + l₂[k]))) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSumTwoEnv_i l₁ l₂ nv k (acc + (l₁[k] + l₂[k]))
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := sumTwoEnv_update_s l₁ l₂ nv k acc (acc + (l₁[k] + l₂[k]))
  have up2 := sumTwoEnv_update_i l₁ l₂ nv k (k + 1) (acc + (l₁[k] + l₂[k]))
  cases F <;>
    simp [sumTwoBody, evalStmtFuel, evalStmtZero, evalStmtWith,
      hs, hi2, up1, up2]

/-- The OOB step on the first array: the `a[i]` read fails loudly
    (the `b` read is never reached — first error wins). -/
theorem sumTwoBody_oob_a (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (hget₁ : l₁[k]? = none) (hk32 : k < 2 ^ 32) :
    evalStmtFuel F sumTwoBody (mkSumTwoEnv l₁ l₂ nv k acc) =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hs : evalExpr (.uadd (.var "s")
        (.uadd (.idx "a" (.var "i")) (.idx "b" (.var "i"))))
        (mkSumTwoEnv l₁ l₂ nv k acc) = .error .OOB := by
    have h1 := mkSumTwoEnv_s l₁ l₂ nv k acc
    have ha := mkSumTwoEnv_a l₁ l₂ nv k acc
    have hb := mkSumTwoEnv_b l₁ l₂ nv k acc
    have hii := mkSumTwoEnv_i l₁ l₂ nv k acc
    simp only [evalExpr, h1, ha, hb, hii, hkk, hget₁]
  cases F <;>
    simp [sumTwoBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs]

/-- The OOB step on the second array: `a[i]` reads fine, the `b[i]`
    read fails loudly. -/
theorem sumTwoBody_oob_b (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32) (k : Nat) (acc x : BitVec 32)
    (hget₁ : l₁[k]? = some x) (hget₂ : l₂[k]? = none)
    (hk32 : k < 2 ^ 32) :
    evalStmtFuel F sumTwoBody (mkSumTwoEnv l₁ l₂ nv k acc) =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hs : evalExpr (.uadd (.var "s")
        (.uadd (.idx "a" (.var "i")) (.idx "b" (.var "i"))))
        (mkSumTwoEnv l₁ l₂ nv k acc) = .error .OOB := by
    have h1 := mkSumTwoEnv_s l₁ l₂ nv k acc
    have ha := mkSumTwoEnv_a l₁ l₂ nv k acc
    have hb := mkSumTwoEnv_b l₁ l₂ nv k acc
    have hii := mkSumTwoEnv_i l₁ l₂ nv k acc
    simp only [evalExpr, h1, ha, hb, hii, hkk, hget₁, hget₂]
  cases F <;>
    simp [sumTwoBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs]

/-- Loop correctness, in-range: the loop folds the remaining suffix
    pair. -/
theorem sumTwoWhile_correct (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hle₁ : nv.toNat ≤ l₁.length) (hle₂ : nv.toNat ≤ l₂.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F sumTwoWhile (mkSumTwoEnv l₁ l₂ nv k acc) =
      .ok (mkSumTwoEnv l₁ l₂ nv nv.toNat
        (acc + pairSum (l₁.drop k) (l₂.drop k) (nv.toNat - k)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkSumTwoEnv l₁ l₂ nv nv.toNat acc) = .ok (.b false) := by
      simpa using (sumTwoCond_eval l₁ l₂ nv nv.toNat acc h32)
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    have hpre : pairSum (l₁.drop nv.toNat) (l₂.drop nv.toNat) 0 = 0 :=
      pairSum_zero _ _
    simp [sumTwoWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcond, hsub, hpre]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen₁ : k < l₁.length := by omega
      have hklen₂ : k < l₂.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumTwoEnv l₁ l₂ nv k acc) = .ok (.b true) := by
        simpa [hlt] using (sumTwoCond_eval l₁ l₂ nv k acc hk32)
      have hbody := sumTwoBody_eval F l₁ l₂ nv k acc hklen₁ hklen₂ hk32
      have hstep : evalStmtFuel (F + 1) sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv k acc)
          = evalStmtFuel F sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv (k + 1) (acc + (l₁[k] + l₂[k]))) := by
        simp [sumTwoWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hrec := ih (k + 1) (acc + (l₁[k] + l₂[k])) (by omega) (by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hdrop := drop_pair_cons_getElem l₁ l₂ k hklen₁ hklen₂
      obtain ⟨hd₁, hd₂⟩ := hdrop
      have hacc : (acc + (l₁[k] + l₂[k])) +
            pairSum (l₁.drop (k + 1)) (l₂.drop (k + 1)) (nv.toNat - (k + 1))
          = acc + pairSum (l₁.drop k) (l₂.drop k) (nv.toNat - k) := by
        rw [hkk1, hd₁, hd₂, pairSum_cons]
        exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumTwoEnv l₁ l₂ nv nv.toNat acc) = .ok (.b false) := by
        simpa using (sumTwoCond_eval l₁ l₂ nv nv.toNat acc h32)
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      have hpre : pairSum (l₁.drop nv.toNat) (l₂.drop nv.toNat) 0 = 0 :=
        pairSum_zero _ _
      simp [sumTwoWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hsub, hpre]

/-- Loop correctness, out-of-range: the loop reports `OOB` at the
    first index past the shorter array. -/
theorem sumTwoWhile_oob (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ min l₁.length l₂.length)
    (hlt : min l₁.length l₂.length < nv.toNat)
    (hmin32 : min l₁.length l₂.length < 2 ^ 32)
    (hF : min l₁.length l₂.length - k + 1 ≤ F) :
    evalStmtFuel F sumTwoWhile (mkSumTwoEnv l₁ l₂ nv k acc) =
      .error .OOB := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    have hkn : k < nv.toNat := by omega
    have hk32 : k < 2 ^ 32 := by omega
    have hklen₁ : k ≤ l₁.length := by omega
    have hklen₂ : k ≤ l₂.length := by omega
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkSumTwoEnv l₁ l₂ nv k acc) = .ok (.b true) := by
      simpa [hkn] using (sumTwoCond_eval l₁ l₂ nv k acc hk32)
    by_cases hboth : k < l₁.length ∧ k < l₂.length
    · obtain ⟨hk₁, hk₂⟩ := hboth
      have hbody := sumTwoBody_eval F l₁ l₂ nv k acc hk₁ hk₂ hk32
      have hstep : evalStmtFuel (F + 1) sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv k acc)
          = evalStmtFuel F sumTwoWhile
            (mkSumTwoEnv l₁ l₂ nv (k + 1) (acc + (l₁[k] + l₂[k]))) := by
        simp [sumTwoWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      exact ih (k + 1) (acc + (l₁[k] + l₂[k])) (by omega) (by omega)
    · have hbody : evalStmtFuel F sumTwoBody
            (mkSumTwoEnv l₁ l₂ nv k acc) = .error .OOB := by
        by_cases hka : k < l₁.length
        · have hnb : ¬ k < l₂.length := fun h => hboth ⟨hka, h⟩
          have hkb : k = l₂.length := by omega
          subst hkb
          have hget₁ : l₁[l₂.length]? = some l₁[l₂.length] :=
            List.getElem?_eq_getElem hka
          have hget₂ : l₂[l₂.length]? = none :=
            List.getElem?_eq_none (Nat.le_refl _)
          exact sumTwoBody_oob_b F l₁ l₂ nv l₂.length acc l₁[l₂.length]
            hget₁ hget₂ hk32
        · have hkk : k = l₁.length := by omega
          subst hkk
          have hget₁ : l₁[l₁.length]? = none :=
            List.getElem?_eq_none (Nat.le_refl _)
          exact sumTwoBody_oob_a F l₁ l₂ nv l₁.length acc hget₁ hk32
      simp [sumTwoWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hbody]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `sum_two`, at any fuel covering `n`. -/
theorem evalFuncFuel_sumTwo (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32)
    (hle₁ : nv.toNat ≤ l₁.length) (hle₂ : nv.toNat ≤ l₂.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    evalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] =
      sumTwoFwd l₁ l₂ nv := by
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]
      = mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0) := rfl
  have hret := mkSumTwoEnv_s l₁ l₂ nv nv.toNat (pairSum l₁ l₂ nv.toNat)
  have hle : nv.toNat ≤ l₁.length ∧ nv.toNat ≤ l₂.length := ⟨hle₁, hle₂⟩
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumTwoEnv l₁ l₂ nv nv.toNat
            (BitVec.ofNat 32 0 + pairSum (l₁.drop 0) (l₂.drop 0)
              (nv.toNat - 0)),
            .fellThrough) :=
      sumTwoWhile_correct l₁ l₂ nv 0 0 (BitVec.ofNat 32 0)
        (Nat.zero_le _) hle₁ hle₂ h32 (by cir_fuel)
    simp [evalFuncFuel, sumTwoFunc, twoReaderParams, bindArgs, evalStmtFuel,
      evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend, sumTwoFwd,
      henv, hloopH0, hret, hle]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumTwoEnv l₁ l₂ nv nv.toNat
            (BitVec.ofNat 32 0 + pairSum (l₁.drop 0) (l₂.drop 0)
              (nv.toNat - 0)),
            .fellThrough) :=
      sumTwoWhile_correct l₁ l₂ nv (F + 1) 0 (BitVec.ofNat 32 0)
        (Nat.zero_le _) hle₁ hle₂ h32 (by cir_fuel)
    simp [evalFuncFuel, sumTwoFunc, twoReaderParams, bindArgs, evalStmtFuel,
      evalStmtWith, evalExpr, litVal, envExtend, sumTwoFwd,
      henv, hloopS, hret, hle]

/-- `emit_correct` for `sum_two` at the default fuel. -/
theorem emit_correct_sumTwo (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (hle₁ : nv.toNat ≤ l₁.length) (hle₂ : nv.toNat ≤ l₂.length)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] =
      sumTwoFwd l₁ l₂ nv := by
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  exact evalFuncFuel_sumTwo EVAL_FUEL l₁ l₂ nv hle₁ hle₂ h32 hfuel

/-- OOB corollary: over-long lengths fail loudly on both sides
    (past *either* array). -/
theorem evalFuncFuel_sumTwo_oob (F : Nat) (l₁ l₂ : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : min l₁.length l₂.length < nv.toNat)
    (hmin32 : min l₁.length l₂.length < 2 ^ 32)
    (hF : min l₁.length l₂.length + 1 ≤ F) :
    evalFuncFuel F sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] =
      .error .OOB := by
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]
      = mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0) := rfl
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0)) =
          .error .OOB :=
      sumTwoWhile_oob l₁ l₂ nv 0 0 (BitVec.ofNat 32 0)
        (Nat.zero_le _) hlt hmin32 (by cir_fuel)
    simp [evalFuncFuel, sumTwoFunc, twoReaderParams, bindArgs, evalStmtFuel,
      evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
      henv, hloopH0]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumTwoWhile (mkSumTwoEnv l₁ l₂ nv 0 (BitVec.ofNat 32 0)) =
          .error .OOB :=
      sumTwoWhile_oob l₁ l₂ nv (F + 1) 0 (BitVec.ofNat 32 0)
        (Nat.zero_le _) hlt hmin32 (by cir_fuel)
    simp [evalFuncFuel, sumTwoFunc, twoReaderParams, bindArgs, evalStmtFuel,
      evalStmtWith, evalExpr, litVal, envExtend,
      henv, hloopS]

/-- OOB corollary at the default fuel. -/
theorem emit_correct_sumTwo_oob (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32)
    (hlt : min l₁.length l₂.length < nv.toNat)
    (hfuel : min l₁.length l₂.length + 1 ≤ EVAL_FUEL) :
    evalFunc sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 nv] = .error .OOB := by
  have hmin32 : min l₁.length l₂.length < 2 ^ 32 := by cir_fuel
  exact evalFuncFuel_sumTwo_oob EVAL_FUEL l₁ l₂ nv hlt hmin32 hfuel
