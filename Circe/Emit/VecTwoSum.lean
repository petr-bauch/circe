import Circe.Emit.VecAt
import Circe.Emit.VecBinarySearch

/-
V2 brute-force two-sum over `std::vector<int>` (nested half-open
loops, early `IPair` return).

Corpus: `tests/cpp/vec_two_sum.cpp` → `tests/cir/vec_two_sum.cir`.
Shape: `n = size`, outer `while (i < n)` with `ult` guard, inner
`j = i + 1`, inner `while (j < n)`, element reads via bare
`stdVecAt` (indices `< n ≤ len`, no fused guard — unlike V1 the
reads sit in a nested body where dead `.fail` branches would
double), checked `i32` add (`nsw`, overflow is a loud `Overflow`
leg, the `vec_at_sum` precedent), `ueq` against `target`, hit
returns `IPair` of the explicitly-narrowed indices (`(int)i`,
`(int)j` in the corpus, `.i32ofU64` in the model — `structVal`
holds 32-bit words only, so a u64 pair is inexpressible), miss
returns the narrowed `(n, n)` (`find_eq` house style generalized
to pairs). Sortedness is irrelevant (brute force). Reuses the V1
`evalStmtFuel_seq_return` / `ofNat64_toNat'` helpers by import
(V1 stays untouched).
-/

/-- Function name (Itanium mangling of a `vec_two_sum` free function
taking `const vector<int>&` + `int`, returning `IPair`). -/
def vecTwoSumName : String := "_Z11vec_two_sumRKSt6vectorIiSaIiEEi"

/-- Inner sum: checked `i32` add of the two `at()` reads. -/
def vecTwoSumAdd : CExpr :=
  (.add (.stdVecAt "s" (.var "i")) (.stdVecAt "s" (.var "j")))

/-- Hit pair: explicitly narrowed indices. -/
def vecTwoSumHit : CExpr :=
  (.pair (.i32ofU64 (.var "i")) (.i32ofU64 (.var "j")))

/-- Miss pair: narrowed `(n, n)`. -/
def vecTwoSumMiss : CExpr :=
  (.pair (.i32ofU64 (.var "n")) (.i32ofU64 (.var "n")))

/-- Inner body: hit-return or `j++`. -/
def vecTwoSumInnerBody : CStmt :=
  (.if_ (.ueq vecTwoSumAdd (.var "target"))
    (.return_ vecTwoSumHit)
    (.assign "j" (.uadd (.var "j") (.lit (.u64 1)))))

/-- Inner loop `while (j < n) body`. -/
def vecTwoSumInner : CStmt :=
  (.while_ (.ult (.var "j") (.var "n")) vecTwoSumInnerBody)

/-- Outer body: reset `j`, run inner, `i++`. -/
def vecTwoSumOuterBody : CStmt :=
  (.seq (.assign "j" (.uadd (.var "i") (.lit (.u64 1))))
    (.seq vecTwoSumInner
      (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))))

/-- Outer loop `while (i < n) body`. -/
def vecTwoSumOuter : CStmt :=
  (.while_ (.ult (.var "i") (.var "n")) vecTwoSumOuterBody)

/-- Whole function: `let_`-prelude binds `n/i/j` (`assign` needs
bound targets), outer loop, miss returns the narrowed `(n, n)`. -/
def vecTwoSumFunc : Func :=
  ⟨vecTwoSumName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "target", ty := .i 32, role := .owned }],
   .struct "IPair" [.i 32, .i 32],
   (.seq (.let_ "n" (.u 64) (.stdVecLen "s"))
     (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq vecTwoSumOuter
           (.return_ vecTwoSumMiss)))))⟩

/-- Loop environment (u64 indices/bound, `i32` target). Binding order
matches the prelude `let_` cons chain so the entry bridge is `rfl`. -/
def mkTwoSumEnv (l : List (BitVec 32)) (n i j : Nat) (t : BitVec 32) : Env :=
  [("j", .u64 (BitVec.ofNat 64 j)), ("i", .u64 (BitVec.ofNat 64 i)),
   ("n", .u64 (BitVec.ofNat 64 n)),
   ("s", .stdVecVal l), ("target", .i32 t)]

@[simp] theorem mkTwoSumEnv_j (l : List (BitVec 32)) (n i j : Nat) (t : BitVec 32) :
    envLookup (mkTwoSumEnv l n i j t) "j" = some (.u64 (BitVec.ofNat 64 j)) := by
  simp [mkTwoSumEnv, envLookup]

@[simp] theorem mkTwoSumEnv_i (l : List (BitVec 32)) (n i j : Nat) (t : BitVec 32) :
    envLookup (mkTwoSumEnv l n i j t) "i" = some (.u64 (BitVec.ofNat 64 i)) := by
  simp [mkTwoSumEnv, envLookup, show ("i" : String) ≠ "j" by decide]

@[simp] theorem mkTwoSumEnv_n (l : List (BitVec 32)) (n i j : Nat) (t : BitVec 32) :
    envLookup (mkTwoSumEnv l n i j t) "n" = some (.u64 (BitVec.ofNat 64 n)) := by
  simp [mkTwoSumEnv, envLookup, show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "i" by decide]

@[simp] theorem mkTwoSumEnv_s (l : List (BitVec 32)) (n i j : Nat) (t : BitVec 32) :
    envLookup (mkTwoSumEnv l n i j t) "s" = some (.stdVecVal l) := by
  simp [mkTwoSumEnv, envLookup, show ("s" : String) ≠ "j" by decide,
    show ("s" : String) ≠ "i" by decide,
    show ("s" : String) ≠ "n" by decide]

@[simp] theorem mkTwoSumEnv_target (l : List (BitVec 32)) (n i j : Nat) (t : BitVec 32) :
    envLookup (mkTwoSumEnv l n i j t) "target" = some (.i32 t) := by
  simp [mkTwoSumEnv, envLookup, show ("target" : String) ≠ "j" by decide,
    show ("target" : String) ≠ "i" by decide,
    show ("target" : String) ≠ "n" by decide,
    show ("target" : String) ≠ "s" by decide]

/-- `assign` updates restore the constructor shape. -/
@[simp] theorem twoSumEnv_update_i (l : List (BitVec 32)) (n i i' j : Nat) (t : BitVec 32) :
    envUpdate (mkTwoSumEnv l n i j t) "i" (.u64 (BitVec.ofNat 64 i')) =
      some (mkTwoSumEnv l n i' j t) := by
  simp [mkTwoSumEnv, envUpdate, show ("i" : String) ≠ "j" by decide]

@[simp] theorem twoSumEnv_update_j (l : List (BitVec 32)) (n i j j' : Nat) (t : BitVec 32) :
    envUpdate (mkTwoSumEnv l n i j t) "j" (.u64 (BitVec.ofNat 64 j')) =
      some (mkTwoSumEnv l n i j' t) := by
  simp [mkTwoSumEnv, envUpdate]

/-- `add` on two `i32`-valued expressions forwards to
`checkedAddI32` (local mirror of `evalExpr_add_lit`, needed for
the sum of two reads). -/
theorem evalExpr_add_i32s (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 32)
    (h₁ : evalExpr e₁ ρ = .ok (.i32 x))
    (h₂ : evalExpr e₂ ρ = .ok (.i32 y)) :
    evalExpr (.add e₁ e₂) ρ = (checkedAddI32 x y).map .i32 := by
  simp [evalExpr, h₁, h₂]

/-- `if_` propagates a condition error (no named lemma exists —
same shape as the `seq` composition lemmas). -/
theorem evalStmtFuel_if_err (f : Nat) (c : CExpr) (t e : CStmt)
    (ρ : Env) (err : Panic)
    (h : evalExpr c ρ = .error err) :
    evalStmtFuel f (.if_ c t e) ρ = .error err := by
  cases f with
  | zero =>
    simp only [evalStmtFuel, evalStmtZero] at h ⊢
    simp only [evalStmtWith, h]
  | succ g =>
    simp only [evalStmtFuel] at h ⊢
    simp only [evalStmtWith, h]

/-- Outer-guard evaluation: `ult i n` is `decide (i < n)`. -/
theorem vecTwoSumOuterGuard_eval (l : List (BitVec 32)) (n i j : Nat)
    (t : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hn : n ≤ l.length) (hi : i ≤ l.length) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkTwoSumEnv l n i j t) =
      .ok (.b (decide (i < n))) := by
  have hiE := evalExpr_var_hit _ _ _ (mkTwoSumEnv_i l n i j t)
  have hnE := evalExpr_var_hit _ _ _ (mkTwoSumEnv_n l n i j t)
  have h := evalExpr_ult_u64 _ _ _ _ _ hiE hnE
  have huv : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 n) =
      decide (i < n) := by
    rw [BitVec.ult_eq_decide,
      ofNat64_toNat' i (Nat.lt_of_le_of_lt hi hlen),
      ofNat64_toNat' n (Nat.lt_of_le_of_lt hn hlen)]
  rwa [huv] at h

/-- Inner-guard evaluation: `ult j n` is `decide (j < n)`. -/
theorem vecTwoSumInnerGuard_eval (l : List (BitVec 32)) (n i j : Nat)
    (t : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hn : n ≤ l.length) (hj : j ≤ l.length) :
    evalExpr (.ult (.var "j") (.var "n"))
        (mkTwoSumEnv l n i j t) =
      .ok (.b (decide (j < n))) := by
  have hjE := evalExpr_var_hit _ _ _ (mkTwoSumEnv_j l n i j t)
  have hnE := evalExpr_var_hit _ _ _ (mkTwoSumEnv_n l n i j t)
  have h := evalExpr_ult_u64 _ _ _ _ _ hjE hnE
  have huv : (BitVec.ofNat 64 j).ult (BitVec.ofNat 64 n) =
      decide (j < n) := by
    rw [BitVec.ult_eq_decide,
      ofNat64_toNat' j (Nat.lt_of_le_of_lt hj hlen),
      ofNat64_toNat' n (Nat.lt_of_le_of_lt hn hlen)]
  rwa [huv] at h

/-- Midpoint-free read at `i`: delivers the element word. -/
theorem vecTwoSumReadI_hit (l : List (BitVec 32)) (n i j : Nat)
    (t : BitVec 32) (x : BitVec 32)
    (hget : l[(BitVec.ofNat 64 i).toNat]? = some x) :
    evalExpr (.stdVecAt "s" (.var "i")) (mkTwoSumEnv l n i j t) =
      .ok (.i32 x) :=
  evalExpr_stdVecAt_some "s" _ _ _ _ _
    (mkTwoSumEnv_s l n i j t)
    (evalExpr_var_hit _ _ _ (mkTwoSumEnv_i l n i j t)) hget

/-- Read at `j`: delivers the element word. -/
theorem vecTwoSumReadJ_hit (l : List (BitVec 32)) (n i j : Nat)
    (t : BitVec 32) (y : BitVec 32)
    (hget : l[(BitVec.ofNat 64 j).toNat]? = some y) :
    evalExpr (.stdVecAt "s" (.var "j")) (mkTwoSumEnv l n i j t) =
      .ok (.i32 y) :=
  evalExpr_stdVecAt_some "s" _ _ _ _ _
    (mkTwoSumEnv_s l n i j t)
    (evalExpr_var_hit _ _ _ (mkTwoSumEnv_j l n i j t)) hget

/-- `checkedAddI32` errors are always `Overflow` (the definition
    has no other error leg). -/
theorem checkedAddI32_err_eq (x y : BitVec 32) (e : Panic)
    (h : checkedAddI32 x y = .error e) : e = .Overflow := by
  by_cases hc : inInt32Range (x.toInt + y.toInt)
  · simp [checkedAddI32, hc] at h
  · simp [checkedAddI32, hc] at h
    exact Eq.symm (by simpa using h)

/-! ## Reference search (fuel-bounded, mirrors the statement fuel) -/

/-- Search outcome: hit indices, miss, or `i32`-add overflow. -/
inductive TwoSumOutcome where
  | hit : Nat → Nat → TwoSumOutcome
  | miss : TwoSumOutcome
  | overflow : TwoSumOutcome
  deriving DecidableEq, Repr

/-- Impossible `getElem?` is contradictory under a membership proof
    (both reference matches are non-dependent, so `simp`/`rw`
    rewrite freely; V1 `binSearch_getElem_ne_none` precedent). -/
theorem twoSum_getElem_ne_none (l : List (BitVec 32)) (k : Nat)
    (hmem : k < l.length) (h : l[k]? = none) : False := by
  have hg : l[k]? = some l[k] := List.getElem?_eq_getElem hmem
  rw [hg] at h
  simp at h

/-- Inner reference: fuel-bounded scan of `j` over `[j, n)` with `i`
    fixed. Fuel-`0` and `none` arms are unreachable under the loop
    invariants; they forward to `.miss` and proofs close them by
    contradiction. -/
def twoSumInner (l : List (BitVec 32)) (t : BitVec 32) (n : Nat) :
    Nat → Nat → Nat → TwoSumOutcome
  | 0, _, _ => .miss
  | fuel + 1, i, j =>
    if _ : j < n then
      match l[i]? with
      | some x =>
        match l[j]? with
        | some y =>
          match checkedAddI32 x y with
          | .ok s => if s == t then .hit i j else twoSumInner l t n fuel i (j + 1)
          | .error _ => .overflow
        | none => .miss
      | none => .miss
    else .miss

/-- Outer reference: fuel-bounded scan of `i` over `[i, n)`. -/
def twoSumOuter (l : List (BitVec 32)) (t : BitVec 32) (n : Nat) :
    Nat → Nat → TwoSumOutcome
  | 0, _ => .miss
  | fuel + 1, i =>
    if _ : i < n then
      match twoSumInner l t n fuel i (i + 1) with
      | .hit a b => .hit a b
      | .miss => twoSumOuter l t n fuel (i + 1)
      | .overflow => .overflow
    else .miss

/-- Forward model over the entry environment. -/
def vecTwoSumFwd (l : List (BitVec 32)) (t : BitVec 32) : Result Value :=
  match twoSumOuter l t l.length (l.length + 1) 0 with
  | .hit a b => .ok (.structVal "IPair" [(("a", BitVec.ofNat 32 a)), (("b", BitVec.ofNat 32 b))])
  | .miss => .ok (.structVal "IPair" [(("a", BitVec.ofNat 32 l.length)), (("b", BitVec.ofNat 32 l.length))])
  | .overflow => .error .Overflow

/-! ## Body steps (fuel-generalized; both bodies are loop-free) -/

/-- Inner-hit step: reads hit, add succeeds, `s == t`: returns the
    narrowed pair. -/
theorem vecTwoSumInnerBody_hit (F : Nat) (l : List (BitVec 32))
    (n i j : Nat) (t : BitVec 32)
    (x y : BitVec 32)
    (hgeti : l[(BitVec.ofNat 64 i).toNat]? = some x)
    (hgetj : l[(BitVec.ofNat 64 j).toNat]? = some y)
    (s : BitVec 32)
    (hadd : checkedAddI32 x y = .ok s)
    (heq : (s == t) = true) :
    evalStmtFuel F vecTwoSumInnerBody (mkTwoSumEnv l n i j t) =
      .ok (mkTwoSumEnv l n i j t,
        .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 ((BitVec.ofNat 64 i).toNat))),
          (("b", BitVec.ofNat 32 ((BitVec.ofNat 64 j).toNat)))])) := by
  have hxi := vecTwoSumReadI_hit l n i j t x hgeti
  have hyj := vecTwoSumReadJ_hit l n i j t y hgetj
  have haddE := evalExpr_add_i32s _ _ _ _ _ hxi hyj
  rw [hadd] at haddE
  have hueq : evalExpr (.ueq vecTwoSumAdd (.var "target"))
      (mkTwoSumEnv l n i j t) = .ok (.b true) := by
    have ht := evalExpr_var_hit _ _ _ (mkTwoSumEnv_target l n i j t)
    have h := evalExpr_ueq_i32 _ _ _ _ _ haddE ht
    rwa [heq] at h
  have hni : evalExpr (.i32ofU64 (.var "i")) (mkTwoSumEnv l n i j t) =
      .ok (.i32 (BitVec.ofNat 32 ((BitVec.ofNat 64 i).toNat))) :=
    evalExpr_i32ofU64_ok _ _ _ (evalExpr_var_hit _ _ _ (mkTwoSumEnv_i l n i j t))
  have hnj : evalExpr (.i32ofU64 (.var "j")) (mkTwoSumEnv l n i j t) =
      .ok (.i32 (BitVec.ofNat 32 ((BitVec.ofNat 64 j).toNat))) :=
    evalExpr_i32ofU64_ok _ _ _ (evalExpr_var_hit _ _ _ (mkTwoSumEnv_j l n i j t))
  have hpair := evalExpr_pair_ok _ _ _ _ _ hni hnj
  have hret := evalStmtFuel_return F _ _ _ hpair
  simp only [vecTwoSumInnerBody]
  rw [evalStmtFuel_if_true F _ _ _ _ hueq]
  exact hret

/-- Inner-miss step: add succeeds, `s != t`: `j++`, falls through. -/
theorem vecTwoSumInnerBody_next (F : Nat) (l : List (BitVec 32))
    (n i j : Nat) (t : BitVec 32)
    (x y : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hn : n ≤ l.length) (hjlt : j < n)
    (hgeti : l[(BitVec.ofNat 64 i).toNat]? = some x)
    (hgetj : l[(BitVec.ofNat 64 j).toNat]? = some y)
    (s : BitVec 32)
    (hadd : checkedAddI32 x y = .ok s)
    (hne : (s == t) = false) :
    evalStmtFuel F vecTwoSumInnerBody (mkTwoSumEnv l n i j t) =
      .ok (mkTwoSumEnv l n i (j + 1) t, .fellThrough) := by
  have hxi := vecTwoSumReadI_hit l n i j t x hgeti
  have hyj := vecTwoSumReadJ_hit l n i j t y hgetj
  have haddE := evalExpr_add_i32s _ _ _ _ _ hxi hyj
  rw [hadd] at haddE
  have hueq : evalExpr (.ueq vecTwoSumAdd (.var "target"))
      (mkTwoSumEnv l n i j t) = .ok (.b false) := by
    have ht := evalExpr_var_hit _ _ _ (mkTwoSumEnv_target l n i j t)
    have h := evalExpr_ueq_i32 _ _ _ _ _ haddE ht
    rwa [hne] at h
  have hjE := evalExpr_var_hit _ _ _ (mkTwoSumEnv_j l n i j t)
  have honeE : evalExpr (.lit (.u64 (1 : BitVec 64)))
      (mkTwoSumEnv l n i j t) = .ok (.u64 1) := evalExpr_lit _ _
  have haddJ := evalExpr_uadd_u64 _ _ _ _ _ hjE honeE
  have hj1 : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,
      ofNat64_toNat' j (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt hjlt) hn) hlen)]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1, ofNat64_toNat' (j + 1) (by
      have : j + 1 ≤ l.length := Nat.le_trans (Nat.succ_le_of_lt hjlt) hn
      exact Nat.lt_of_le_of_lt this hlen)]
    exact Nat.mod_eq_of_lt (by
      have : j + 1 ≤ l.length := Nat.le_trans (Nat.succ_le_of_lt hjlt) hn
      exact Nat.lt_of_le_of_lt this hlen)
  rw [hj1] at haddJ
  have hassign_j := evalStmtFuel_assign F _ _ _ _ _ haddJ
    (twoSumEnv_update_j l n i j _ t)
  simp only [vecTwoSumInnerBody]
  rw [evalStmtFuel_if_false F _ _ _ _ hueq]
  exact hassign_j

/-- `ueq` propagates a left-operand error (local; the lit-only
mismatch lemmas do not cover expression operands). -/
theorem evalExpr_ueq_err (e₁ e₂ : CExpr) (ρ : Env) (err : Panic)
    (h : evalExpr e₁ ρ = .error err) :
    evalExpr (.ueq e₁ e₂) ρ = .error err := by
  simp [evalExpr, h]

/-- Inner-overflow step: the add overflows, the `ueq` condition
errors, the body errors with the same panic. -/
theorem vecTwoSumInnerBody_overflow (F : Nat) (l : List (BitVec 32))
    (n i j : Nat) (t : BitVec 32)
    (x y : BitVec 32)
    (hgeti : l[(BitVec.ofNat 64 i).toNat]? = some x)
    (hgetj : l[(BitVec.ofNat 64 j).toNat]? = some y)
    (e : Panic)
    (hadd : checkedAddI32 x y = .error e) :
    evalStmtFuel F vecTwoSumInnerBody (mkTwoSumEnv l n i j t) = .error e := by
  have hxi := vecTwoSumReadI_hit l n i j t x hgeti
  have hyj := vecTwoSumReadJ_hit l n i j t y hgetj
  have haddE := evalExpr_add_i32s _ _ _ _ _ hxi hyj
  rw [hadd] at haddE
  have haddE' : evalExpr (.add (.stdVecAt "s" (.var "i")) (.stdVecAt "s" (.var "j")))
      (mkTwoSumEnv l n i j t) = .error e := haddE
  have hueq : evalExpr (.ueq vecTwoSumAdd (.var "target"))
      (mkTwoSumEnv l n i j t) = .error e :=
    evalExpr_ueq_err _ _ _ _ haddE'
  simp only [vecTwoSumInnerBody]
  exact evalStmtFuel_if_err F _ _ _ _ _ hueq

/-- Inner-loop clean exit (guard false): env unchanged. -/
theorem vecTwoSumInner_exit (F : Nat) (l : List (BitVec 32))
    (n i j : Nat) (t : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hn : n ≤ l.length) (hj : j ≤ l.length)
    (hge : n ≤ j) :
    evalStmtFuel (F + 1) vecTwoSumInner (mkTwoSumEnv l n i j t) =
      .ok (mkTwoSumEnv l n i j t, .fellThrough) := by
  have hcond : evalExpr (.ult (.var "j") (.var "n"))
      (mkTwoSumEnv l n i j t) = .ok (.b false) := by
    have h := vecTwoSumInnerGuard_eval l n i j t hlen hn hj
    have hfalse : decide (j < n) = false :=
      decide_eq_false (Nat.not_lt.mpr hge)
    rwa [hfalse] at h
  simp [vecTwoSumInner, evalStmtFuel, evalStmtSuccHandler,
    evalStmtWith, hcond]

/-- Outer-loop clean exit (guard false): env unchanged. -/
theorem vecTwoSumOuter_exit (F : Nat) (l : List (BitVec 32))
    (n i j : Nat) (t : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hn : n ≤ l.length) (hi : i ≤ l.length)
    (hge : n ≤ i) :
    evalStmtFuel (F + 1) vecTwoSumOuter (mkTwoSumEnv l n i j t) =
      .ok (mkTwoSumEnv l n i j t, .fellThrough) := by
  have hcond : evalExpr (.ult (.var "i") (.var "n"))
      (mkTwoSumEnv l n i j t) = .ok (.b false) := by
    have h := vecTwoSumOuterGuard_eval l n i j t hlen hn hi
    have hfalse : decide (i < n) = false :=
      decide_eq_false (Nat.not_lt.mpr hge)
    rwa [hfalse] at h
  simp [vecTwoSumOuter, evalStmtFuel, evalStmtSuccHandler,
    evalStmtWith, hcond]

/-- `j := i + 1` step (outer prelude per iteration). -/
theorem vecTwoSumAssignJ_reset (F : Nat) (l : List (BitVec 32))
    (n i j : Nat) (t : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hn : n ≤ l.length) (hilt : i < n) :
    evalStmtFuel F (.assign "j" (.uadd (.var "i") (.lit (.u64 1))))
        (mkTwoSumEnv l n i j t) =
      .ok (mkTwoSumEnv l n i (i + 1) t, .fellThrough) := by
  have hiE := evalExpr_var_hit _ _ _ (mkTwoSumEnv_i l n i j t)
  have honeE : evalExpr (.lit (.u64 (1 : BitVec 64)))
      (mkTwoSumEnv l n i j t) = .ok (.u64 1) := evalExpr_lit _ _
  have hadd := evalExpr_uadd_u64 _ _ _ _ _ hiE honeE
  have hi1 : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,
      ofNat64_toNat' i (Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.lt_of_lt_of_le hilt hn)) hlen)]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1, ofNat64_toNat' (i + 1) (by
      have : i + 1 ≤ l.length :=
        Nat.le_trans (Nat.succ_le_of_lt hilt) hn
      exact Nat.lt_of_le_of_lt this hlen)]
    exact Nat.mod_eq_of_lt (by
      have : i + 1 ≤ l.length :=
        Nat.le_trans (Nat.succ_le_of_lt hilt) hn
      exact Nat.lt_of_le_of_lt this hlen)
  rw [hi1] at hadd
  exact evalStmtFuel_assign F _ _ _ _ _ hadd
    (twoSumEnv_update_j l n i j _ t)

/-- `i := i + 1` step (outer postlude per iteration). -/
theorem vecTwoSumAssignI_incr (F : Nat) (l : List (BitVec 32))
    (n i j : Nat) (t : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hn : n ≤ l.length) (hilt : i < n) :
    evalStmtFuel F (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
        (mkTwoSumEnv l n i j t) =
      .ok (mkTwoSumEnv l n (i + 1) j t, .fellThrough) := by
  have hiE := evalExpr_var_hit _ _ _ (mkTwoSumEnv_i l n i j t)
  have honeE : evalExpr (.lit (.u64 (1 : BitVec 64)))
      (mkTwoSumEnv l n i j t) = .ok (.u64 1) := evalExpr_lit _ _
  have hadd := evalExpr_uadd_u64 _ _ _ _ _ hiE honeE
  have hi1 : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,
      ofNat64_toNat' i (Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.lt_of_lt_of_le hilt hn)) hlen)]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1, ofNat64_toNat' (i + 1) (by
      have : i + 1 ≤ l.length :=
        Nat.le_trans (Nat.succ_le_of_lt hilt) hn
      exact Nat.lt_of_le_of_lt this hlen)]
    exact Nat.mod_eq_of_lt (by
      have : i + 1 ≤ l.length :=
        Nat.le_trans (Nat.succ_le_of_lt hilt) hn
      exact Nat.lt_of_le_of_lt this hlen)
  rw [hi1] at hadd
  exact evalStmtFuel_assign F _ _ _ _ _ hadd
    (twoSumEnv_update_i l n i _ j t)

/-! ## Inner-loop correctness (fuel-generalized; `n - j` is the measure) -/

/-- Inner-hit soundness: reference hit ⟹ the loop returns that pair. -/
theorem vecTwoSumInner_hit (l : List (BitVec 32)) (t : BitVec 32) (n : Nat)
    (F i j : Nat) (a b : Nat)
    (hn : n ≤ l.length) (hjle : j ≤ n) (hilt : i < n)
    (hl64 : l.length < 2 ^ 64)
    (hF : n - j + 1 ≤ F)
    (hhit : twoSumInner l t n F i j = .hit a b) :
    ∃ ρ', evalStmtFuel F vecTwoSumInner (mkTwoSumEnv l n i j t) =
      .ok (ρ', .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 a)), (("b", BitVec.ofNat 32 b))])) := by
  induction F generalizing i j a b with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hjlt : j < n
    · have hi64 : i < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt hilt) hn) hl64
      have hj64 : j < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_trans hjle hn) hl64
      have hiN : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat' i hi64
      have hjN : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat' j hj64
      have hmemi : i < l.length := Nat.lt_of_lt_of_le hilt hn
      have hmemj : j < l.length := Nat.lt_of_lt_of_le hjlt hn
      cases hgeti : l[i]? with
      | none => exact (twoSum_getElem_ne_none l i hmemi hgeti).elim
      | some x =>
        cases hgetj : l[j]? with
        | none => exact (twoSum_getElem_ne_none l j hmemj hgetj).elim
        | some y =>
          have hcond : evalExpr (.ult (.var "j") (.var "n"))
              (mkTwoSumEnv l n i j t) = .ok (.b true) := by
            have h := vecTwoSumInnerGuard_eval l n i j t hl64 hn
              (Nat.le_trans hjle hn)
            rwa [decide_eq_true hjlt] at h
          cases hadd : checkedAddI32 x y with
          | error e =>
            have hbin : twoSumInner l t n (F + 1) i j = .overflow := by
              simp only [twoSumInner, hjlt]
              rw [hgeti, hgetj]
              simp [hadd]
            rw [hbin] at hhit
            cases hhit
          | ok s =>
            by_cases heq : (s == t) = true
            · have hbin : twoSumInner l t n (F + 1) i j = .hit i j := by
                simp only [twoSumInner, hjlt]
                rw [hgeti, hgetj]
                simp [hadd, heq]
              rw [hbin] at hhit
              simp only [TwoSumOutcome.hit.injEq] at hhit
              obtain ⟨rfl, rfl⟩ := hhit
              have hgeti' : l[(BitVec.ofNat 64 i).toNat]? = some x := by
                rw [hiN]; exact hgeti
              have hgetj' : l[(BitVec.ofNat 64 j).toNat]? = some y := by
                rw [hjN]; exact hgetj
              have hbody := vecTwoSumInnerBody_hit F l n i j t x y
                hgeti' hgetj' s hadd heq
              have hstep : evalStmtFuel (F + 1) vecTwoSumInner
                  (mkTwoSumEnv l n i j t) =
                  .ok (mkTwoSumEnv l n i j t,
                    .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 ((BitVec.ofNat 64 i).toNat))),
                      (("b", BitVec.ofNat 32 ((BitVec.ofNat 64 j).toNat)))])) := by
                cir_unfold_leaf (vecTwoSumInner, hcond, hbody)
              rw [hiN, hjN] at hstep
              exact ⟨_, hstep⟩
            · have hne : (s == t) = false := Bool.eq_false_of_ne_true heq
              have hbin : twoSumInner l t n (F + 1) i j =
                  twoSumInner l t n F i (j + 1) := by
                simp only [twoSumInner, hjlt]
                rw [hgeti, hgetj]
                simp [hadd, hne]
              rw [hbin] at hhit
              have hgeti' : l[(BitVec.ofNat 64 i).toNat]? = some x := by
                rw [hiN]; exact hgeti
              have hgetj' : l[(BitVec.ofNat 64 j).toNat]? = some y := by
                rw [hjN]; exact hgetj
              have hbody := vecTwoSumInnerBody_next F l n i j t x y
                hl64 hn hjlt hgeti' hgetj' s hadd hne
              have hstep : evalStmtFuel (F + 1) vecTwoSumInner
                  (mkTwoSumEnv l n i j t) =
                  evalStmtFuel F vecTwoSumInner
                    (mkTwoSumEnv l n i (j + 1) t) := by
                cir_unfold_leaf (vecTwoSumInner, hcond, hbody)
              rw [hstep]
              exact ih i (j + 1) a b (hjle := by omega) (hilt := hilt) (hF := by omega) (hhit := hhit)
    · have hmiss : twoSumInner l t n (F + 1) i j = .miss := by
        simp [twoSumInner, hjlt]
      rw [hmiss] at hhit
      cases hhit

/-- Inner-miss soundness: reference miss ⟹ the loop falls through
    with `j = n` (exact env; `i` is never assigned by the inner
    body, so the outer induction chains without framing). -/
theorem vecTwoSumInner_miss (l : List (BitVec 32)) (t : BitVec 32) (n : Nat)
    (F i j : Nat)
    (hn : n ≤ l.length) (hjle : j ≤ n) (hilt : i < n)
    (hl64 : l.length < 2 ^ 64)
    (hF : n - j + 1 ≤ F)
    (hmiss : twoSumInner l t n F i j = .miss) :
    evalStmtFuel F vecTwoSumInner (mkTwoSumEnv l n i j t) =
      .ok (mkTwoSumEnv l n i n t, .fellThrough) := by
  induction F generalizing i j with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hjlt : j < n
    · have hi64 : i < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt hilt) hn) hl64
      have hj64 : j < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_trans hjle hn) hl64
      have hiN : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat' i hi64
      have hjN : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat' j hj64
      have hmemi : i < l.length := Nat.lt_of_lt_of_le hilt hn
      have hmemj : j < l.length := Nat.lt_of_lt_of_le hjlt hn
      cases hgeti : l[i]? with
      | none => exact (twoSum_getElem_ne_none l i hmemi hgeti).elim
      | some x =>
        cases hgetj : l[j]? with
        | none => exact (twoSum_getElem_ne_none l j hmemj hgetj).elim
        | some y =>
          have hcond : evalExpr (.ult (.var "j") (.var "n"))
              (mkTwoSumEnv l n i j t) = .ok (.b true) := by
            have h := vecTwoSumInnerGuard_eval l n i j t hl64 hn
              (Nat.le_trans hjle hn)
            rwa [decide_eq_true hjlt] at h
          cases hadd : checkedAddI32 x y with
          | error e =>
            have hbin : twoSumInner l t n (F + 1) i j = .overflow := by
              simp only [twoSumInner, hjlt]
              rw [hgeti, hgetj]
              simp [hadd]
            rw [hbin] at hmiss
            cases hmiss
          | ok s =>
            by_cases heq : (s == t) = true
            · have hbin : twoSumInner l t n (F + 1) i j = .hit i j := by
                simp only [twoSumInner, hjlt]
                rw [hgeti, hgetj]
                simp [hadd, heq]
              rw [hbin] at hmiss
              cases hmiss
            · have hne : (s == t) = false := Bool.eq_false_of_ne_true heq
              have hbin : twoSumInner l t n (F + 1) i j =
                  twoSumInner l t n F i (j + 1) := by
                simp only [twoSumInner, hjlt]
                rw [hgeti, hgetj]
                simp [hadd, hne]
              rw [hbin] at hmiss
              have hgeti' : l[(BitVec.ofNat 64 i).toNat]? = some x := by
                rw [hiN]; exact hgeti
              have hgetj' : l[(BitVec.ofNat 64 j).toNat]? = some y := by
                rw [hjN]; exact hgetj
              have hbody := vecTwoSumInnerBody_next F l n i j t x y
                hl64 hn hjlt hgeti' hgetj' s hadd hne
              have hstep : evalStmtFuel (F + 1) vecTwoSumInner
                  (mkTwoSumEnv l n i j t) =
                  evalStmtFuel F vecTwoSumInner
                    (mkTwoSumEnv l n i (j + 1) t) := by
                cir_unfold_leaf (vecTwoSumInner, hcond, hbody)
              rw [hstep]
              exact ih i (j + 1) (hjle := by omega) (hilt := hilt) (hF := by omega) (hmiss := hmiss)
    · have hjn : j = n := by omega
      rw [hjn]
      exact vecTwoSumInner_exit F l n i n t hl64 hn hn (Nat.le_refl _)

/-- Inner-overflow soundness: reference overflow ⟹ the loop errors
    with `Overflow` (the only `checkedAddI32` error leg). -/
theorem vecTwoSumInner_overflow (l : List (BitVec 32)) (t : BitVec 32)
    (n : Nat) (F i j : Nat)
    (hn : n ≤ l.length) (hjle : j ≤ n) (hilt : i < n)
    (hl64 : l.length < 2 ^ 64)
    (hF : n - j + 1 ≤ F)
    (hover : twoSumInner l t n F i j = .overflow) :
    evalStmtFuel F vecTwoSumInner (mkTwoSumEnv l n i j t) =
      .error .Overflow := by
  induction F generalizing i j with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hjlt : j < n
    · have hi64 : i < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_of_lt hilt) hn) hl64
      have hj64 : j < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (Nat.le_trans hjle hn) hl64
      have hiN : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat' i hi64
      have hjN : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat' j hj64
      have hmemi : i < l.length := Nat.lt_of_lt_of_le hilt hn
      have hmemj : j < l.length := Nat.lt_of_lt_of_le hjlt hn
      cases hgeti : l[i]? with
      | none => exact (twoSum_getElem_ne_none l i hmemi hgeti).elim
      | some x =>
        cases hgetj : l[j]? with
        | none => exact (twoSum_getElem_ne_none l j hmemj hgetj).elim
        | some y =>
          have hcond : evalExpr (.ult (.var "j") (.var "n"))
              (mkTwoSumEnv l n i j t) = .ok (.b true) := by
            have h := vecTwoSumInnerGuard_eval l n i j t hl64 hn
              (Nat.le_trans hjle hn)
            rwa [decide_eq_true hjlt] at h
          cases hadd : checkedAddI32 x y with
          | error e =>
            have hbin : twoSumInner l t n (F + 1) i j = .overflow := by
              simp only [twoSumInner, hjlt]
              rw [hgeti, hgetj]
              simp [hadd]
            rw [hbin] at hover
            have hgeti' : l[(BitVec.ofNat 64 i).toNat]? = some x := by
              rw [hiN]; exact hgeti
            have hgetj' : l[(BitVec.ofNat 64 j).toNat]? = some y := by
              rw [hjN]; exact hgetj
            have hbody := vecTwoSumInnerBody_overflow F l n i j t x y
              hgeti' hgetj' e hadd
            have hstep : evalStmtFuel (F + 1) vecTwoSumInner
                (mkTwoSumEnv l n i j t) = .error e := by
              cir_unfold_leaf (vecTwoSumInner, hcond, hbody)
            have hoe := checkedAddI32_err_eq x y e hadd
            subst hoe
            exact hstep
          | ok s =>
            by_cases heq : (s == t) = true
            · have hbin : twoSumInner l t n (F + 1) i j = .hit i j := by
                simp only [twoSumInner, hjlt]
                rw [hgeti, hgetj]
                simp [hadd, heq]
              rw [hbin] at hover
              cases hover
            · have hne : (s == t) = false := Bool.eq_false_of_ne_true heq
              have hbin : twoSumInner l t n (F + 1) i j =
                  twoSumInner l t n F i (j + 1) := by
                simp only [twoSumInner, hjlt]
                rw [hgeti, hgetj]
                simp [hadd, hne]
              rw [hbin] at hover
              have hstep : evalStmtFuel (F + 1) vecTwoSumInner
                  (mkTwoSumEnv l n i j t) =
                  evalStmtFuel F vecTwoSumInner
                    (mkTwoSumEnv l n i (j + 1) t) := by
                have hgeti' : l[(BitVec.ofNat 64 i).toNat]? = some x := by
                  rw [hiN]; exact hgeti
                have hgetj' : l[(BitVec.ofNat 64 j).toNat]? = some y := by
                  rw [hjN]; exact hgetj
                have hbody := vecTwoSumInnerBody_next F l n i j t x y
                  hl64 hn hjlt hgeti' hgetj' s hadd hne
                cir_unfold_leaf (vecTwoSumInner, hcond, hbody)
              rw [hstep]
              exact ih i (j + 1) (hjle := by omega) (hilt := hilt) (hF := by omega) (hover := hover)
    · have hmiss : twoSumInner l t n (F + 1) i j = .miss := by
        simp [twoSumInner, hjlt]
      rw [hmiss] at hover
      cases hover

/-! ## Outer-loop correctness (fuel-generalized; `n - i` is the measure) -/

/-- Outer-hit soundness: reference hit ⟹ the loop returns that pair. -/
theorem vecTwoSumOuter_hit (l : List (BitVec 32)) (t : BitVec 32) (n : Nat)
    (F i j0 : Nat) (a b : Nat)
    (hn : n ≤ l.length) (hile : i ≤ n)
    (hl64 : l.length < 2 ^ 64)
    (hF : n - i + 1 ≤ F)
    (hhit : twoSumOuter l t n F i = .hit a b) :
    ∃ ρ', evalStmtFuel F vecTwoSumOuter (mkTwoSumEnv l n i j0 t) =
      .ok (ρ', .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 a)), (("b", BitVec.ofNat 32 b))])) := by
  induction F generalizing i j0 a b with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hilt : i < n
    · have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkTwoSumEnv l n i j0 t) = .ok (.b true) := by
        have h := vecTwoSumOuterGuard_eval l n i j0 t hl64 hn
          (Nat.le_trans hile hn)
        rwa [decide_eq_true hilt] at h
      have hreset := vecTwoSumAssignJ_reset F l n i j0 t hl64 hn hilt
      cases hinner : twoSumInner l t n F i (i + 1) with
      | hit a' b' =>
        obtain ⟨ρ1, hinnerH⟩ := vecTwoSumInner_hit l t n F i (i + 1) a' b'
          hn (by omega : i + 1 ≤ n) hilt hl64 (by omega : n - (i + 1) + 1 ≤ F) hinner
        have hbin : twoSumOuter l t n (F + 1) i = .hit a' b' := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hhit
        simp only [TwoSumOutcome.hit.injEq] at hhit
        obtain ⟨rfl, rfl⟩ := hhit
        have hbody : evalStmtFuel F vecTwoSumOuterBody
            (mkTwoSumEnv l n i j0 t) =
            .ok (ρ1, .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 a')), (("b", BitVec.ofNat 32 b'))])) := by
          have hseq : evalStmtFuel F
              (.seq vecTwoSumInner
                (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))
              (mkTwoSumEnv l n i (i + 1) t) =
              .ok (ρ1, .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 a')), (("b", BitVec.ofNat 32 b'))])) :=
            evalStmtFuel_seq_return F _ _ _ _ _ hinnerH
          simp only [vecTwoSumOuterBody]
          rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hreset]
          exact hseq
        have hstep : evalStmtFuel (F + 1) vecTwoSumOuter
            (mkTwoSumEnv l n i j0 t) =
            .ok (ρ1, .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 a')), (("b", BitVec.ofNat 32 b'))])) := by
          cir_unfold_leaf (vecTwoSumOuter, hcond, hbody)
        exact ⟨_, hstep⟩
      | miss =>
        have hinnerM := vecTwoSumInner_miss l t n F i (i + 1)
          hn (by omega : i + 1 ≤ n) hilt hl64 (by omega : n - (i + 1) + 1 ≤ F) hinner
        have hbin : twoSumOuter l t n (F + 1) i =
            twoSumOuter l t n F (i + 1) := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hhit
        have hbody : evalStmtFuel F vecTwoSumOuterBody
            (mkTwoSumEnv l n i j0 t) =
            .ok (mkTwoSumEnv l n (i + 1) n t, .fellThrough) := by
          have hseq : evalStmtFuel F
              (.seq vecTwoSumInner
                (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))
              (mkTwoSumEnv l n i (i + 1) t) =
              .ok (mkTwoSumEnv l n (i + 1) n t, .fellThrough) := by
            rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hinnerM]
            exact vecTwoSumAssignI_incr F l n i n t hl64 hn hilt
          simp only [vecTwoSumOuterBody]
          rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hreset]
          exact hseq
        have hstep : evalStmtFuel (F + 1) vecTwoSumOuter
            (mkTwoSumEnv l n i j0 t) =
            evalStmtFuel F vecTwoSumOuter
              (mkTwoSumEnv l n (i + 1) n t) := by
          cir_unfold_leaf (vecTwoSumOuter, hcond, hbody)
        rw [hstep]
        exact ih (i + 1) n a b (hile := by omega) (hF := by omega) (hhit := hhit)
      | overflow =>
        have hbin : twoSumOuter l t n (F + 1) i = .overflow := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hhit
        cases hhit
    · have hmiss : twoSumOuter l t n (F + 1) i = .miss := by
        simp [twoSumOuter, hilt]
      rw [hmiss] at hhit
      cases hhit

/-- Outer-miss soundness: reference miss ⟹ the loop falls through
    with `n` intact (the trailing miss-pair reads it). -/
theorem vecTwoSumOuter_miss (l : List (BitVec 32)) (t : BitVec 32) (n : Nat)
    (F i j0 : Nat)
    (hn : n ≤ l.length) (hile : i ≤ n)
    (hl64 : l.length < 2 ^ 64)
    (hF : n - i + 1 ≤ F)
    (hmiss : twoSumOuter l t n F i = .miss) :
    ∃ ρ', evalStmtFuel F vecTwoSumOuter (mkTwoSumEnv l n i j0 t) =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "n" = some (.u64 (BitVec.ofNat 64 n)) := by
  induction F generalizing i j0 with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hilt : i < n
    · have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkTwoSumEnv l n i j0 t) = .ok (.b true) := by
        have h := vecTwoSumOuterGuard_eval l n i j0 t hl64 hn
          (Nat.le_trans hile hn)
        rwa [decide_eq_true hilt] at h
      have hreset := vecTwoSumAssignJ_reset F l n i j0 t hl64 hn hilt
      cases hinner : twoSumInner l t n F i (i + 1) with
      | hit a' b' =>
        have hbin : twoSumOuter l t n (F + 1) i = .hit a' b' := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hmiss
        cases hmiss
      | miss =>
        have hinnerM := vecTwoSumInner_miss l t n F i (i + 1)
          hn (by omega : i + 1 ≤ n) hilt hl64 (by omega : n - (i + 1) + 1 ≤ F) hinner
        have hbin : twoSumOuter l t n (F + 1) i =
            twoSumOuter l t n F (i + 1) := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hmiss
        have hbody : evalStmtFuel F vecTwoSumOuterBody
            (mkTwoSumEnv l n i j0 t) =
            .ok (mkTwoSumEnv l n (i + 1) n t, .fellThrough) := by
          have hseq : evalStmtFuel F
              (.seq vecTwoSumInner
                (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))
              (mkTwoSumEnv l n i (i + 1) t) =
              .ok (mkTwoSumEnv l n (i + 1) n t, .fellThrough) := by
            rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hinnerM]
            exact vecTwoSumAssignI_incr F l n i n t hl64 hn hilt
          simp only [vecTwoSumOuterBody]
          rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hreset]
          exact hseq
        have hstep : evalStmtFuel (F + 1) vecTwoSumOuter
            (mkTwoSumEnv l n i j0 t) =
            evalStmtFuel F vecTwoSumOuter
              (mkTwoSumEnv l n (i + 1) n t) := by
          cir_unfold_leaf (vecTwoSumOuter, hcond, hbody)
        rw [hstep]
        exact ih (i + 1) n (hile := by omega) (hF := by omega) (hmiss := hmiss)
      | overflow =>
        have hbin : twoSumOuter l t n (F + 1) i = .overflow := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hmiss
        cases hmiss
    · have hin : i = n := by omega
      rw [hin]
      exact ⟨_, vecTwoSumOuter_exit F l n n j0 t hl64 hn hn (Nat.le_refl _),
        mkTwoSumEnv_n l n n j0 t⟩

/-- Outer-overflow soundness: reference overflow ⟹ the loop errors
    with `Overflow`. -/
theorem vecTwoSumOuter_overflow (l : List (BitVec 32)) (t : BitVec 32)
    (n : Nat) (F i j0 : Nat)
    (hn : n ≤ l.length) (hile : i ≤ n)
    (hl64 : l.length < 2 ^ 64)
    (hF : n - i + 1 ≤ F)
    (hover : twoSumOuter l t n F i = .overflow) :
    evalStmtFuel F vecTwoSumOuter (mkTwoSumEnv l n i j0 t) =
      .error .Overflow := by
  induction F generalizing i j0 with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hilt : i < n
    · have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkTwoSumEnv l n i j0 t) = .ok (.b true) := by
        have h := vecTwoSumOuterGuard_eval l n i j0 t hl64 hn
          (Nat.le_trans hile hn)
        rwa [decide_eq_true hilt] at h
      have hreset := vecTwoSumAssignJ_reset F l n i j0 t hl64 hn hilt
      cases hinner : twoSumInner l t n F i (i + 1) with
      | hit a' b' =>
        have hbin : twoSumOuter l t n (F + 1) i = .hit a' b' := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hover
        cases hover
      | miss =>
        have hinnerM := vecTwoSumInner_miss l t n F i (i + 1)
          hn (by omega : i + 1 ≤ n) hilt hl64 (by omega : n - (i + 1) + 1 ≤ F) hinner
        have hbin : twoSumOuter l t n (F + 1) i =
            twoSumOuter l t n F (i + 1) := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hover
        have hbody : evalStmtFuel F vecTwoSumOuterBody
            (mkTwoSumEnv l n i j0 t) =
            .ok (mkTwoSumEnv l n (i + 1) n t, .fellThrough) := by
          have hseq : evalStmtFuel F
              (.seq vecTwoSumInner
                (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))
              (mkTwoSumEnv l n i (i + 1) t) =
              .ok (mkTwoSumEnv l n (i + 1) n t, .fellThrough) := by
            rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hinnerM]
            exact vecTwoSumAssignI_incr F l n i n t hl64 hn hilt
          simp only [vecTwoSumOuterBody]
          rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hreset]
          exact hseq
        have hstep : evalStmtFuel (F + 1) vecTwoSumOuter
            (mkTwoSumEnv l n i j0 t) =
            evalStmtFuel F vecTwoSumOuter
              (mkTwoSumEnv l n (i + 1) n t) := by
          cir_unfold_leaf (vecTwoSumOuter, hcond, hbody)
        rw [hstep]
        exact ih (i + 1) n (hile := by omega) (hF := by omega) (hover := hover)
      | overflow =>
        have hinnerO := vecTwoSumInner_overflow l t n F i (i + 1)
          hn (by omega : i + 1 ≤ n) hilt hl64 (by omega : n - (i + 1) + 1 ≤ F) hinner
        have hbin : twoSumOuter l t n (F + 1) i = .overflow := by
          simp only [twoSumOuter, hilt]
          rw [hinner]
          simp
        rw [hbin] at hover
        have hbody : evalStmtFuel F vecTwoSumOuterBody
            (mkTwoSumEnv l n i j0 t) = .error .Overflow := by
          have hseq : evalStmtFuel F
              (.seq vecTwoSumInner
                (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))
              (mkTwoSumEnv l n i (i + 1) t) = .error .Overflow :=
            evalStmtFuel_seq_err F _ _ _ _ hinnerO
          simp only [vecTwoSumOuterBody]
          rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hreset]
          exact hseq
        have hstep : evalStmtFuel (F + 1) vecTwoSumOuter
            (mkTwoSumEnv l n i j0 t) = .error .Overflow := by
          cir_unfold_leaf (vecTwoSumOuter, hcond, hbody)
        exact hstep
    · have hmiss : twoSumOuter l t n (F + 1) i = .miss := by
        simp [twoSumOuter, hilt]
      rw [hmiss] at hover
      cases hover

/-! ## Fuel agreement + `emit_correct` -/

/-- Inner search agrees on any two sufficient fuels. -/
theorem twoSumInner_fuel_ge (l : List (BitVec 32)) (t : BitVec 32)
    (n : Nat) (F₁ : Nat) :
    ∀ (F₂ i j : Nat),
    j ≤ n → n - j + 1 ≤ F₁ → n - j + 1 ≤ F₂ →
    twoSumInner l t n F₁ i j = twoSumInner l t n F₂ i j := by
  induction F₁ with
  | zero =>
    intro F₂ i j hjle h₁ _
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F₁ ih =>
    intro F₂ i j hjle h₁ h₂
    cases F₂ with
    | zero =>
      have hfalse : False := by omega
      exact hfalse.elim
    | succ F₂' =>
      by_cases hjlt : j < n
      · cases hgeti : l[i]? with
        | none => simp only [twoSumInner, hjlt]; rw [hgeti]
        | some x =>
          cases hgetj : l[j]? with
          | none => simp only [twoSumInner, hjlt]; rw [hgeti, hgetj]
          | some y =>
            cases hadd : checkedAddI32 x y with
            | error e =>
              simp only [twoSumInner, hjlt]
              rw [hgeti, hgetj]
              simp [hadd]
            | ok s =>
              by_cases heq : (s == t) = true
              · simp [twoSumInner, hjlt, hgeti, hgetj, hadd, heq]
              · have hne : (s == t) = false := Bool.eq_false_of_ne_true heq
                simp [twoSumInner, hjlt, hgeti, hgetj, hadd, hne]
                exact ih F₂' i (j + 1) (by omega) (by omega) (by omega)
      · simp [twoSumInner, hjlt]

/-- Outer search agrees on any two sufficient fuels (inner calls
agree by `twoSumInner_fuel_ge`). -/
theorem twoSumOuter_fuel_ge (l : List (BitVec 32)) (t : BitVec 32)
    (n : Nat) (F₁ : Nat) :
    ∀ (F₂ i : Nat),
    i ≤ n → n - i + 1 ≤ F₁ → n - i + 1 ≤ F₂ →
    twoSumOuter l t n F₁ i = twoSumOuter l t n F₂ i := by
  induction F₁ with
  | zero =>
    intro F₂ i hile h₁ _
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F₁ ih =>
    intro F₂ i hile h₁ h₂
    cases F₂ with
    | zero =>
      have hfalse : False := by omega
      exact hfalse.elim
    | succ F₂' =>
      by_cases hilt : i < n
      · cases hinner : twoSumInner l t n F₁ i (i + 1) with
        | hit a b =>
          have hinner2 : twoSumInner l t n F₂' i (i + 1) = .hit a b := by
            have hag := twoSumInner_fuel_ge l t n F₁ F₂' i (i + 1)
              (by omega : i + 1 ≤ n) (by omega : n - (i + 1) + 1 ≤ F₁)
              (by omega : n - (i + 1) + 1 ≤ F₂')
            rw [← hag]; exact hinner
          have hbin1 : twoSumOuter l t n (F₁ + 1) i = .hit a b := by
            simp only [twoSumOuter, hilt]
            rw [hinner]
            simp
          have hbin2 : twoSumOuter l t n (F₂' + 1) i = .hit a b := by
            simp only [twoSumOuter, hilt]
            rw [hinner2]
            simp
          rw [hbin1, hbin2]
        | miss =>
          have hinner2 : twoSumInner l t n F₂' i (i + 1) = .miss := by
            have hag := twoSumInner_fuel_ge l t n F₁ F₂' i (i + 1)
              (by omega : i + 1 ≤ n) (by omega : n - (i + 1) + 1 ≤ F₁)
              (by omega : n - (i + 1) + 1 ≤ F₂')
            rw [← hag]; exact hinner
          have hbin1 : twoSumOuter l t n (F₁ + 1) i =
              twoSumOuter l t n F₁ (i + 1) := by
            simp only [twoSumOuter, hilt]
            rw [hinner]
            simp
          have hbin2 : twoSumOuter l t n (F₂' + 1) i =
              twoSumOuter l t n F₂' (i + 1) := by
            simp only [twoSumOuter, hilt]
            rw [hinner2]
            simp
          rw [hbin1, hbin2]
          exact ih F₂' (i + 1) (by omega) (by omega) (by omega)
        | overflow =>
          have hinner2 : twoSumInner l t n F₂' i (i + 1) = .overflow := by
            have hag := twoSumInner_fuel_ge l t n F₁ F₂' i (i + 1)
              (by omega : i + 1 ≤ n) (by omega : n - (i + 1) + 1 ≤ F₁)
              (by omega : n - (i + 1) + 1 ≤ F₂')
            rw [← hag]; exact hinner
          have hbin1 : twoSumOuter l t n (F₁ + 1) i = .overflow := by
            simp only [twoSumOuter, hilt]
            rw [hinner]
            simp
          have hbin2 : twoSumOuter l t n (F₂' + 1) i = .overflow := by
            simp only [twoSumOuter, hilt]
            rw [hinner2]
            simp
          rw [hbin1, hbin2]
      · simp [twoSumOuter, hilt]

/-- `emit_correct` for two-sum (fuel-generalized; the dynamic-length
side condition is `l.length + 1 ≤ F`). -/
theorem evalFuncFuel_vecTwoSum (F : Nat) (l : List (BitVec 32))
    (t : BitVec 32)
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    evalFuncFuel F vecTwoSumFunc [.stdVecVal l, .i32 t] =
      vecTwoSumFwd l t := by
  have hbind : bindArgs vecTwoSumFunc.args [.stdVecVal l, .i32 t] =
      some [("s", .stdVecVal l), ("target", .i32 t)] := rfl
  have hbody : vecTwoSumFunc.body =
      (.seq (.let_ "n" (.u 64) (.stdVecLen "s"))
        (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecTwoSumOuter
              (.return_ vecTwoSumMiss))))) := rfl
  have hlenE : evalExpr (.stdVecLen "s")
      [("s", .stdVecVal l), ("target", .i32 t)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some "s" _ l (by simp [envLookup])
  have hlet_n : evalStmtFuel F (.let_ "n" (.u 64) (.stdVecLen "s"))
      [("s", .stdVecVal l), ("target", .i32 t)] =
      .ok ([("n", .u64 (BitVec.ofNat 64 l.length)),
        ("s", .stdVecVal l), ("target", .i32 t)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ hlenE
  have hlet_i : evalStmtFuel F
      (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("n", .u64 (BitVec.ofNat 64 l.length)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      .ok ([("i", .u64 (BitVec.ofNat 64 0)),
        ("n", .u64 (BitVec.ofNat 64 l.length)),
        ("s", .stdVecVal l), ("target", .i32 t)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have hlet_j : evalStmtFuel F
      (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("i", .u64 (BitVec.ofNat 64 0)),
        ("n", .u64 (BitVec.ofNat 64 l.length)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      .ok ([("j", .u64 (BitVec.ofNat 64 0)),
        ("i", .u64 (BitVec.ofNat 64 0)),
        ("n", .u64 (BitVec.ofNat 64 l.length)),
        ("s", .stdVecVal l), ("target", .i32 t)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have henv : [("j", .u64 (BitVec.ofNat 64 0)),
        ("i", .u64 (BitVec.ofNat 64 0)),
        ("n", .u64 (BitVec.ofNat 64 l.length)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      mkTwoSumEnv l l.length 0 0 t := rfl
  have hag : twoSumOuter l t l.length F 0 =
      twoSumOuter l t l.length (l.length + 1) 0 :=
    twoSumOuter_fuel_ge l t l.length F _ 0 (Nat.zero_le _) (by omega) (by omega)
  cases hbs : twoSumOuter l t l.length F 0 with
  | hit a b =>
    obtain ⟨ρ', hwhile⟩ := vecTwoSumOuter_hit l t l.length F 0 0 a b
      (Nat.le_refl _) (Nat.zero_le _) hl64 (by omega) hbs
    rw [hag] at hbs
    have hfwd : vecTwoSumFwd l t =
        .ok (.structVal "IPair" [(("a", BitVec.ofNat 32 a)), (("b", BitVec.ofNat 32 b))]) := by
      simp [vecTwoSumFwd, hbs]
    have hstmt : evalStmtFuel F vecTwoSumFunc.body
        [("s", .stdVecVal l), ("target", .i32 t)] =
        .ok (ρ', .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 a)), (("b", BitVec.ofNat 32 b))])) := by
      rw [hbody,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_n,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_i,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_j, henv,
        evalStmtFuel_seq_return F _ _ _ _ _ hwhile]
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | miss =>
    obtain ⟨ρ', hwhile, hn'⟩ := vecTwoSumOuter_miss l t l.length F 0 0
      (Nat.le_refl _) (Nat.zero_le _) hl64 (by omega) hbs
    rw [hag] at hbs
    have hfwd : vecTwoSumFwd l t =
        .ok (.structVal "IPair" [(("a", BitVec.ofNat 32 l.length)), (("b", BitVec.ofNat 32 l.length))]) := by
      simp [vecTwoSumFwd, hbs]
    have hnN : (BitVec.ofNat 64 l.length).toNat = l.length :=
      ofNat64_toNat' _ hl64
    have hnE : evalExpr (.var "n") ρ' =
        .ok (.u64 (BitVec.ofNat 64 l.length)) :=
      evalExpr_var_hit _ _ _ hn'
    have hnn : evalExpr (.i32ofU64 (.var "n")) ρ' =
        .ok (.i32 (BitVec.ofNat 32 l.length)) := by
      have h := evalExpr_i32ofU64_ok (.var "n") ρ' _ hnE
      rwa [hnN] at h
    have hpairE : evalExpr vecTwoSumMiss ρ' =
        .ok (.structVal "IPair" [(("a", BitVec.ofNat 32 l.length)), (("b", BitVec.ofNat 32 l.length))]) := by
      simp only [vecTwoSumMiss]
      exact evalExpr_pair_ok _ _ _ _ _ hnn hnn
    have hretS : evalStmtFuel F (.return_ vecTwoSumMiss) ρ' =
        .ok (ρ', .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 l.length)), (("b", BitVec.ofNat 32 l.length))])) :=
      evalStmtFuel_return F _ _ _ hpairE
    have hstmt : evalStmtFuel F vecTwoSumFunc.body
        [("s", .stdVecVal l), ("target", .i32 t)] =
        .ok (ρ', .returned (.structVal "IPair" [(("a", BitVec.ofNat 32 l.length)), (("b", BitVec.ofNat 32 l.length))])) := by
      rw [hbody,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_n,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_i,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_j, henv]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hwhile).trans hretS
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | overflow =>
    obtain hwhile := vecTwoSumOuter_overflow l t l.length F 0 0
      (Nat.le_refl _) (Nat.zero_le _) hl64 (by omega) hbs
    rw [hag] at hbs
    have hfwd : vecTwoSumFwd l t = .error .Overflow := by
      simp [vecTwoSumFwd, hbs]
    have hstmt : evalStmtFuel F vecTwoSumFunc.body
        [("s", .stdVecVal l), ("target", .i32 t)] = .error .Overflow := by
      rw [hbody,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_n,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_i,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_j, henv]
      exact evalStmtFuel_seq_err F _ _ _ _ hwhile
    simp [evalFuncFuel, hbind, hstmt, hfwd]
