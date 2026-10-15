import Circe.Emit.VecAt

/-
V1 binary search over `std::vector<int>` (sorted, half-open `[lo,hi)`.

Corpus: `tests/cpp/vec_binary_search.cpp` → `tests/cir/vec_binary_search.cir`
(141 `cir.` lines). Shape: `lo = 0`, `hi = size`, `while (lo < hi)` with
`ult` guard, safe midpoint `lo + ((hi - lo) >> 1)` via `usub` + u64 `bshr`
(no div op, no overflow debt), element read via bare `stdVecAt`
(`_M_range_check` is dead-but-propagated, same as `VecAtSum`), branch on
`slt` (elements are `i32`) / `ueq`, miss result = `len` (`find_eq` house
style, avoids small-width `i32`/`-1` casts). Sortedness is caller debt.
-/

/-- Function name (Itanium mangling of a `vec_binary_search` free function
taking `const vector<int>&` + `int`). -/
def vecBinarySearchName : String := "_Z17vec_binary_searchRKSt6vectorIiSaIiEEi"

/-- Safe midpoint `lo + ((hi - lo) >> 1)`. -/
def vecBinSearchMid : CExpr :=
  (.uadd (.var "lo") (.bshr (.usub (.var "hi") (.var "lo")) (.lit (.u64 1))))

/-- Element read at the midpoint (bare `stdVecAt`; the range
guard `ult mid (stdVecLen s)` holds by `lo ≤ mid < hi ≤ len`). -/
def vecBinSearchRead : CExpr := (.stdVecAt "s" vecBinSearchMid)

/-- Loop body: `mid` read under the fused range check (dead `.fail`,
`stdVecAtFunc` precedent), then hit / go-left / go-right. -/
def vecBinSearchBody : CStmt :=
  (.seq (.assign "mid" vecBinSearchMid)
    (.if_ (.ult vecBinSearchMid (.stdVecLen "s"))
      (.seq (.assign "x" vecBinSearchRead)
        (.if_ (.ueq (.var "x") (.var "target"))
          (.return_ (.var "mid"))
          (.if_ (.slt (.var "x") (.var "target"))
            (.assign "lo" (.uadd (.var "mid") (.lit (.u64 1))))
            (.assign "hi" (.var "mid")))))
      .fail))

/-- The search loop `while (lo < hi) body`. -/
def vecBinSearchWhile : CStmt :=
  (.while_ (.ult (.var "lo") (.var "hi")) vecBinSearchBody)

/-- Whole function: `let_`-prelude binds `lo/hi/mid/x` (`assign` needs
bound targets), loop, miss returns `len`. -/
def vecBinSearchFunc : Func :=
  ⟨vecBinarySearchName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "target", ty := .i 32, role := .owned }],
   .u 64,
   (.seq (.let_ "lo" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "hi" (.u 64) (.stdVecLen "s"))
       (.seq (.let_ "mid" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq (.let_ "x" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
           (.seq vecBinSearchWhile
             (.return_ (.stdVecLen "s")))))))⟩

/-- Loop environment (u64 indices, `i32` target/element). `mid`/`x` are
pre-bound (stale on entry, overwritten by the body) because `assign`
rejects unbound targets. Binding order matches the prelude `let_` cons
chain so the entry bridge is `rfl` (`vecAtSumFunc` precedent). -/
def mkBinSearchEnv (l : List (BitVec 32)) (lo hi : Nat) (t : BitVec 32)
    (mid : Nat) (x : BitVec 32) : Env :=
  [("x", .i32 x), ("mid", .u64 (BitVec.ofNat 64 mid)),
   ("hi", .u64 (BitVec.ofNat 64 hi)), ("lo", .u64 (BitVec.ofNat 64 lo)),
   ("s", .stdVecVal l), ("target", .i32 t)]

@[simp] theorem mkBinSearchEnv_x (l : List (BitVec 32)) (lo hi : Nat) (t : BitVec 32)
    (mid : Nat) (x : BitVec 32) :
    envLookup (mkBinSearchEnv l lo hi t mid x) "x" = some (.i32 x) := by
  simp [mkBinSearchEnv, envLookup]

@[simp] theorem mkBinSearchEnv_mid (l : List (BitVec 32)) (lo hi : Nat) (t : BitVec 32)
    (mid : Nat) (x : BitVec 32) :
    envLookup (mkBinSearchEnv l lo hi t mid x) "mid" =
      some (.u64 (BitVec.ofNat 64 mid)) := by
  simp [mkBinSearchEnv, envLookup, show ("mid" : String) ≠ "x" by decide]

@[simp] theorem mkBinSearchEnv_hi (l : List (BitVec 32)) (lo hi : Nat) (t : BitVec 32)
    (mid : Nat) (x : BitVec 32) :
    envLookup (mkBinSearchEnv l lo hi t mid x) "hi" =
      some (.u64 (BitVec.ofNat 64 hi)) := by
  simp [mkBinSearchEnv, envLookup, show ("hi" : String) ≠ "x" by decide,
    show ("hi" : String) ≠ "mid" by decide]

@[simp] theorem mkBinSearchEnv_lo (l : List (BitVec 32)) (lo hi : Nat) (t : BitVec 32)
    (mid : Nat) (x : BitVec 32) :
    envLookup (mkBinSearchEnv l lo hi t mid x) "lo" =
      some (.u64 (BitVec.ofNat 64 lo)) := by
  simp [mkBinSearchEnv, envLookup, show ("lo" : String) ≠ "x" by decide,
    show ("lo" : String) ≠ "mid" by decide,
    show ("lo" : String) ≠ "hi" by decide]

@[simp] theorem mkBinSearchEnv_s (l : List (BitVec 32)) (lo hi : Nat) (t : BitVec 32)
    (mid : Nat) (x : BitVec 32) :
    envLookup (mkBinSearchEnv l lo hi t mid x) "s" = some (.stdVecVal l) := by
  simp [mkBinSearchEnv, envLookup, show ("s" : String) ≠ "x" by decide,
    show ("s" : String) ≠ "mid" by decide,
    show ("s" : String) ≠ "hi" by decide,
    show ("s" : String) ≠ "lo" by decide]

@[simp] theorem mkBinSearchEnv_target (l : List (BitVec 32)) (lo hi : Nat) (t : BitVec 32)
    (mid : Nat) (x : BitVec 32) :
    envLookup (mkBinSearchEnv l lo hi t mid x) "target" = some (.i32 t) := by
  simp [mkBinSearchEnv, envLookup, show ("target" : String) ≠ "x" by decide,
    show ("target" : String) ≠ "mid" by decide,
    show ("target" : String) ≠ "hi" by decide,
    show ("target" : String) ≠ "lo" by decide,
    show ("target" : String) ≠ "s" by decide]

/-- `assign` updates restore the constructor shape (in-place `envUpdate`). -/
@[simp] theorem binSearchEnv_update_lo (l : List (BitVec 32)) (lo hi lo' : Nat)
    (t : BitVec 32) (mid : Nat) (x : BitVec 32) :
    envUpdate (mkBinSearchEnv l lo hi t mid x) "lo"
        (.u64 (BitVec.ofNat 64 lo')) =
      some (mkBinSearchEnv l lo' hi t mid x) := by
  simp [mkBinSearchEnv, envUpdate, show ("lo" : String) ≠ "x" by decide,
    show ("lo" : String) ≠ "mid" by decide,
    show ("lo" : String) ≠ "hi" by decide]

@[simp] theorem binSearchEnv_update_hi (l : List (BitVec 32)) (lo hi hi' : Nat)
    (t : BitVec 32) (mid : Nat) (x : BitVec 32) :
    envUpdate (mkBinSearchEnv l lo hi t mid x) "hi"
        (.u64 (BitVec.ofNat 64 hi')) =
      some (mkBinSearchEnv l lo hi' t mid x) := by
  simp [mkBinSearchEnv, envUpdate, show ("hi" : String) ≠ "x" by decide,
    show ("hi" : String) ≠ "mid" by decide]

@[simp] theorem binSearchEnv_update_mid (l : List (BitVec 32)) (lo hi mid' : Nat)
    (t : BitVec 32) (mid : Nat) (x : BitVec 32) :
    envUpdate (mkBinSearchEnv l lo hi t mid x) "mid"
        (.u64 (BitVec.ofNat 64 mid')) =
      some (mkBinSearchEnv l lo hi t mid' x) := by
  simp [mkBinSearchEnv, envUpdate, show ("mid" : String) ≠ "x" by decide]

@[simp] theorem binSearchEnv_update_x (l : List (BitVec 32)) (lo hi : Nat)
    (t : BitVec 32) (mid : Nat) (x x' : BitVec 32) :
    envUpdate (mkBinSearchEnv l lo hi t mid x) "x" (.i32 x') =
      some (mkBinSearchEnv l lo hi t mid x') := by
  simp [mkBinSearchEnv, envUpdate]

/-- `u64` literal round-trip under a vector-length bound (local copy of the
`ofNat64_toNat` shape, avoiding a Hoare import in `Emit`). -/
theorem ofNat64_toNat' (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-- The midpoint evaluates to `lo + (hi - lo) / 2` as a `u64` word. -/
theorem vecBinSearchMid_toNat (l : List (BitVec 32)) (lo hi : Nat)
    (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length) (hlehi : lo ≤ hi) :
    evalExpr vecBinSearchMid (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2))) := by
  have hlo64 : (BitVec.ofNat 64 lo).toNat = lo :=
    ofNat64_toNat' lo (Nat.lt_of_le_of_lt hle hlen)
  have hhi64 : (BitVec.ofNat 64 hi).toNat = hi :=
    ofNat64_toNat' hi (Nat.lt_of_le_of_lt hhi hlen)
  have hlo : evalExpr (.var "lo") (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 (BitVec.ofNat 64 lo)) :=
    evalExpr_var_hit _ _ _ (mkBinSearchEnv_lo l lo hi t mid0 x0)
  have hhi : evalExpr (.var "hi") (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 (BitVec.ofNat 64 hi)) :=
    evalExpr_var_hit _ _ _ (mkBinSearchEnv_hi l lo hi t mid0 x0)
  have hsub := evalExpr_usub_u64u64 _ _ _ _ _ hhi hlo
  have hone : evalExpr (.lit (.u64 (1 : BitVec 64))) (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 1) := evalExpr_lit _ _
  have hshr := evalExpr_bshr_u64 _ _ _ _ _ hsub hone
  have hsh : checkedShiftU64 (BitVec.ofNat 64 hi - BitVec.ofNat 64 lo) 1 (· >>> ·) =
      .ok ((BitVec.ofNat 64 hi - BitVec.ofNat 64 lo) >>> 1) :=
    checkedShiftU64_ok _ _ _ (by decide)
  rw [hsh] at hshr
  have hadd := evalExpr_uadd_u64 _ _ _ _ _ hlo hshr
  have hmidN : (BitVec.ofNat 64 lo +
      ((BitVec.ofNat 64 hi - BitVec.ofNat 64 lo) >>> 1)).toNat
      = lo + (hi - lo) / 2 := by
    have hshr1 : ∀ d : Nat, (d >>> 1) = d / 2 := fun d => rfl
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      hlo64, hhi64, hshr1]
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [h64]
    omega
  have hmidBV : BitVec.ofNat 64 lo +
      ((BitVec.ofNat 64 hi - BitVec.ofNat 64 lo) >>> 1) =
      BitVec.ofNat 64 (lo + (hi - lo) / 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [hmidN, ofNat64_toNat']
    have : lo + (hi - lo) / 2 ≤ l.length := by omega
    exact Nat.lt_of_le_of_lt this hlen
  simp only [vecBinSearchMid] at hadd ⊢
  rw [hmidBV] at hadd
  exact hadd

/-- Midpoint read delivers the element word. -/
theorem vecBinSearchRead_hit (l : List (BitVec 32)) (lo hi : Nat)
    (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32) (i : BitVec 64) (x : BitVec 32)
    (hmid : evalExpr vecBinSearchMid (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.u64 i))
    (hget : l[i.toNat]? = some x) :
    evalExpr vecBinSearchRead (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.i32 x) :=
  evalExpr_stdVecAt_some "s" _ _ _ _ _ (mkBinSearchEnv_s l lo hi t mid0 x0) hmid hget

/-- Search outcome: hit index or miss (miss forwards to `l.length`). -/
inductive BinResult where
  | hit : Nat → BinResult
  | miss : BinResult
  deriving DecidableEq, Repr

/-- Reference search: fuel-bounded, returns index or `l.length` on miss.
The `none` arm is unreachable (`mid < l.length` always holds in-loop);
it forwards to `.miss` and proofs close it by contradiction, keeping the
match non-dependent so `simp`/`rw` rewrite the discriminee freely. -/
def binSearch (l : List (BitVec 32)) (t : BitVec 32) : Nat → Nat → Nat → BinResult
  | 0, _, _ => .miss
  | fuel + 1, lo, hi =>
    if _ : lo < hi then
      let mid := lo + (hi - lo) / 2
      if _ : mid < l.length then
        match l[mid]? with
        | some x =>
          if x == t then .hit mid
          else if x.slt t then binSearch l t fuel (mid + 1) hi
          else binSearch l t fuel lo mid
        | none => .miss
      else .miss
    else .miss

/-- The `none` arm is unreachable: `mid < l.length` contradicts it. -/
theorem binSearch_getElem_ne_none (l : List (BitVec 32)) (mid : Nat)
    (hmem : mid < l.length) (h : l[mid]? = none) : False := by
  have hg : l[mid]? = some l[mid] := List.getElem?_eq_getElem hmem
  rw [hg] at h
  simp at h

/-- Forward model over the entry environment. -/
def vecBinarySearchFwd (l : List (BitVec 32)) (t : BitVec 32) : Result Value :=
  match binSearch l t (l.length + 1) 0 l.length with
  | .hit m => .ok (.u64 (BitVec.ofNat 64 m))
  | .miss => .ok (.u64 (BitVec.ofNat 64 l.length))

/-- `ueq` on two `i32`-valued expressions (no general lemma exists —
only literal shapes — so the binary-search branch proves this local one;
mirrors `evalExpr_ult_u64`). -/
theorem evalExpr_ueq_i32 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 32)
    (h₁ : evalExpr e₁ ρ = .ok (.i32 x))
    (h₂ : evalExpr e₂ ρ = .ok (.i32 y)) :
    evalExpr (.ueq e₁ e₂) ρ = .ok (.b (x == y)) := by
  simp [evalExpr, h₁, h₂]

/-- `seq` propagates `returned` (the second component never runs); local
mirror of `evalStmtFuel_seq_fallthrough`, needed for the hit path. -/
theorem evalStmtFuel_seq_return (f : Nat) (a b : CStmt)
    (ρ ρ' : Env) (v : Value)
    (h : evalStmtFuel f a ρ = .ok (ρ', .returned v)) :
    evalStmtFuel f (.seq a b) ρ = .ok (ρ', .returned v) := by
  cases f with
  | zero =>
    simp only [evalStmtFuel, evalStmtZero] at h ⊢
    simp only [evalStmtWith, h]
  | succ g =>
    simp only [evalStmtFuel] at h ⊢
    simp only [evalStmtWith, h]

/-- Loop-guard evaluation: `ult lo hi` is `decide (lo < hi)`. -/
theorem vecBinSearchGuard_eval (l : List (BitVec 32)) (lo hi : Nat)
    (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length) :
    evalExpr (.ult (.var "lo") (.var "hi"))
        (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.b (decide (lo < hi))) := by
  have hloE := evalExpr_var_hit _ _ _ (mkBinSearchEnv_lo l lo hi t mid0 x0)
  have hhiE := evalExpr_var_hit _ _ _ (mkBinSearchEnv_hi l lo hi t mid0 x0)
  have h := evalExpr_ult_u64 _ _ _ _ _ hloE hhiE
  have huv : (BitVec.ofNat 64 lo).ult (BitVec.ofNat 64 hi) =
      decide (lo < hi) := by
    rw [BitVec.ult_eq_decide,
      ofNat64_toNat' lo (Nat.lt_of_le_of_lt hle hlen),
      ofNat64_toNat' hi (Nat.lt_of_le_of_lt hhi hlen)]
  rwa [huv] at h

/-- Fused range-check evaluation: `ult mid len` is true in-loop. -/
theorem vecBinSearchRange_eval (l : List (BitVec 32)) (lo hi : Nat)
    (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32) (midv : Nat)
    (hlen : l.length < 2 ^ 64)
    (hmidv : midv < l.length)
    (hmid : evalExpr vecBinSearchMid (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 (BitVec.ofNat 64 midv))) :
    evalExpr (.ult vecBinSearchMid (.stdVecLen "s"))
        (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.b true) := by
  have hlenE := evalExpr_stdVecLen_some "s" _ _
    (mkBinSearchEnv_s l lo hi t mid0 x0)
  have h := evalExpr_ult_u64 _ _ _ _ _ hmid hlenE
  have huv : (BitVec.ofNat 64 midv).ult (BitVec.ofNat 64 l.length) = true := by
    rw [BitVec.ult_eq_decide,
      ofNat64_toNat' midv (Nat.lt_trans hmidv hlen),
      ofNat64_toNat' l.length hlen]
    exact decide_eq_true hmidv
  rwa [huv] at h

/-- Hit-branch condition: `ueq x target` is `(x == t)`. -/
theorem vecBinSearchUeq_eval (l : List (BitVec 32)) (lo hi : Nat)
    (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32) (xv : BitVec 32)
    (hxv : evalExpr (.var "x") (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.i32 xv)) :
    evalExpr (.ueq (.var "x") (.var "target"))
        (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.b (xv == t)) := by
  have ht := evalExpr_var_hit _ _ _ (mkBinSearchEnv_target l lo hi t mid0 x0)
  exact evalExpr_ueq_i32 _ _ _ _ _ hxv ht

/-- Go-left condition: `slt x target` is `x.slt t`. -/
theorem vecBinSearchSlt_eval (l : List (BitVec 32)) (lo hi : Nat)
    (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32) (xv : BitVec 32)
    (hxv : evalExpr (.var "x") (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.i32 xv)) :
    evalExpr (.slt (.var "x") (.var "target"))
        (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.b (xv.slt t)) := by
  have ht := evalExpr_var_hit _ _ _ (mkBinSearchEnv_target l lo hi t mid0 x0)
  exact evalExpr_slt_i32 _ _ _ _ _ hxv ht

/-! ## Body steps (fuel-generalized; the body is loop-free) -/

/-- Hit step: guard and range hold, `x == t`: returns `mid`. -/
theorem vecBinSearchBody_hit (F : Nat) (l : List (BitVec 32))
    (lo hi : Nat) (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32)
    (xv : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length) (hlehi : lo ≤ hi)
    (hlt : lo < hi)
    (hget : l[lo + (hi - lo) / 2]? = some xv)
    (heq : (xv == t) = true) :
    evalStmtFuel F vecBinSearchBody (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv,
        .returned (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2)))) := by
  have hmidv_lt : lo + (hi - lo) / 2 < l.length := by omega
  have hmidE : evalExpr vecBinSearchMid (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2))) :=
    vecBinSearchMid_toNat l lo hi t mid0 x0 hlen hle hhi hlehi
  have hassign_mid : evalStmtFuel F (.assign "mid" vecBinSearchMid)
      (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0, .fellThrough) :=
    evalStmtFuel_assign F _ _ _ _ _ hmidE
      (binSearchEnv_update_mid l lo hi _ t mid0 x0)
  have hmidE₁ : evalExpr vecBinSearchMid
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) =
      .ok (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2))) :=
    vecBinSearchMid_toNat l lo hi t _ x0 hlen hle hhi hlehi
  have hrange := vecBinSearchRange_eval l lo hi t _ x0 _ hlen hmidv_lt hmidE₁
  have hmidN : (BitVec.ofNat 64 (lo + (hi - lo) / 2)).toNat =
      lo + (hi - lo) / 2 :=
    ofNat64_toNat' _ (Nat.lt_trans hmidv_lt hlen)
  have hget' : l[(BitVec.ofNat 64 (lo + (hi - lo) / 2)).toNat]? = some xv := by
    rw [hmidN]; exact hget
  have hread : evalExpr vecBinSearchRead
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) = .ok (.i32 xv) :=
    vecBinSearchRead_hit l lo hi t _ x0 _ xv hmidE₁ hget'
  have hassign_x : evalStmtFuel F (.assign "x" vecBinSearchRead)
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv, .fellThrough) :=
    evalStmtFuel_assign F _ _ _ _ _ hread
      (binSearchEnv_update_x l lo hi t _ x0 xv)
  have hxv : evalExpr (.var "x")
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv) = .ok (.i32 xv) :=
    evalExpr_var_hit _ _ _ (mkBinSearchEnv_x l lo hi t _ xv)
  have hueq := vecBinSearchUeq_eval l lo hi t _ _ xv hxv
  rw [heq] at hueq
  have hret : evalStmtFuel F (.return_ (.var "mid"))
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv,
        .returned (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2)))) :=
    evalStmtFuel_return F _ _ _
      (evalExpr_var_hit _ _ _ (mkBinSearchEnv_mid l lo hi t _ xv))
  simp only [vecBinSearchBody]
  rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hassign_mid,
    evalStmtFuel_if_true F _ _ _ _ hrange,
    evalStmtFuel_seq_fallthrough F _ _ _ _ hassign_x,
    evalStmtFuel_if_true F _ _ _ _ hueq]
  exact hret

/-- Go-left step: `x != t`, `x < t`: `lo := mid + 1`, falls through. -/
theorem vecBinSearchBody_left (F : Nat) (l : List (BitVec 32))
    (lo hi : Nat) (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32)
    (xv : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length) (hlehi : lo ≤ hi)
    (hlt : lo < hi)
    (hget : l[lo + (hi - lo) / 2]? = some xv)
    (hne : (xv == t) = false) (hslt : (xv.slt t) = true) :
    evalStmtFuel F vecBinSearchBody (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (mkBinSearchEnv l (lo + (hi - lo) / 2 + 1) hi t
        (lo + (hi - lo) / 2) xv, .fellThrough) := by
  have hmidv_lt : lo + (hi - lo) / 2 < l.length := by omega
  have hmidE : evalExpr vecBinSearchMid (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2))) :=
    vecBinSearchMid_toNat l lo hi t mid0 x0 hlen hle hhi hlehi
  have hassign_mid : evalStmtFuel F (.assign "mid" vecBinSearchMid)
      (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0, .fellThrough) :=
    evalStmtFuel_assign F _ _ _ _ _ hmidE
      (binSearchEnv_update_mid l lo hi _ t mid0 x0)
  have hmidE₁ : evalExpr vecBinSearchMid
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) =
      .ok (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2))) :=
    vecBinSearchMid_toNat l lo hi t _ x0 hlen hle hhi hlehi
  have hrange := vecBinSearchRange_eval l lo hi t _ x0 _ hlen hmidv_lt hmidE₁
  have hmidN : (BitVec.ofNat 64 (lo + (hi - lo) / 2)).toNat =
      lo + (hi - lo) / 2 :=
    ofNat64_toNat' _ (Nat.lt_trans hmidv_lt hlen)
  have hget' : l[(BitVec.ofNat 64 (lo + (hi - lo) / 2)).toNat]? = some xv := by
    rw [hmidN]; exact hget
  have hread : evalExpr vecBinSearchRead
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) = .ok (.i32 xv) :=
    vecBinSearchRead_hit l lo hi t _ x0 _ xv hmidE₁ hget'
  have hassign_x : evalStmtFuel F (.assign "x" vecBinSearchRead)
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv, .fellThrough) :=
    evalStmtFuel_assign F _ _ _ _ _ hread
      (binSearchEnv_update_x l lo hi t _ x0 xv)
  have hxv : evalExpr (.var "x")
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv) = .ok (.i32 xv) :=
    evalExpr_var_hit _ _ _ (mkBinSearchEnv_x l lo hi t _ xv)
  have hueq := vecBinSearchUeq_eval l lo hi t _ _ xv hxv
  rw [hne] at hueq
  have hsltE := vecBinSearchSlt_eval l lo hi t _ _ xv hxv
  rw [hslt] at hsltE
  have hmid1 : BitVec.ofNat 64 (lo + (hi - lo) / 2) + 1 =
      BitVec.ofNat 64 (lo + (hi - lo) / 2 + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add,
      ofNat64_toNat' _ (Nat.lt_trans hmidv_lt hlen)]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1, ofNat64_toNat' _ (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hmidvE := evalExpr_var_hit _ _ _
    (mkBinSearchEnv_mid l lo hi t (lo + (hi - lo) / 2) xv)
  have honeE : evalExpr (.lit (.u64 (1 : BitVec 64)))
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv) = .ok (.u64 1) :=
    evalExpr_lit _ _
  have hadd := evalExpr_uadd_u64 _ _ _ _ _ hmidvE honeE
  rw [hmid1] at hadd
  have hassign_lo := evalStmtFuel_assign F _ _ _ _ _ hadd
    (binSearchEnv_update_lo l lo hi _ t _ xv)
  simp only [vecBinSearchBody]
  rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hassign_mid,
    evalStmtFuel_if_true F _ _ _ _ hrange,
    evalStmtFuel_seq_fallthrough F _ _ _ _ hassign_x,
    evalStmtFuel_if_false F _ _ _ _ hueq,
    evalStmtFuel_if_true F _ _ _ _ hsltE]
  exact hassign_lo

/-- Go-right step: `x != t`, `¬ x < t`: `hi := mid`, falls through. -/
theorem vecBinSearchBody_right (F : Nat) (l : List (BitVec 32))
    (lo hi : Nat) (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32)
    (xv : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length) (hlehi : lo ≤ hi)
    (hlt : lo < hi)
    (hget : l[lo + (hi - lo) / 2]? = some xv)
    (hne : (xv == t) = false) (hslt : (xv.slt t) = false) :
    evalStmtFuel F vecBinSearchBody (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (mkBinSearchEnv l lo (lo + (hi - lo) / 2) t
        (lo + (hi - lo) / 2) xv, .fellThrough) := by
  have hmidv_lt : lo + (hi - lo) / 2 < l.length := by omega
  have hmidE : evalExpr vecBinSearchMid (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2))) :=
    vecBinSearchMid_toNat l lo hi t mid0 x0 hlen hle hhi hlehi
  have hassign_mid : evalStmtFuel F (.assign "mid" vecBinSearchMid)
      (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0, .fellThrough) :=
    evalStmtFuel_assign F _ _ _ _ _ hmidE
      (binSearchEnv_update_mid l lo hi _ t mid0 x0)
  have hmidE₁ : evalExpr vecBinSearchMid
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) =
      .ok (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2))) :=
    vecBinSearchMid_toNat l lo hi t _ x0 hlen hle hhi hlehi
  have hrange := vecBinSearchRange_eval l lo hi t _ x0 _ hlen hmidv_lt hmidE₁
  have hmidN : (BitVec.ofNat 64 (lo + (hi - lo) / 2)).toNat =
      lo + (hi - lo) / 2 :=
    ofNat64_toNat' _ (Nat.lt_trans hmidv_lt hlen)
  have hget' : l[(BitVec.ofNat 64 (lo + (hi - lo) / 2)).toNat]? = some xv := by
    rw [hmidN]; exact hget
  have hread : evalExpr vecBinSearchRead
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) = .ok (.i32 xv) :=
    vecBinSearchRead_hit l lo hi t _ x0 _ xv hmidE₁ hget'
  have hassign_x : evalStmtFuel F (.assign "x" vecBinSearchRead)
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) x0) =
      .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv, .fellThrough) :=
    evalStmtFuel_assign F _ _ _ _ _ hread
      (binSearchEnv_update_x l lo hi t _ x0 xv)
  have hxv : evalExpr (.var "x")
      (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv) = .ok (.i32 xv) :=
    evalExpr_var_hit _ _ _ (mkBinSearchEnv_x l lo hi t _ xv)
  have hueq := vecBinSearchUeq_eval l lo hi t _ _ xv hxv
  rw [hne] at hueq
  have hsltE := vecBinSearchSlt_eval l lo hi t _ _ xv hxv
  rw [hslt] at hsltE
  have hmidvE := evalExpr_var_hit _ _ _
    (mkBinSearchEnv_mid l lo hi t (lo + (hi - lo) / 2) xv)
  have hassign_hi := evalStmtFuel_assign F _ _ _ _ _ hmidvE
    (binSearchEnv_update_hi l lo hi _ t _ xv)
  simp only [vecBinSearchBody]
  rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hassign_mid,
    evalStmtFuel_if_true F _ _ _ _ hrange,
    evalStmtFuel_seq_fallthrough F _ _ _ _ hassign_x,
    evalStmtFuel_if_false F _ _ _ _ hueq,
    evalStmtFuel_if_false F _ _ _ _ hsltE]
  exact hassign_hi

/-! ## While correctness (fuel-generalized; `hi - lo` is the measure) -/

/-- Loop-guard `false` exits cleanly at successor fuel. -/
theorem vecBinSearchWhile_exit (F : Nat) (l : List (BitVec 32))
    (lo hi : Nat) (t : BitVec 32) (mid0 : Nat) (x0 : BitVec 32)
    (hlen : l.length < 2 ^ 64)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length)
    (hge : hi ≤ lo) :
    evalStmtFuel (F + 1) vecBinSearchWhile
        (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (mkBinSearchEnv l lo hi t mid0 x0, .fellThrough) := by
  have hcond : evalExpr (.ult (.var "lo") (.var "hi"))
      (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.b false) := by
    have h := vecBinSearchGuard_eval l lo hi t mid0 x0 hlen hle hhi
    have hfalse : decide (lo < hi) = false :=
      decide_eq_false (Nat.not_lt.mpr hge)
    rwa [hfalse] at h
  simp [vecBinSearchWhile, evalStmtFuel, evalStmtSuccHandler,
    evalStmtWith, hcond]

/-- Hit soundness: `binSearch` hit ⟹ the loop returns that index. -/
theorem vecBinSearchWhile_hit (l : List (BitVec 32)) (t : BitVec 32)
    (F lo hi : Nat) (mid0 : Nat) (x0 : BitVec 32) (m : Nat)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length) (hlehi : lo ≤ hi)
    (hl64 : l.length < 2 ^ 64)
    (hF : hi - lo + 1 ≤ F)
    (hhit : binSearch l t F lo hi = .hit m) :
    ∃ ρ', evalStmtFuel F vecBinSearchWhile (mkBinSearchEnv l lo hi t mid0 x0) =
      .ok (ρ', .returned (.u64 (BitVec.ofNat 64 m))) := by
  induction F generalizing lo hi mid0 x0 m with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hlt : lo < hi
    · have hmem : lo + (hi - lo) / 2 < l.length := by omega
      cases hget : l[lo + (hi - lo) / 2]? with
      | none => exact (binSearch_getElem_ne_none l _ hmem hget).elim
      | some xv =>
        have hcond : evalExpr (.ult (.var "lo") (.var "hi"))
            (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.b true) := by
          have h := vecBinSearchGuard_eval l lo hi t mid0 x0 hl64 hle hhi
          rwa [decide_eq_true hlt] at h
        by_cases heq : (xv == t) = true
        · have hbin : binSearch l t (F + 1) lo hi =
              .hit (lo + (hi - lo) / 2) := by
            simp only [binSearch, hlt, hmem]
            rw [hget]
            simp [heq]
          rw [hbin] at hhit
          have hm : lo + (hi - lo) / 2 = m := by injection hhit
          subst hm
          have hbody := vecBinSearchBody_hit F l lo hi t mid0 x0 xv
            hl64 hle hhi hlehi hlt hget heq
          have hstep : evalStmtFuel (F + 1) vecBinSearchWhile
              (mkBinSearchEnv l lo hi t mid0 x0) =
              .ok (mkBinSearchEnv l lo hi t (lo + (hi - lo) / 2) xv,
                .returned (.u64 (BitVec.ofNat 64 (lo + (hi - lo) / 2)))) := by
            simp [vecBinSearchWhile, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hbody]
          exact ⟨_, hstep⟩
        · have hne : (xv == t) = false := Bool.eq_false_of_ne_true heq
          by_cases hslt : (xv.slt t) = true
          · have hbin : binSearch l t (F + 1) lo hi =
                binSearch l t F (lo + (hi - lo) / 2 + 1) hi := by
              simp only [binSearch, hlt, hmem]
              rw [hget]
              simp [hne, hslt]
            rw [hbin] at hhit
            have hbody := vecBinSearchBody_left F l lo hi t mid0 x0 xv
              hl64 hle hhi hlehi hlt hget hne hslt
            have hstep : evalStmtFuel (F + 1) vecBinSearchWhile
                (mkBinSearchEnv l lo hi t mid0 x0) =
                evalStmtFuel F vecBinSearchWhile
                  (mkBinSearchEnv l (lo + (hi - lo) / 2 + 1) hi t
                    (lo + (hi - lo) / 2) xv) := by
              simp [vecBinSearchWhile, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcond, hbody]
            rw [hstep]
            exact ih _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) hhit
          · have hnlt : (xv.slt t) = false := Bool.eq_false_of_ne_true hslt
            have hbin : binSearch l t (F + 1) lo hi =
                binSearch l t F lo (lo + (hi - lo) / 2) := by
              simp only [binSearch, hlt, hmem]
              rw [hget]
              simp [hne, hnlt]
            rw [hbin] at hhit
            have hbody := vecBinSearchBody_right F l lo hi t mid0 x0 xv
              hl64 hle hhi hlehi hlt hget hne hnlt
            have hstep : evalStmtFuel (F + 1) vecBinSearchWhile
                (mkBinSearchEnv l lo hi t mid0 x0) =
                evalStmtFuel F vecBinSearchWhile
                  (mkBinSearchEnv l lo (lo + (hi - lo) / 2) t
                    (lo + (hi - lo) / 2) xv) := by
              simp [vecBinSearchWhile, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcond, hbody]
            rw [hstep]
            exact ih _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) hhit
    · have hmiss : binSearch l t (F + 1) lo hi = .miss := by
        simp [binSearch, hlt]
      rw [hmiss] at hhit
      cases hhit

/-- Miss soundness: `binSearch` miss ⟹ the loop falls through with `s`
intact (the trailing `return len` reads it). -/
theorem vecBinSearchWhile_miss (l : List (BitVec 32)) (t : BitVec 32)
    (F lo hi : Nat) (mid0 : Nat) (x0 : BitVec 32)
    (hle : lo ≤ l.length) (hhi : hi ≤ l.length) (hlehi : lo ≤ hi)
    (hl64 : l.length < 2 ^ 64)
    (hF : hi - lo + 1 ≤ F)
    (hmiss : binSearch l t F lo hi = .miss) :
    ∃ ρ', evalStmtFuel F vecBinSearchWhile (mkBinSearchEnv l lo hi t mid0 x0) =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "s" = some (.stdVecVal l) := by
  induction F generalizing lo hi mid0 x0 with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hlt : lo < hi
    · have hmem : lo + (hi - lo) / 2 < l.length := by omega
      cases hget : l[lo + (hi - lo) / 2]? with
      | none => exact (binSearch_getElem_ne_none l _ hmem hget).elim
      | some xv =>
        have hcond : evalExpr (.ult (.var "lo") (.var "hi"))
            (mkBinSearchEnv l lo hi t mid0 x0) = .ok (.b true) := by
          have h := vecBinSearchGuard_eval l lo hi t mid0 x0 hl64 hle hhi
          rwa [decide_eq_true hlt] at h
        by_cases heq : (xv == t) = true
        · have hbin : binSearch l t (F + 1) lo hi =
              .hit (lo + (hi - lo) / 2) := by
            simp only [binSearch, hlt, hmem]
            rw [hget]
            simp [heq]
          rw [hbin] at hmiss
          cases hmiss
        · have hne : (xv == t) = false := Bool.eq_false_of_ne_true heq
          by_cases hslt : (xv.slt t) = true
          · have hbin : binSearch l t (F + 1) lo hi =
                binSearch l t F (lo + (hi - lo) / 2 + 1) hi := by
              simp only [binSearch, hlt, hmem]
              rw [hget]
              simp [hne, hslt]
            rw [hbin] at hmiss
            have hbody := vecBinSearchBody_left F l lo hi t mid0 x0 xv
              hl64 hle hhi hlehi hlt hget hne hslt
            have hstep : evalStmtFuel (F + 1) vecBinSearchWhile
                (mkBinSearchEnv l lo hi t mid0 x0) =
                evalStmtFuel F vecBinSearchWhile
                  (mkBinSearchEnv l (lo + (hi - lo) / 2 + 1) hi t
                    (lo + (hi - lo) / 2) xv) := by
              simp [vecBinSearchWhile, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcond, hbody]
            rw [hstep]
            exact ih _ _ _ _ (by omega) (by omega) (by omega) (by omega) hmiss
          · have hnlt : (xv.slt t) = false := Bool.eq_false_of_ne_true hslt
            have hbin : binSearch l t (F + 1) lo hi =
                binSearch l t F lo (lo + (hi - lo) / 2) := by
              simp only [binSearch, hlt, hmem]
              rw [hget]
              simp [hne, hnlt]
            rw [hbin] at hmiss
            have hbody := vecBinSearchBody_right F l lo hi t mid0 x0 xv
              hl64 hle hhi hlehi hlt hget hne hnlt
            have hstep : evalStmtFuel (F + 1) vecBinSearchWhile
                (mkBinSearchEnv l lo hi t mid0 x0) =
                evalStmtFuel F vecBinSearchWhile
                  (mkBinSearchEnv l lo (lo + (hi - lo) / 2) t
                    (lo + (hi - lo) / 2) xv) := by
              simp [vecBinSearchWhile, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcond, hbody]
            rw [hstep]
            exact ih _ _ _ _ (by omega) (by omega) (by omega) (by omega) hmiss
    · have hgeo : lo = hi := by omega
      subst hgeo
      have hexit := vecBinSearchWhile_exit F l lo lo t mid0 x0
        hl64 hle hhi (Nat.le_refl _)
      exact ⟨_, hexit, mkBinSearchEnv_s l lo lo t mid0 x0⟩

/-! ## Fuel agreement + `emit_correct` -/

/-- `binSearch` agrees on any two sufficient fuels (the forward model
fixes `l.length + 1`; the evaluator runs at any `F ≥ l.length + 1`). -/
theorem binSearch_fuel_ge (l : List (BitVec 32)) (t : BitVec 32) (F₁ : Nat) :
    ∀ (F₂ lo hi : Nat),
    lo ≤ l.length → hi ≤ l.length → lo ≤ hi →
    hi - lo + 1 ≤ F₁ → hi - lo + 1 ≤ F₂ →
    binSearch l t F₁ lo hi = binSearch l t F₂ lo hi := by
  induction F₁ with
  | zero =>
    intro F₂ lo hi _ _ hlehi h₁ _
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F₁ ih =>
    intro F₂ lo hi hle hhi hlehi h₁ h₂
    cases F₂ with
    | zero =>
      have hfalse : False := by omega
      exact hfalse.elim
    | succ F₂' =>
      by_cases hlt : lo < hi
      · have hmem : lo + (hi - lo) / 2 < l.length := by omega
        cases hget : l[lo + (hi - lo) / 2]? with
        | none =>
          simp only [binSearch, hlt, hmem]
          rw [hget]
        | some xv =>
          by_cases heq : (xv == t) = true
          · simp only [binSearch, hlt, hmem]
            rw [hget]
            simp [heq]
          · have hne : (xv == t) = false := Bool.eq_false_of_ne_true heq
            by_cases hslt : (xv.slt t) = true
            · simp only [binSearch, hlt, hmem]
              rw [hget]
              simp [hne, hslt]
              exact ih F₂' _ _ (by omega) (by omega) (by omega)
                (by omega) (by omega)
            · have hnlt : (xv.slt t) = false :=
                Bool.eq_false_of_ne_true hslt
              simp only [binSearch, hlt, hmem]
              rw [hget]
              simp [hne, hnlt]
              exact ih F₂' _ _ (by omega) (by omega) (by omega)
                (by omega) (by omega)
      · simp [binSearch, hlt]

/-- `emit_correct` for binary search (fuel-generalized; the slice's
dynamic-length side condition is `l.length + 1 ≤ F`). -/
theorem evalFuncFuel_vecBinarySearch (F : Nat) (l : List (BitVec 32))
    (t : BitVec 32)
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    evalFuncFuel F vecBinSearchFunc [.stdVecVal l, .i32 t] =
      vecBinarySearchFwd l t := by
  have hbind : bindArgs vecBinSearchFunc.args [.stdVecVal l, .i32 t] =
      some [("s", .stdVecVal l), ("target", .i32 t)] := rfl
  have hbody : vecBinSearchFunc.body =
      (.seq (.let_ "lo" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "hi" (.u 64) (.stdVecLen "s"))
          (.seq (.let_ "mid" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq (.let_ "x" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
              (.seq vecBinSearchWhile
                (.return_ (.stdVecLen "s"))))))) := rfl
  have hlet_lo : evalStmtFuel F
      (.let_ "lo" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("s", .stdVecVal l), ("target", .i32 t)] =
      .ok ([("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have hlenE₁ : evalExpr (.stdVecLen "s")
      [("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some "s" _ l
      (by simp [envLookup, show ("s" : String) ≠ "lo" by decide])
  have hlet_hi : evalStmtFuel F (.let_ "hi" (.u 64) (.stdVecLen "s"))
      [("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      .ok ([("hi", .u64 (BitVec.ofNat 64 l.length)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ hlenE₁
  have hlet_mid : evalStmtFuel F
      (.let_ "mid" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("hi", .u64 (BitVec.ofNat 64 l.length)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      .ok ([("mid", .u64 (BitVec.ofNat 64 0)),
        ("hi", .u64 (BitVec.ofNat 64 l.length)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have hlet_x : evalStmtFuel F
      (.let_ "x" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      [("mid", .u64 (BitVec.ofNat 64 0)),
        ("hi", .u64 (BitVec.ofNat 64 l.length)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      .ok ([("x", .i32 (BitVec.ofNat 32 0)),
        ("mid", .u64 (BitVec.ofNat 64 0)),
        ("hi", .u64 (BitVec.ofNat 64 l.length)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have henv : [("x", .i32 (BitVec.ofNat 32 0)),
        ("mid", .u64 (BitVec.ofNat 64 0)),
        ("hi", .u64 (BitVec.ofNat 64 l.length)),
        ("lo", .u64 (BitVec.ofNat 64 0)),
        ("s", .stdVecVal l), ("target", .i32 t)] =
      mkBinSearchEnv l 0 l.length t 0 (BitVec.ofNat 32 0) := rfl
  have hag : binSearch l t F 0 l.length =
      binSearch l t (l.length + 1) 0 l.length :=
    binSearch_fuel_ge l t F _ 0 l.length (Nat.zero_le _) (Nat.le_refl _)
      (Nat.zero_le _) (by omega) (by omega)
  cases hbs : binSearch l t F 0 l.length with
  | hit m =>
    obtain ⟨ρ', hwhile⟩ := vecBinSearchWhile_hit l t F 0 l.length 0
      (BitVec.ofNat 32 0) m (Nat.zero_le _) (Nat.le_refl _) (Nat.zero_le _)
      hl64 (by omega) hbs
    rw [hag] at hbs
    have hfwd : vecBinarySearchFwd l t = .ok (.u64 (BitVec.ofNat 64 m)) := by
      simp [vecBinarySearchFwd, hbs]
    have hstmt : evalStmtFuel F vecBinSearchFunc.body
        [("s", .stdVecVal l), ("target", .i32 t)] =
        .ok (ρ', .returned (.u64 (BitVec.ofNat 64 m))) := by
      rw [hbody,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_lo,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_hi,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_mid,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_x, henv,
        evalStmtFuel_seq_return F _ _ _ _ _ hwhile]
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | miss =>
    obtain ⟨ρ', hwhile, hs'⟩ := vecBinSearchWhile_miss l t F 0 l.length 0
      (BitVec.ofNat 32 0) (Nat.zero_le _) (Nat.le_refl _) (Nat.zero_le _)
      hl64 (by omega) hbs
    rw [hag] at hbs
    have hfwd : vecBinarySearchFwd l t =
        .ok (.u64 (BitVec.ofNat 64 l.length)) := by
      simp [vecBinarySearchFwd, hbs]
    have hret : evalExpr (.stdVecLen "s") ρ' =
        .ok (.u64 (BitVec.ofNat 64 l.length)) :=
      evalExpr_stdVecLen_some "s" _ _ hs'
    have hretS : evalStmtFuel F (.return_ (.stdVecLen "s")) ρ' =
        .ok (ρ', .returned (.u64 (BitVec.ofNat 64 l.length))) :=
      evalStmtFuel_return F _ _ _ hret
    have hstmt : evalStmtFuel F vecBinSearchFunc.body
        [("s", .stdVecVal l), ("target", .i32 t)] =
        .ok (ρ', .returned (.u64 (BitVec.ofNat 64 l.length))) := by
      rw [hbody,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_lo,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_hi,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_mid,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_x, henv]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hwhile).trans hretS
    simp [evalFuncFuel, hbind, hstmt, hfwd]
