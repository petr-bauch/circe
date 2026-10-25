-- LoopOob gallery: the third short-read-loop use.
--
-- A copy loop `while (i < n) { dst[i] = src[i]; i++; }` over a
-- short source (`src.length < n ≤ dst.length`). The first
-- `src.length - i` iterations fall through (the ok leg,
-- `whileStep_of_bodyOk`); the iteration at `i = src.length` reads
-- past the source and the loop reports `OOB` (the err leg,
-- `whileErr_of_bodyErr`). The guard discharge is `iterGuardT`.
-- All three `Circe.Crypto.LoopOob` bricks fire, generalizing the
-- K6c xor-loop twins to a counter-plus-two-array loop.
--
-- Compile-gated: building this root (`lake build LoopOobGallery`)
-- is the check.
import Circe.Crypto.LoopOob

namespace LoopOobGallery

/-- Copy body: `dst[i] = src[i]; i = i + 1`. -/
def copyBody : CStmt :=
  .seq (.arrSet "dst" (.var "i") (.idxu "src" (.var "i")))
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Copy loop: `while (i < n) copyBody`. -/
def copyLoop : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) copyBody

/-- Empty program: the body is call-free, so evaluation never
    consults `prog`. -/
def copyProg : Prog := []

/-- Copy-loop environment: counter, destination, source, bound. -/
def mkCopyEnv (src dst : List (BitVec 32)) (n iB : BitVec 64) : Env :=
  [("i", .u64 iB), ("dst", .arr32 dst),
   ("src", .arr32 src), ("n", .u64 n)]

/-- The bound word equals the counter-target value (both name the
    same trip count `N`). -/
theorem ofNat64_eq (n : BitVec 64) (N : Nat)
    (hN : n.toNat = N) (hN64 : N < 2 ^ 64) :
    BitVec.ofNat 64 N = n :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN64, hN])

/-- The copy guard reads true below the bound (the `iterGuardT`
    brick, instantiated at the `n` variable). -/
theorem copyGuardT (src dst : List (BitVec 32)) (n : BitVec 64)
    (N : Nat) (hN : n.toNat = N) (hN64 : N < 2 ^ 64)
    (iB : BitVec 64) (i : Nat) (hi : iB.toNat = i) (hiN : i < N)
    (hnV : envLookup (mkCopyEnv src dst n iB) "n" = some (.u64 n))
    (hivar : evalExpr (.var "i") (mkCopyEnv src dst n iB) =
      .ok (.u64 iB)) :
    evalExpr (.ult (.var "i") (.var "n")) (mkCopyEnv src dst n iB) =
      .ok (.b true) := by
  have hbnd : evalExpr (.var "n") (mkCopyEnv src dst n iB) =
      .ok (.u64 (BitVec.ofNat 64 N)) := by
    rw [ofNat64_eq n N hN hN64]
    exact evalExpr_var_hit _ _ _ hnV
  exact iterGuardT (.var "n") _ iB i N hi hN64 hiN hivar hbnd

/-- Error leg: with the source exhausted, the value read misses and
    the `arrSet` (hence the body) reports `OOB` at any fuel. -/
theorem copyBody_oob (src dst : List (BitVec 32)) (n iB : BitVec 64)
    (hiV : envLookup (mkCopyEnv src dst n iB) "i" = some (.u64 iB))
    (hsrcV : envLookup (mkCopyEnv src dst n iB) "src" =
      some (.arr32 src))
    (hgetS' : src[iB.toNat]? = none) (F' : Nat) :
    evalProgStmt copyProg F' copyBody (mkCopyEnv src dst n iB) =
      .error .OOB := by
  have hivar : evalExpr (.var "i") (mkCopyEnv src dst n iB) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hiV
  have hmvErr : evalExpr (.idxu "src" (.var "i"))
      (mkCopyEnv src dst n iB) = .error .OOB := by
    simp only [evalExpr, hsrcV, hiV, hgetS']
  have harr : evalProgStmt copyProg F'
      (.arrSet "dst" (.var "i") (.idxu "src" (.var "i")))
      (mkCopyEnv src dst n iB) = .error .OOB := by
    cases F' <;>
      simp [evalProgStmt, evalStmtFuel, evalStmtZero,
        evalStmtWith, hivar, hmvErr]
  have hbody : copyBody =
      .seq (.arrSet "dst" (.var "i") (.idxu "src" (.var "i")))
        (.assign "i"
          (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))) := rfl
  rw [hbody, evalProgStmt_seq_err _ _ _ _ _ _ harr]

/-- Success leg: with both reads in bounds, the store goes through
    and the counter advances (the post-body env names the written
    destination and the bumped counter). -/
theorem copyBody_correct (src dst : List (BitVec 32)) (n : BitVec 64)
    (iB : BitVec 64)
    (hiV : envLookup (mkCopyEnv src dst n iB) "i" = some (.u64 iB))
    (hsrcV : envLookup (mkCopyEnv src dst n iB) "src" =
      some (.arr32 src))
    (hdstV : envLookup (mkCopyEnv src dst n iB) "dst" =
      some (.arr32 dst))
    (w : BitVec 32) (hgetS : src[iB.toNat]? = some w)
    (d : BitVec 32) (hgetD : dst[iB.toNat]? = some d)
    (huSet : envUpdate (mkCopyEnv src dst n iB) "dst"
      (.arr32 (dst.set iB.toNat w)) =
      some (mkCopyEnv src (dst.set iB.toNat w) n iB))
    (F' : Nat) :
    evalProgStmt copyProg F' copyBody (mkCopyEnv src dst n iB) =
      .ok (mkCopyEnv src (dst.set iB.toNat w) n
        (iB + BitVec.ofNat 64 1), .fellThrough) := by
  have hivar : evalExpr (.var "i") (mkCopyEnv src dst n iB) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hiV
  have hmvOk : evalExpr (.idxu "src" (.var "i"))
      (mkCopyEnv src dst n iB) = .ok (.u32 w) := by
    simp only [evalExpr, hsrcV, hiV, hgetS]
  have harrSet : evalProgStmt copyProg F'
      (.arrSet "dst" (.var "i") (.idxu "src" (.var "i")))
      (mkCopyEnv src dst n iB) =
      .ok (mkCopyEnv src (dst.set iB.toNat w) n iB,
        .fellThrough) := by
    simp only [evalProgStmt]
    exact evalStmtFuel_arrSet F' "dst" _ _ _ iB w dst d _
      hivar hmvOk hdstV hgetD huSet
  have hbody : copyBody =
      .seq (.arrSet "dst" (.var "i") (.idxu "src" (.var "i")))
        (.assign "i"
          (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))) := rfl
  rw [hbody, evalProgStmt_seq_fallthrough _ _ _ _ _ _ harrSet]
  simp only [evalProgStmt]
  have hivarMid : evalExpr (.var "i")
      (mkCopyEnv src (dst.set iB.toNat w) n iB) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ (by rfl)
  have haddOk : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkCopyEnv src (dst.set iB.toNat w) n iB) =
      .ok (.u64 (iB + BitVec.ofNat 64 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hivarMid (evalExpr_lit _ _)
  exact evalStmtFuel_assign _ _ _ _ _ _
    haddOk (by rfl)

/-- The copy loop over a short source reports `OOB`: induction on
    the remaining successful iterations `src.length - i`
    (the K6c recipe: `whileErr_of_bodyErr` closes the exhausted
    case, `whileStep_of_bodyOk` advances the success case). -/
theorem copyLoop_oob (src dst : List (BitVec 32)) (n : BitVec 64)
    (N : Nat) (hN : n.toNat = N) (hN64 : N < 2 ^ 64)
    (hshort : src.length < N) (hdst : N ≤ dst.length)
    (iB : BitVec 64) (i : Nat) (hi : iB.toNat = i)
    (hle : i ≤ src.length) (hiN : i < N)
    (k : Nat) (hk : src.length - i = k)
    (F : Nat) (hF : k + 1 ≤ F) :
    evalProgStmt copyProg F copyLoop (mkCopyEnv src dst n iB) =
      .error .OOB := by
  have u64add_exact : ∀ (x y : BitVec 64),
      x.toNat + y.toNat < 2 ^ 64 →
      (x + y).toNat = x.toNat + y.toNat := by
    intro x y h
    rw [BitVec.toNat_add]
    have hx : x.toNat < 2 ^ 64 := x.isLt
    have hy : y.toNat < 2 ^ 64 := y.isLt
    omega
  induction k generalizing iB i dst F with
  | zero =>
    have hgetS' : src[iB.toNat]? = none := by
      apply List.getElem?_eq_none
      rw [hi]
      omega
    cases F with
    | zero => omega
    | succ F' =>
      have hloop : copyLoop =
          .while_ (.ult (.var "i") (.var "n")) copyBody := rfl
      have hivar : evalExpr (.var "i") (mkCopyEnv src dst n iB) =
          .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ (by rfl)
      have hguard := copyGuardT src dst n N hN hN64 iB i hi hiN
        (by rfl) hivar
      exact whileErr_of_bodyErr copyProg F' _ _ _ _ _ hloop
        hguard (copyBody_oob src dst n iB (by rfl) (by rfl) hgetS' F')
  | succ k ih =>
    cases F with
    | zero => omega
    | succ F' =>
      have hloop : copyLoop =
          .while_ (.ult (.var "i") (.var "n")) copyBody := rfl
      have hivar : evalExpr (.var "i") (mkCopyEnv src dst n iB) =
          .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ (by rfl)
      have hguard := copyGuardT src dst n N hN hN64 iB i hi hiN
        (by rfl) hivar
      obtain ⟨w, hgetS0⟩ : ∃ w, src[i]? = some w :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hgetS : src[iB.toNat]? = some w := by
        rw [hi]
        exact hgetS0
      obtain ⟨d, hgetD0⟩ : ∃ d, dst[i]? = some d :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hgetD : dst[iB.toNat]? = some d := by
        rw [hi]
        exact hgetD0
      have hbodyOk := copyBody_correct src dst n iB (by rfl) (by rfl)
        (by rfl) w hgetS d hgetD (by rfl) F'
      have hwhile := whileStep_of_bodyOk copyProg F' _ _ _ _ _
        hloop hguard hbodyOk
      rw [hwhile]
      have h1 : (BitVec.ofNat 64 1).toNat = 1 := by decide
      have hiB1 : (iB + BitVec.ofNat 64 1).toNat = i + 1 := by
        have hb : iB.toNat + (BitVec.ofNat 64 1).toNat < 2 ^ 64 := by
          rw [hi, h1]
          omega
        have h := u64add_exact iB (BitVec.ofNat 64 1) hb
        rwa [hi, h1] at h
      exact ih (iB := iB + BitVec.ofNat 64 1) (i := i + 1)
        (dst := dst.set iB.toNat w) (F := F') (hi := hiB1)
        (hle := by omega) (hiN := by omega) (hk := by omega)
        (hF := by omega)
        (hdst := by rw [List.length_set]; exact hdst)

/-- Closed instance: `src = [1, 2]` against `n = 3` copies twice,
    then the `i = 2` read misses and the loop reports `OOB`. -/
def main : IO Unit := do
  let src : List (BitVec 32) := [1, 2]
  let dst : List (BitVec 32) := [0, 0, 0]
  let n : BitVec 64 := BitVec.ofNat 64 3
  match evalProgStmt copyProg 10 copyLoop
      (mkCopyEnv src dst n (BitVec.ofNat 64 0)) with
  | .error .OOB =>
    IO.println "loopoob-gallery: short-src copy reports OOB (ok)"
  | .error e =>
    throw (IO.userError
      s!"loopoob-gallery: want OOB, got {(repr e).pretty}")
  | .ok _ =>
    throw (IO.userError "loopoob-gallery: want OOB, loop fell through")

end LoopOobGallery
