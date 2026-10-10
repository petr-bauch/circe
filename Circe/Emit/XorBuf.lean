/-
Circe.Emit.XorBuf — the K2 bounded buffer-xor kernel `xor_n`
(`out[i] = a[i] ^ b[i]`, `i in [0, n)`): the first entry with buffer
params (`mutBorrow` out + `sharedBorrow` ins, length-paired `n`),
with forward and `emit_correct` proofs. Indices are `u64` (faithful
to CIRGen — the N9 precedent; the S3 `u32` reader precedent does not
apply to writer loops).
-/
import Circe.Emit.Fragment

/-- Loop body: `out[i] = a[i] ^ b[i]; i++` (one `cir.xor` + one
    word-store, the `cir.for` step region). -/
def xorBody : CStmt :=
  .seq (.arrSet "out" (.var "i")
           (.bxor (.idxu "a" (.var "i")) (.idxu "b" (.var "i"))))
       (.assign "i" (.uadd (.var "i")
         (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Loop: `while (i < n) { ... }` (`cir.for` cond region). -/
def xorWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) xorBody

/-- Canonical CoreIR for `tests/c/xor_n.c`: single bounded `for`
    (`i in [0, n)`), one `cir.xor` + one word-store per iteration,
    stores only to `out`. -/
def xorNFunc : Func :=
  ⟨"xor_n",
   [{ name := "out", ty := .array (.u 32) 4096, role := .mutBorrow 0 },
    { name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "b", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .array (.u 32) 4096,
   .seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq xorWhile (.return_ (.var "out")))⟩

/-- Prefix xor: first `n` words of `o` replaced by `a[i] ^^^ b[i]`
    (out-of-bounds indices keep the old word via `getD`; unreachable
    under the length hypotheses the forward checks). -/
def xorNList (o a b : List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => o
  | n+1 =>
    ((xorNList o a b n).set n ((a[n]?.getD 0) ^^^ (b[n]?.getD 0)))

/-- Unfolding the last step (definitional). -/
theorem xorNList_succ (o a b : List (BitVec 32)) (n : Nat) :
    xorNList o a b (n + 1) =
      ((xorNList o a b n).set n
        ((a[n]?.getD 0) ^^^ (b[n]?.getD 0))) := rfl

/-- The prefix keeps its length. -/
theorem xorNList_length (o a b : List (BitVec 32)) (n : Nat) :
    (xorNList o a b n).length = o.length := by
  induction n generalizing o with
  | zero => rfl
  | succ k ih => simp [xorNList, ih, List.length_set]

/-- Value-level forward for `xor_n`: the xored prefix, `OOB` when `n`
    exceeds any buffer (C would read/write out of bounds — UB made
    loud, reads before the write). -/
def xorNFwd (o a b : List (BitVec 32)) (n : BitVec 64) : Result Value :=
  if n.toNat ≤ o.length ∧ n.toNat ≤ a.length ∧ n.toNat ≤ b.length then
    .ok (.arr32 (xorNList o a b n.toNat))
  else .error .OOB

/-! ### Loop-env lemmas -/

/-- Loop env: index `k`, current out-list `cur` (`a`/`b`/`n` fixed). -/
def mkXorEnv (a b : List (BitVec 32)) (nv : BitVec 64) (k : Nat)
    (cur : List (BitVec 32)) : Env :=
  [("i", .u64 (BitVec.ofNat 64 k)), ("out", .arr32 cur),
   ("a", .arr32 a), ("b", .arr32 b), ("n", .u64 nv)]

theorem mkXorEnv_i (a b : List (BitVec 32)) (nv : BitVec 64) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkXorEnv a b nv k cur) "i" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkXorEnv, envLookup]

theorem mkXorEnv_out (a b : List (BitVec 32)) (nv : BitVec 64) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkXorEnv a b nv k cur) "out" = some (.arr32 cur) := by
  simp [mkXorEnv, envLookup, show ("out" : String) ≠ "i" by decide]

theorem mkXorEnv_a (a b : List (BitVec 32)) (nv : BitVec 64) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkXorEnv a b nv k cur) "a" = some (.arr32 a) := by
  simp [mkXorEnv, envLookup, show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "out" by decide]

theorem mkXorEnv_b (a b : List (BitVec 32)) (nv : BitVec 64) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkXorEnv a b nv k cur) "b" = some (.arr32 b) := by
  simp [mkXorEnv, envLookup, show ("b" : String) ≠ "i" by decide,
    show ("b" : String) ≠ "out" by decide,
    show ("b" : String) ≠ "a" by decide]

theorem mkXorEnv_n (a b : List (BitVec 32)) (nv : BitVec 64) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkXorEnv a b nv k cur) "n" = some (.u64 nv) := by
  simp [mkXorEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "out" by decide,
    show ("n" : String) ≠ "a" by decide,
    show ("n" : String) ≠ "b" by decide]

/-- Updating `out` in a loop env stays a loop env. -/
theorem xorEnv_update_out (a b : List (BitVec 32)) (nv : BitVec 64)
    (k : Nat) (cur v : List (BitVec 32)) :
    envUpdate (mkXorEnv a b nv k cur) "out" (.arr32 v) =
      some (mkXorEnv a b nv k v) := by
  simp [mkXorEnv, envUpdate, show ("out" : String) ≠ "i" by decide]

/-- Updating `i` in a loop env stays a loop env. -/
theorem xorEnv_update_i (a b : List (BitVec 32)) (nv : BitVec 64)
    (k k' : Nat) (cur : List (BitVec 32)) :
    envUpdate (mkXorEnv a b nv k cur) "i"
        (.u64 (BitVec.ofNat 64 k')) =
      some (mkXorEnv a b nv k' cur) := by
  simp [mkXorEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem xorCond_eval (a b : List (BitVec 32)) (nv : BitVec 64) (k : Nat)
    (cur : List (BitVec 32)) (h : k < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.var "n")) (mkXorEnv a b nv k cur) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkXorEnv_i a b nv k cur
  have hn := mkXorEnv_n a b nv k cur
  simp [evalExpr, hi, hn, ofNat64_ult k nv h]

/-- The prefix-update commutes with the spec tail (invariant
    maintenance, shared by the ok and `OOB` inductions). -/
theorem xorCur_step (o a b : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32))
    (hcur : cur = xorNList o a b k)
    (hka : k < a.length) (hkb : k < b.length) :
    cur.set k (a[k] ^^^ b[k]) = xorNList o a b (k + 1) := by
  have hgeta : a[k]? = some a[k] := List.getElem?_eq_getElem hka
  have hgetb : b[k]? = some b[k] := List.getElem?_eq_getElem hkb
  have e1 : a[k]?.getD 0 = a[k] := by simp [hgeta]
  have e2 : b[k]?.getD 0 = b[k] := by simp [hgetb]
  rw [hcur, xorNList_succ, e1, e2]

/-- One body step xors the `k`-th word and advances the index (any
    fuel: loop-free). -/
theorem xorBody_eval (F : Nat) (a b : List (BitVec 32)) (nv : BitVec 64)
    (k : Nat) (cur : List (BitVec 32))
    (hka : k < a.length) (hkb : k < b.length) (hko : k < cur.length)
    (hk64 : k < 2 ^ 64) :
    evalStmtFuel F xorBody (mkXorEnv a b nv k cur) =
      .ok (mkXorEnv a b nv (k + 1) (cur.set k (a[k] ^^^ b[k])),
        .fellThrough) := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hgeta : a[k]? = some a[k] := List.getElem?_eq_getElem hka
  have hgetb : b[k]? = some b[k] := List.getElem?_eq_getElem hkb
  have hgeto : cur[k]? = some cur[k] := List.getElem?_eq_getElem hko
  have hxor : evalExpr
        (.bxor (.idxu "a" (.var "i")) (.idxu "b" (.var "i")))
        (mkXorEnv a b nv k cur) = .ok (.u32 (a[k] ^^^ b[k])) := by
    have ha := mkXorEnv_a a b nv k cur
    have hb := mkXorEnv_b a b nv k cur
    have hi := mkXorEnv_i a b nv k cur
    simp only [evalExpr, ha, hb, hi, hkk, hgeta, hgetb]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkXorEnv a b nv k (cur.set k (a[k] ^^^ b[k]))) =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkXorEnv_i a b nv k (cur.set k (a[k] ^^^ b[k]))
    simp only [evalExpr, litVal, h1, ofNat64_add_one]
  have up1 := xorEnv_update_out a b nv k cur (cur.set k (a[k] ^^^ b[k]))
  have up2 := xorEnv_update_i a b nv k (k + 1) (cur.set k (a[k] ^^^ b[k]))
  have hi0 := mkXorEnv_i a b nv k cur
  have hie : evalExpr (.var "i") (mkXorEnv a b nv k cur) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hi0]
  have harr0 := mkXorEnv_out a b nv k cur
  -- `simp only` (no `BitVec` mod-normalization): `hkk` aligns the
  -- `i.toNat` index the evaluator produces with `k` (N9 precedent).
  cases F <;>
    simp only [xorBody, evalStmtFuel, evalStmtZero, evalStmtWith, hie, hxor, harr0, hkk, hgeto, up1, hi2, up2]

/-- The read-`a` failure: `OOB` propagates through the body. -/
theorem xorBody_error_a (F : Nat) (a b : List (BitVec 32))
    (nv : BitVec 64) (k : Nat) (cur : List (BitVec 32))
    (hka : ¬ k < a.length) (hk64 : k < 2 ^ 64) :
    evalStmtFuel F xorBody (mkXorEnv a b nv k cur) = .error .OOB := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hi0 := mkXorEnv_i a b nv k cur
  have hgeta : a[k]? = none :=
    List.getElem?_eq_none (Nat.le_of_not_gt hka)
  have hxorerr : evalExpr
        (.bxor (.idxu "a" (.var "i")) (.idxu "b" (.var "i")))
        (mkXorEnv a b nv k cur) = .error .OOB := by
    have ha := mkXorEnv_a a b nv k cur
    have hi := mkXorEnv_i a b nv k cur
    simp only [evalExpr, ha, hi, hkk, hgeta]
  have hie : evalExpr (.var "i") (mkXorEnv a b nv k cur) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hi0]
  cases F <;>
    simp only [xorBody, evalStmtFuel, evalStmtZero, evalStmtWith, hie, hxorerr]

/-- The read-`b` failure (the `a` read succeeds first). -/
theorem xorBody_error_b (F : Nat) (a b : List (BitVec 32))
    (nv : BitVec 64) (k : Nat) (cur : List (BitVec 32))
    (hka : k < a.length) (hkb : ¬ k < b.length) (hk64 : k < 2 ^ 64) :
    evalStmtFuel F xorBody (mkXorEnv a b nv k cur) = .error .OOB := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hi0 := mkXorEnv_i a b nv k cur
  have hgeta : a[k]? = some a[k] := List.getElem?_eq_getElem hka
  have hgetb : b[k]? = none :=
    List.getElem?_eq_none (Nat.le_of_not_gt hkb)
  have hxorerr : evalExpr
        (.bxor (.idxu "a" (.var "i")) (.idxu "b" (.var "i")))
        (mkXorEnv a b nv k cur) = .error .OOB := by
    have ha := mkXorEnv_a a b nv k cur
    have hb := mkXorEnv_b a b nv k cur
    have hi := mkXorEnv_i a b nv k cur
    simp only [evalExpr, ha, hb, hi, hkk, hgeta, hgetb]
  have hie : evalExpr (.var "i") (mkXorEnv a b nv k cur) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hi0]
  cases F <;>
    simp only [xorBody, evalStmtFuel, evalStmtZero, evalStmtWith, hie, hxorerr]

/-- The write failure: both reads succeed, the `arrSet` is `OOB`. -/
theorem xorBody_error_o (F : Nat) (a b : List (BitVec 32))
    (nv : BitVec 64) (k : Nat) (cur : List (BitVec 32))
    (hka : k < a.length) (hkb : k < b.length)
    (hko : ¬ k < cur.length) (hk64 : k < 2 ^ 64) :
    evalStmtFuel F xorBody (mkXorEnv a b nv k cur) = .error .OOB := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hgeta : a[k]? = some a[k] := List.getElem?_eq_getElem hka
  have hgetb : b[k]? = some b[k] := List.getElem?_eq_getElem hkb
  have hgeto : cur[k]? = none :=
    List.getElem?_eq_none (Nat.le_of_not_gt hko)
  have hxor : evalExpr
        (.bxor (.idxu "a" (.var "i")) (.idxu "b" (.var "i")))
        (mkXorEnv a b nv k cur) = .ok (.u32 (a[k] ^^^ b[k])) := by
    have ha := mkXorEnv_a a b nv k cur
    have hb := mkXorEnv_b a b nv k cur
    have hi := mkXorEnv_i a b nv k cur
    simp only [evalExpr, ha, hb, hi, hkk, hgeta, hgetb]
  have hi0 := mkXorEnv_i a b nv k cur
  have hie : evalExpr (.var "i") (mkXorEnv a b nv k cur) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hi0]
  have harr0 := mkXorEnv_out a b nv k cur
  cases F <;>
    simp only [xorBody, evalStmtFuel, evalStmtZero, evalStmtWith, hie, hxor, harr0, hkk, hgeto]

/-! ### Loop correctness (fuel induction) -/

/-- Loop correctness, in-range: the loop xors the remaining suffix. -/
theorem xorWhile_correct (o a b : List (BitVec 32)) (nv : BitVec 64)
    (F k : Nat) (cur : List (BitVec 32))
    (hk : k ≤ nv.toNat)
    (hlen : nv.toNat ≤ o.length ∧ nv.toNat ≤ a.length ∧ nv.toNat ≤ b.length)
    (hcur : cur = xorNList o a b k)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F xorWhile (mkXorEnv a b nv k cur) =
      .ok (mkXorEnv a b nv nv.toNat (xorNList o a b nv.toNat),
        .fellThrough) := by
  induction F generalizing k cur with
  | zero =>
    have hkn : k = nv.toNat := by omega
    subst hkn
    have hk64 : nv.toNat < 2 ^ 64 := nv.isLt
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkXorEnv a b nv nv.toNat cur) = .ok (.b false) := by
      simpa using (xorCond_eval a b nv nv.toNat cur hk64)
    -- `hcur` rewrites `cur` inside the goal scrutinee, so align
    -- `hcond` with it first (else the rule cannot fire).
    rw [hcur] at hcond
    simp [xorWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcond, hcur]
  | succ F ih =>
    by_cases hkn : k < nv.toNat
    · have hk64 : k < 2 ^ 64 := by omega
      have hcond := xorCond_eval a b nv k cur hk64
      have hcondT : evalExpr (.ult (.var "i") (.var "n"))
          (mkXorEnv a b nv k cur) = .ok (.b true) := by
        simpa [hkn] using hcond
      obtain ⟨hlo, hla, hlb⟩ := hlen
      have hka : k < a.length := by omega
      have hkb : k < b.length := by omega
      have hko : k < cur.length := by rw [hcur, xorNList_length]; omega
      have hbody := xorBody_eval F a b nv k cur hka hkb hko hk64
      have hstep : evalStmtFuel (F + 1) xorWhile (mkXorEnv a b nv k cur)
          = evalStmtFuel F xorWhile
            (mkXorEnv a b nv (k + 1) (cur.set k (a[k] ^^^ b[k]))) := by
        simp [xorWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondT, hbody]
      rw [hstep]
      exact ih (k + 1) (cur.set k (a[k] ^^^ b[k])) (by omega)
        (xorCur_step o a b k cur hcur hka hkb) (by omega)
    · have hkn' : k = nv.toNat := by omega
      have hk64 : k < 2 ^ 64 := by omega
      have hcond := xorCond_eval a b nv k cur hk64
      have hcondF : evalExpr (.ult (.var "i") (.var "n"))
          (mkXorEnv a b nv k cur) = .ok (.b false) := by
        simpa [hkn'] using hcond
      rw [hkn'] at hcondF hcur ⊢
      rw [hcur] at hcondF
      simp [xorWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondF, hcur]

/-- Exiting past the end with a short buffer is impossible (the
    failure below fires first); shared by the `OOB` induction exits. -/
theorem xorOob_exit_false (o a b : List (BitVec 32)) (nv : BitVec 64)
    (k : Nat)
    (hkn : k = nv.toNat)
    (hfail : ¬ (nv.toNat ≤ o.length ∧ nv.toNat ≤ a.length ∧
      nv.toNat ≤ b.length))
    (hvalid : ∀ j : Nat, j < k → j < o.length ∧ j < a.length ∧
      j < b.length) : False := by
  -- Some buffer is short; that index is valid, hence self-smaller.
  have h3 : o.length < nv.toNat ∨ a.length < nv.toNat ∨
      b.length < nv.toNat := by omega
  obtain ho | ha | hb := h3
  · obtain ⟨ho', -, -⟩ := hvalid o.length (by omega)
    exact absurd ho' (Nat.lt_irrefl _)
  · obtain ⟨-, ha', -⟩ := hvalid a.length (by omega)
    exact absurd ha' (Nat.lt_irrefl _)
  · obtain ⟨-, -, hb'⟩ := hvalid b.length (by omega)
    exact absurd hb' (Nat.lt_irrefl _)

/-- Loop failure: past the shortest buffer the first short op errors. -/
theorem xorWhile_oob (o a b : List (BitVec 32)) (nv : BitVec 64)
    (F k : Nat) (cur : List (BitVec 32))
    (hk : k ≤ nv.toNat)
    (hfail : ¬ (nv.toNat ≤ o.length ∧ nv.toNat ≤ a.length ∧
      nv.toNat ≤ b.length))
    (hcur : cur = xorNList o a b k)
    (hvalid : ∀ j : Nat, j < k → j < o.length ∧ j < a.length ∧
      j < b.length)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F xorWhile (mkXorEnv a b nv k cur) = .error .OOB := by
  induction F generalizing k cur with
  | zero =>
    have hkn : k = nv.toNat := by omega
    exact False.elim (xorOob_exit_false o a b nv k hkn hfail hvalid)
  | succ F ih =>
    by_cases hkn : k < nv.toNat
    · have hk64 : k < 2 ^ 64 := by omega
      have hcond := xorCond_eval a b nv k cur hk64
      have hcondT : evalExpr (.ult (.var "i") (.var "n"))
          (mkXorEnv a b nv k cur) = .ok (.b true) := by
        simpa [hkn] using hcond
      by_cases hka : k < a.length
      · by_cases hkb : k < b.length
        · by_cases hko : k < cur.length
          · have hbody := xorBody_eval F a b nv k cur hka hkb hko hk64
            have hstep : evalStmtFuel (F + 1) xorWhile
                  (mkXorEnv a b nv k cur)
                = evalStmtFuel F xorWhile
                  (mkXorEnv a b nv (k + 1)
                    (cur.set k (a[k] ^^^ b[k]))) := by
              simp [xorWhile, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcondT, hbody]
            rw [hstep]
            -- The step keeps every index `< k + 1` valid (`k` itself
            -- lands in `o` via the just-written prefix).
            have hvalid' : ∀ j : Nat, j < k + 1 →
                j < o.length ∧ j < a.length ∧ j < b.length := by
              intro j hj
              by_cases hjk : j < k
              · exact hvalid j hjk
              · have hjk' : j = k := by omega
                have hko' : k < o.length := by
                  rw [hcur, xorNList_length] at hko
                  exact hko
                rw [hjk']
                exact ⟨hko', hka, hkb⟩
            exact ih (k + 1) (cur.set k (a[k] ^^^ b[k])) (by omega)
              (xorCur_step o a b k cur hcur hka hkb) hvalid' (by omega)
          · have hbody := xorBody_error_o F a b nv k cur hka hkb hko
              hk64
            simp [xorWhile, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hbody]
        · have hbody := xorBody_error_b F a b nv k cur hka hkb hk64
          simp [xorWhile, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcondT, hbody]
      · have hbody := xorBody_error_a F a b nv k cur hka hk64
        simp [xorWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcondT, hbody]
    · have hkn' : k = nv.toNat := by omega
      exact False.elim
        (xorOob_exit_false o a b nv k hkn' hfail hvalid)

/-! ### Whole-function correctness -/

/-- `emit_correct` for `xor_n`, at any fuel covering `n`. -/
theorem evalFuncFuel_xorN (F : Nat) (o a b : List (BitVec 32))
    (nv : BitVec 64)
    (hle : nv.toNat ≤ o.length ∧ nv.toNat ≤ a.length ∧
      nv.toNat ≤ b.length)
    (hF : nv.toNat ≤ F) :
    evalFuncFuel F xorNFunc [.arr32 o, .arr32 a, .arr32 b, .u64 nv] =
      xorNFwd o a b nv := by
  have henv : [("i", .u64 (BitVec.ofNat 64 0)), ("out", .arr32 o),
        ("a", .arr32 a), ("b", .arr32 b), ("n", .u64 nv)]
      = mkXorEnv a b nv 0 o := rfl
  have hret : envLookup
        (mkXorEnv a b nv nv.toNat (xorNList o a b nv.toNat)) "out" =
        some (.arr32 (xorNList o a b nv.toNat)) :=
    mkXorEnv_out a b nv nv.toNat (xorNList o a b nv.toNat)
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          xorWhile (mkXorEnv a b nv 0 o)
        = .ok (mkXorEnv a b nv nv.toNat (xorNList o a b nv.toNat),
            .fellThrough) :=
      xorWhile_correct o a b nv 0 0 o (Nat.zero_le _) hle rfl (by omega)
    simp [evalFuncFuel, xorNFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, xorNFwd, henv, hloopH0,
      hret, hle]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          xorWhile (mkXorEnv a b nv 0 o)
        = .ok (mkXorEnv a b nv nv.toNat (xorNList o a b nv.toNat),
            .fellThrough) :=
      xorWhile_correct o a b nv (F + 1) 0 o (Nat.zero_le _) hle rfl
        (by omega)
    simp [evalFuncFuel, xorNFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, xorNFwd, henv, hloopS, hret, hle]

/-- `emit_correct` for `xor_n` at the default fuel. -/
theorem emit_correct_xorN (o a b : List (BitVec 32)) (nv : BitVec 64)
    (hle : nv.toNat ≤ o.length ∧ nv.toNat ≤ a.length ∧
      nv.toNat ≤ b.length)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc xorNFunc [.arr32 o, .arr32 a, .arr32 b, .u64 nv] =
      xorNFwd o a b nv :=
  evalFuncFuel_xorN EVAL_FUEL o a b nv hle hfuel

/-- OOB corollary: over-long lengths fail loudly. -/
theorem evalFuncFuel_xorN_oob (F : Nat) (o a b : List (BitVec 32))
    (nv : BitVec 64)
    (hfail : ¬ (nv.toNat ≤ o.length ∧ nv.toNat ≤ a.length ∧
      nv.toNat ≤ b.length))
    (hF : nv.toNat ≤ F) :
    evalFuncFuel F xorNFunc [.arr32 o, .arr32 a, .arr32 b, .u64 nv] =
      .error .OOB := by
  have henv : [("i", .u64 (BitVec.ofNat 64 0)), ("out", .arr32 o),
        ("a", .arr32 a), ("b", .arr32 b), ("n", .u64 nv)]
      = mkXorEnv a b nv 0 o := rfl
  have hvalid0 : ∀ j : Nat, j < 0 → j < o.length ∧ j < a.length ∧
      j < b.length := by
    intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          xorWhile (mkXorEnv a b nv 0 o) = .error .OOB :=
      xorWhile_oob o a b nv 0 0 o (Nat.zero_le _) hfail rfl hvalid0
        (by omega)
    simp [evalFuncFuel, xorNFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, henv, hloopH0]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          xorWhile (mkXorEnv a b nv 0 o) = .error .OOB :=
      xorWhile_oob o a b nv (F + 1) 0 o (Nat.zero_le _) hfail rfl
        hvalid0 (by omega)
    simp [evalFuncFuel, xorNFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, henv, hloopS]
