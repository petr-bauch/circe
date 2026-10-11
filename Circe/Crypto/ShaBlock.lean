/-
Circe.Crypto.ShaBlock — the K5 SHA-256 compression function
`sha256_compress` (`tests/c/sha256_compress.c`), verified against
the K5b spec (`Circe.Crypto.Sha`).

Mirror discipline (K4 precedent): the schedule `w` starts as 64
zeros (the C's uninitialized array is written cell-by-cell before
any read — the gate pins the loops structurally via exact op
counts, the mirror abstracts the fill); the working vars `v` start
as 8 zeros; the round constants `K` are a `let_` whole-list copy of
`shaK` (never address-taken, K4 `x`-copy precedent). The five C
loops become five `while_`s over single-purpose bodies. Rotation
amounts are `u32` literals (all `< 32`, complements `< 32`), so no
shift UB arises (K1 `checkedShiftU32`).

Lengths are prefix-generic (K2 precedent): states longer than 24
words pass the tail through untouched; shorter than 24 is `OOB`
(the init loop reads `st[8+t]`, so a short state fails loudly in
the first loop — see `initBody_oob`/`initWhile_oob`).
-/
import Circe.Emit.Fragment
import Circe.Emit.ArraySort
import Circe.Crypto.Block
import Circe.Crypto.Sha

/-! ### Mirror fragments -/

/-- Rotate-right-by-`n` over a word read `X` (K1 leaves composed:
    `bshr`/`bshl` over `u32` literal amounts joined by `bor` —
    the `rotrAt` analog of K4's `rotlAt`). -/
def rotrE (X : CExpr) (n : Nat) : CExpr :=
  .bor (.bshr X (.lit (.u32 (BitVec.ofNat 32 n))))
    (.bshl X (.lit (.u32 (BitVec.ofNat 32 (32 - n)))))

/-- Block-copy body: `w[t] = st[8+t]; t++` (first `cir.for`). -/
def initBody : CStmt :=
  .seq (.arrSet "w" (.var "t")
          (.idxu "st" (.uadd (.lit (.u64 (BitVec.ofNat 64 8))) (.var "t"))))
    (.assign "t" (.uadd (.var "t") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The block-copy loop (`t in [0, 16)`). -/
def initWhile : CStmt :=
  .while_ (.ult (.var "t") (.lit (.u64 (BitVec.ofNat 64 16)))) initBody

/-- Schedule body: `w[u] = w[u-16]+s0(w[u-15])+w[u-7]+s1(w[u-2]);
    u++` (second `cir.for`; left-assoc adds, `Ch`-free — the schedule
    uses only the small sigmas). -/
def schedBody : CStmt :=
  .seq (.arrSet "w" (.var "u")
          (.uadd
            (.uadd
              (.uadd (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 16)))))
                (.bxor
                  (.bxor (rotrE (.idxu "w" (.usub (.var "u")
                      (.lit (.u64 (BitVec.ofNat 64 15))))) 7)
                    (rotrE (.idxu "w" (.usub (.var "u")
                      (.lit (.u64 (BitVec.ofNat 64 15))))) 18))
                  (.bshr (.idxu "w" (.usub (.var "u")
                      (.lit (.u64 (BitVec.ofNat 64 15)))))
                    (.lit (.u32 (BitVec.ofNat 32 3))))))
              (.idxu "w" (.usub (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 7))))))
            (.bxor
              (.bxor (rotrE (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 2))))) 17)
                (rotrE (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 2))))) 19))
              (.bshr (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 2)))))
                (.lit (.u32 (BitVec.ofNat 32 10)))))))
    (.assign "u" (.uadd (.var "u") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The schedule loop (`u in [16, 64)`). -/
def schedWhile : CStmt :=
  .while_ (.ult (.var "u") (.lit (.u64 (BitVec.ofNat 64 64)))) schedBody

/-- Work-init body: `v[i] = st[i]; i++` (third `cir.for`). -/
def vinitBody : CStmt :=
  .seq (.arrSet "v" (.var "i") (.idxu "st" (.var "i")))
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The work-init loop (`i in [0, 8)`). -/
def vinitWhile : CStmt :=
  .while_ (.ult (.var "i") (.lit (.u64 (BitVec.ofNat 64 8)))) vinitBody

/-- `(cV6 A B C D E Ff G H w[r] shaK[r])`: `h + S1(e) + Ch(e,f,g) + K[r] + w[r]` over pristine
    reads (the C's `t1` temp — computed before any store clobbers
    `v[7]/v[6]/v[5]/v[4]`, which is why the temps exist). -/
def t1Expr : CExpr :=
  .uadd
    (.uadd
      (.uadd
        (.uadd (.idxu "v" (atU64 7))
          (.bxor
            (.bxor (rotrE (.idxu "v" (atU64 4)) 6)
              (rotrE (.idxu "v" (atU64 4)) 11))
            (rotrE (.idxu "v" (atU64 4)) 25)))
        (.bxor (.idxu "v" (atU64 6))
          (.band (.idxu "v" (atU64 4))
            (.bxor (.idxu "v" (atU64 5))
              (.idxu "v" (atU64 6))))))
      (.idxu "K" (.var "r")))
    (.idxu "w" (.var "r"))

/-- `(cV12 A B C D E Ff G H w[r] shaK[r])`: `S0(a) + Maj(a,b,c)` over pristine reads. -/
def t2Expr : CExpr :=
  .uadd
    (.bxor
      (.bxor (rotrE (.idxu "v" (atU64 0)) 2)
        (rotrE (.idxu "v" (atU64 0)) 13))
      (rotrE (.idxu "v" (atU64 0)) 22))
    (.bxor
      (.bxor (.band (.idxu "v" (atU64 0)) (.idxu "v" (atU64 1)))
        (.band (.idxu "v" (atU64 0)) (.idxu "v" (atU64 2))))
      (.band (.idxu "v" (atU64 1)) (.idxu "v" (atU64 2))))

/-- One compression round over `v[0..8]` (FIPS 180-4 §6.2.2 body:
    `t1`/`t2` bound first over pristine reads, then the eight stores
    high-to-low — every shift read hits a not-yet-written cell,
    exactly the C order; schedule word and round constant read via
    the `r` counter). -/
def compressFrag : CStmt :=
  .seq (.let_ "t1" (.u 32) t1Expr)
  (.seq (.let_ "t2" (.u 32) t2Expr)
  (.seq (.arrSet "v" (atU64 7) (.idxu "v" (atU64 6)))
  (.seq (.arrSet "v" (atU64 6) (.idxu "v" (atU64 5)))
  (.seq (.arrSet "v" (atU64 5) (.idxu "v" (atU64 4)))
  (.seq (.arrSet "v" (atU64 4)
            (.uadd (.idxu "v" (atU64 3)) (.var "t1")))
  (.seq (.arrSet "v" (atU64 3) (.idxu "v" (atU64 2)))
  (.seq (.arrSet "v" (atU64 2) (.idxu "v" (atU64 1)))
  (.seq (.arrSet "v" (atU64 1) (.idxu "v" (atU64 0)))
    (.arrSet "v" (atU64 0)
      (.uadd (.var "t1") (.var "t2")))))))))))

/-- Round-loop body: one compression round, then `r++`. -/
def shaRoundBody : CStmt :=
  .seq compressFrag
    (.assign "r" (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The 64-round loop (`r in [0, 64)`). -/
def compressWhile : CStmt :=
  .while_ (.ult (.var "r") (.lit (.u64 (BitVec.ofNat 64 64)))) shaRoundBody

/-- Add-back body: `st[j] += v[j]; j++` (fifth `cir.for`). -/
def shaAddBody : CStmt :=
  .seq (.arrSet "st" (.var "j")
          (.uadd (.idxu "st" (.var "j")) (.idxu "v" (.var "j"))))
       (.assign "j" (.uadd (.var "j")
         (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The add-back loop (`j in [0, 8)`). -/
def shaAddWhile : CStmt :=
  .while_ (.ult (.var "j") (.lit (.u64 (BitVec.ofNat 64 8)))) shaAddBody

/-- Canonical CoreIR for `tests/c/sha256_compress.c`: zeroed
    schedule filled from the block tail, 48 schedule steps, zeroed
    working vars filled from the digest head, the `K` table, 64
    compression rounds, add-back over `st`, returning the buffer. -/
def sha256Func : Func :=
  ⟨"sha256_compress",
   [{ name := "st", ty := .array (.u 32) 24, role := .mutBorrow 0 }],
   .array (.u 32) 24,
   .seq (.let_ "w" (.array (.u 32) 64)
           (.lit (.arr32 (List.replicate 64 0))))
   (.seq (.let_ "t" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq initWhile
   (.seq (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 16))))
   (.seq schedWhile
   (.seq (.let_ "v" (.array (.u 32) 8)
             (.lit (.arr32 (List.replicate 8 0))))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq vinitWhile
   (.seq (.let_ "K" (.array (.u 32) 64) (.lit (.arr32 shaK)))
   (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq compressWhile
   (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq shaAddWhile (.return_ (.var "st"))))))))))))))⟩

/-- Value-level forward for `sha256_compress`: the K5b fold gated on
    24 words; `OOB` below (the init loop reads `st[8+t]` — C would
    read out of bounds). Longer states pass the tail through (K2
    prefix-generic precedent). -/
def sha256FuncFwd (s : List (BitVec 32)) : Result Value :=
  if 24 ≤ s.length then .ok (.arr32 (sha256CompressFwd s))
  else .error .OOB

/-! ### Value mirrors (one definition site per sub-value, K4 `qrV` precedent) -/

/-- Schedule-word sub-values over reads `A B C D`
    (`w[u-16]`, `w[u-15]`, `w[u-7]`, `w[u-2]`), mirroring the
    `schedBody` nesting exactly. -/
def sV1 (_A B _C _D : BitVec 32) : BitVec 32 := rotrU32 B 7
def sV2 (_A B _C _D : BitVec 32) : BitVec 32 := rotrU32 B 18
def sV3 (A B C D : BitVec 32) : BitVec 32 :=
  sV1 A B C D ^^^ sV2 A B C D
def sV4 (A B C D : BitVec 32) : BitVec 32 :=
  sV3 A B C D ^^^ (B >>> 3)
def sV5 (_A _B _C D : BitVec 32) : BitVec 32 := rotrU32 D 17
def sV6 (_A _B _C D : BitVec 32) : BitVec 32 := rotrU32 D 19
def sV7 (A B C D : BitVec 32) : BitVec 32 :=
  sV5 A B C D ^^^ sV6 A B C D
def sV8 (A B C D : BitVec 32) : BitVec 32 :=
  sV7 A B C D ^^^ (D >>> 10)
def sV9 (A B C D : BitVec 32) : BitVec 32 := A + sV4 A B C D
def sV10 (A B C D : BitVec 32) : BitVec 32 := sV9 A B C D + C
def sV11 (A B C D : BitVec 32) : BitVec 32 := sV10 A B C D + sV8 A B C D

/-- Round sub-values over working reads `A..H`, schedule word `WT`
    and constant `KK`, mirroring the `compressFrag` nesting. -/
def cV1 (_A _B _C _D E _F _G _H _WT _KK : BitVec 32) : BitVec 32 := rotrU32 E 6
def cV2 (_A _B _C _D E _F _G _H _WT _KK : BitVec 32) : BitVec 32 := rotrU32 E 11
def cV3 (_A _B _C _D E _F _G _H _WT _KK : BitVec 32) : BitVec 32 := rotrU32 E 25
def cV4 (A B C D E F G H WT KK : BitVec 32) : BitVec 32 :=
  cV1 A B C D E F G H WT KK ^^^ cV2 A B C D E F G H WT KK ^^^
    cV3 A B C D E F G H WT KK
def cV5 (A B C D E F G H WT KK : BitVec 32) : BitVec 32 :=
  G ^^^ (E &&& (F ^^^ G))
def cV6 (A B C D E F G H WT KK : BitVec 32) : BitVec 32 :=
  H + cV4 A B C D E F G H WT KK + cV5 A B C D E F G H WT KK + KK + WT
def cV7 (A _B _C _D _E _F _G _H _WT _KK : BitVec 32) : BitVec 32 := rotrU32 A 2
def cV8 (A _B _C _D _E _F _G _H _WT _KK : BitVec 32) : BitVec 32 := rotrU32 A 13
def cV9 (A _B _C _D _E _F _G _H _WT _KK : BitVec 32) : BitVec 32 := rotrU32 A 22
def cV10 (A B C D E F G H WT KK : BitVec 32) : BitVec 32 :=
  cV7 A B C D E F G H WT KK ^^^ cV8 A B C D E F G H WT KK ^^^
    cV9 A B C D E F G H WT KK
def cV11 (A B C D E F G H WT KK : BitVec 32) : BitVec 32 :=
  (A &&& B) ^^^ (A &&& C) ^^^ (B &&& C)
def cV12 (A B C D E F G H WT KK : BitVec 32) : BitVec 32 :=
  cV10 A B C D E F G H WT KK + cV11 A B C D E F G H WT KK

/-! ### Index-arithmetic and rotate helpers -/

/-- Wrapping `u64` addition is exact when the sum fits (the `8 + t`
    block reads; same shape as `u64sub_toNat_exact`). -/
theorem ofNat64_add_toNat (a b : Nat) (h : a + b < 2 ^ 64) :
    ((BitVec.ofNat 64 a) + (BitVec.ofNat 64 b)).toNat = a + b := by
  have ha : (BitVec.ofNat 64 a).toNat = a := ofNat64_toNat a (by omega)
  have hb : (BitVec.ofNat 64 b).toNat = b := ofNat64_toNat b (by omega)
  rw [BitVec.toNat_add, ha, hb, Nat.mod_eq_of_lt h]

/-- Wrapping `u64` subtraction is exact when the subtrahend fits
    (the `u - c` schedule reads). -/
theorem ofNat64_sub_toNat (t c : Nat) (hc : c ≤ t) (ht : t < 2 ^ 64) :
    ((BitVec.ofNat 64 t) - (BitVec.ofNat 64 c)).toNat = t - c := by
  have h := u64sub_toNat_exact (BitVec.ofNat 64 t) (BitVec.ofNat 64 c)
    (by rw [ofNat64_toNat t ht, ofNat64_toNat c (by omega)]; omega)
  rw [h, ofNat64_toNat t ht, ofNat64_toNat c (by omega)]

/-- Addition stays in `ofNat` form (for the counter/index envs). -/
theorem ofNat64_add (a b : Nat) (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.toNat_inj.mp
  rw [ofNat64_add_toNat a b h, ofNat64_toNat (a + b) h]

/-- Subtraction stays in `ofNat` form (for the schedule index envs). -/
theorem ofNat64_sub (t c : Nat) (hc : c ≤ t) (ht : t < 2 ^ 64) :
    BitVec.ofNat 64 t - BitVec.ofNat 64 c = BitVec.ofNat 64 (t - c) := by
  apply BitVec.toNat_inj.mp
  rw [ofNat64_sub_toNat t c hc ht, ofNat64_toNat (t - c) (by omega)]

/-- A `rotrE` evaluates to the K5b `rotrU32` (both shift amounts are
    `< 32`, so the K1 check always succeeds — mirrors `rotlAt_eval`,
    with the K5b `rotrU32_shr`/`rotrU32_shl` bridges). -/
theorem rotrE_eval (ρ : Env) (v : BitVec 32) (X : CExpr) (n : Nat)
    (hX : evalExpr X ρ = .ok (.u32 v))
    (hn_toNat : (BitVec.ofNat 32 n).toNat = n)
    (hnc_toNat : (BitVec.ofNat 32 (32 - n)).toNat = 32 - n)
    (hn : n < 32) (hn0 : 0 < n) :
    evalExpr (rotrE X n) ρ = .ok (.u32 (rotrU32 v n)) := by
  have hshr : checkedShiftU32 v (BitVec.ofNat 32 n) (· >>> ·) =
      .ok (v >>> n) := by
    have h := checkedShiftU32_ok v (BitVec.ofNat 32 n) (· >>> ·)
      (by rw [hn_toNat]; exact hn)
    rw [hn_toNat] at h
    exact h
  have hshl : checkedShiftU32 v (BitVec.ofNat 32 (32 - n)) (· <<< ·) =
      .ok (v <<< (32 - n)) := by
    have h := checkedShiftU32_ok v (BitVec.ofNat 32 (32 - n)) (· <<< ·)
      (by rw [hnc_toNat]; omega)
    rw [hnc_toNat] at h
    exact h
  have e1 : evalExpr
        (.bshr X (.lit (.u32 (BitVec.ofNat 32 n)))) ρ =
        .ok (.u32 (v >>> n)) := by
    simp only [evalExpr, hX, litVal]
    rw [hshr]
    exact u32_map_ok _
  have e2 : evalExpr
        (.bshl X (.lit (.u32 (BitVec.ofNat 32 (32 - n))))) ρ =
        .ok (.u32 (v <<< (32 - n))) := by
    simp only [evalExpr, hX, litVal]
    rw [hshl]
    exact u32_map_ok _
  have hbor := evalExpr_bor_ok _ _ ρ _ _ e1 e2
  simp only [rotrE, hbor, rotrU32]

/-! ### Phase environments (accumulated `let_` scopes, K4 `mkRoundEnv` precedent) -/

/-- Reshape any 8-word list into cons form (for unfolding `roundStep`,
    whose match needs the constructor shape; proved once by
    extensionality over an `omega` case split — no extra imports). -/
theorem cons8 (v : List (BitVec 32)) (h : v.length = 8) :
    v = [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]] := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 8
  · have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
        i = 7 := by omega
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hc <;>
      (rw [List.getElem?_eq_getElem (by omega : _ < v.length)]; simp)
  · rw [List.getElem?_eq_none (show v.length ≤ i by omega),
      List.getElem?_eq_none (show [v[0], v[1], v[2], v[3], v[4],
        v[5], v[6], v[7]].length ≤ i by simp; omega)]

/-- Block-copy env: counter `t`, schedule `w`, input `st`. -/
def mkInitEnv (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32)) : Env :=
  [("t", .u64 (BitVec.ofNat 64 t)), ("w", .arr32 w), ("st", .arr32 s)]

theorem mkInitEnv_t (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32)) :
    envLookup (mkInitEnv s t w) "t" =
      some (.u64 (BitVec.ofNat 64 t)) := by
  simp [mkInitEnv, envLookup]

theorem mkInitEnv_w (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32)) :
    envLookup (mkInitEnv s t w) "w" = some (.arr32 w) := by
  simp [mkInitEnv, envLookup, show ("w" : String) ≠ "t" by decide]

theorem mkInitEnv_st (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32)) :
    envLookup (mkInitEnv s t w) "st" = some (.arr32 s) := by
  simp [mkInitEnv, envLookup, show ("st" : String) ≠ "t" by decide,
    show ("st" : String) ≠ "w" by decide]

theorem initEnv_update_w (s : List (BitVec 32)) (t : Nat)
    (w v : List (BitVec 32)) :
    envUpdate (mkInitEnv s t w) "w" (.arr32 v) =
      some (mkInitEnv s t v) := by
  simp [mkInitEnv, envUpdate, show ("w" : String) ≠ "t" by decide]

theorem initEnv_update_t (s : List (BitVec 32)) (t t' : Nat)
    (w : List (BitVec 32)) :
    envUpdate (mkInitEnv s t w) "t" (.u64 (BitVec.ofNat 64 t')) =
      some (mkInitEnv s t' w) := by
  simp [mkInitEnv, envUpdate]

theorem initCond_eval (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32)) (h : t < 2 ^ 64) :
    evalExpr (.ult (.var "t") (.lit (.u64 (BitVec.ofNat 64 16))))
        (mkInitEnv s t w) =
      .ok (.b (decide (t < 16))) := by
  have ht := mkInitEnv_t s t w
  have h16 : (BitVec.ofNat 64 16).toNat = 16 := ofNat64_toNat 16 (by decide)
  simp [evalExpr, ht, litVal, ofNat64_ult t _ h, h16]

/-- Schedule env: counter `u` over the stale `t = 16`. -/
def mkSchedEnv (s : List (BitVec 32)) (u : Nat)
    (w : List (BitVec 32)) : Env :=
  [("u", .u64 (BitVec.ofNat 64 u)), ("t", .u64 (BitVec.ofNat 64 16)),
   ("w", .arr32 w), ("st", .arr32 s)]

theorem mkSchedEnv_u (s : List (BitVec 32)) (u : Nat)
    (w : List (BitVec 32)) :
    envLookup (mkSchedEnv s u w) "u" =
      some (.u64 (BitVec.ofNat 64 u)) := by
  simp [mkSchedEnv, envLookup]

theorem mkSchedEnv_w (s : List (BitVec 32)) (u : Nat)
    (w : List (BitVec 32)) :
    envLookup (mkSchedEnv s u w) "w" = some (.arr32 w) := by
  simp [mkSchedEnv, envLookup, show ("w" : String) ≠ "u" by decide,
    show ("w" : String) ≠ "t" by decide]

theorem schedEnv_update_w (s : List (BitVec 32)) (u : Nat)
    (w v : List (BitVec 32)) :
    envUpdate (mkSchedEnv s u w) "w" (.arr32 v) =
      some (mkSchedEnv s u v) := by
  simp [mkSchedEnv, envUpdate, show ("w" : String) ≠ "u" by decide,
    show ("w" : String) ≠ "t" by decide]

theorem schedEnv_update_u (s : List (BitVec 32)) (u u' : Nat)
    (w : List (BitVec 32)) :
    envUpdate (mkSchedEnv s u w) "u" (.u64 (BitVec.ofNat 64 u')) =
      some (mkSchedEnv s u' w) := by
  simp [mkSchedEnv, envUpdate]

theorem schedCond_eval (s : List (BitVec 32)) (u : Nat)
    (w : List (BitVec 32)) (h : u < 2 ^ 64) :
    evalExpr (.ult (.var "u") (.lit (.u64 (BitVec.ofNat 64 64))))
        (mkSchedEnv s u w) =
      .ok (.b (decide (u < 64))) := by
  have hu := mkSchedEnv_u s u w
  have h64 : (BitVec.ofNat 64 64).toNat = 64 := ofNat64_toNat 64 (by decide)
  simp [evalExpr, hu, litVal, ofNat64_ult u _ h, h64]

/-- Work-init env: counter `i`, vars `v`, stale `u = 64`, `t = 16`. -/
def mkVinitEnv (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32)) : Env :=
  [("i", .u64 (BitVec.ofNat 64 i)), ("v", .arr32 v),
   ("u", .u64 (BitVec.ofNat 64 64)), ("t", .u64 (BitVec.ofNat 64 16)),
   ("w", .arr32 w), ("st", .arr32 s)]

theorem mkVinitEnv_i (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32)) :
    envLookup (mkVinitEnv s i v w) "i" =
      some (.u64 (BitVec.ofNat 64 i)) := by
  simp [mkVinitEnv, envLookup]

theorem mkVinitEnv_v (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32)) :
    envLookup (mkVinitEnv s i v w) "v" = some (.arr32 v) := by
  simp [mkVinitEnv, envLookup, show ("v" : String) ≠ "i" by decide]

theorem mkVinitEnv_st (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32)) :
    envLookup (mkVinitEnv s i v w) "st" = some (.arr32 s) := by
  simp [mkVinitEnv, envLookup, show ("st" : String) ≠ "i" by decide,
    show ("st" : String) ≠ "v" by decide,
    show ("st" : String) ≠ "u" by decide,
    show ("st" : String) ≠ "t" by decide,
    show ("st" : String) ≠ "w" by decide]

theorem vinitEnv_update_v (s : List (BitVec 32)) (i : Nat)
    (v v' w : List (BitVec 32)) :
    envUpdate (mkVinitEnv s i v w) "v" (.arr32 v') =
      some (mkVinitEnv s i v' w) := by
  simp [mkVinitEnv, envUpdate, show ("v" : String) ≠ "i" by decide]

theorem vinitEnv_update_i (s : List (BitVec 32)) (i i' : Nat)
    (v w : List (BitVec 32)) :
    envUpdate (mkVinitEnv s i v w) "i" (.u64 (BitVec.ofNat 64 i')) =
      some (mkVinitEnv s i' v w) := by
  simp [mkVinitEnv, envUpdate]

theorem vinitCond_eval (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32)) (h : i < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.lit (.u64 (BitVec.ofNat 64 8))))
        (mkVinitEnv s i v w) =
      .ok (.b (decide (i < 8))) := by
  have hi := mkVinitEnv_i s i v w
  have h8 : (BitVec.ofNat 64 8).toNat = 8 := ofNat64_toNat 8 (by decide)
  simp [evalExpr, hi, litVal, ofNat64_ult i _ h, h8]

/-- Compression env: round temps `t1`/`t2` (recomputed each
    iteration, hence params), counter `r`, the `K` table, working
    vars `v`, stale `i = 8`, `u = 64`, `t = 16`. -/
def mkCompressEnv (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) : Env :=
  [("t1", .u32 t1), ("t2", .u32 t2),
   ("r", .u64 (BitVec.ofNat 64 r)), ("K", .arr32 shaK),
   ("i", .u64 (BitVec.ofNat 64 8)), ("v", .arr32 v),
   ("u", .u64 (BitVec.ofNat 64 64)), ("t", .u64 (BitVec.ofNat 64 16)),
   ("w", .arr32 w), ("st", .arr32 s)]

theorem mkCompressEnv_t1 (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envLookup (mkCompressEnv s v r w t1 t2) "t1" = some (.u32 t1) := by
  simp [mkCompressEnv, envLookup]

theorem mkCompressEnv_t2 (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envLookup (mkCompressEnv s v r w t1 t2) "t2" = some (.u32 t2) := by
  simp [mkCompressEnv, envLookup, show ("t2" : String) ≠ "t1" by decide]

theorem mkCompressEnv_r (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envLookup (mkCompressEnv s v r w t1 t2) "r" =
      some (.u64 (BitVec.ofNat 64 r)) := by
  simp [mkCompressEnv, envLookup, show ("r" : String) ≠ "t1" by decide,
    show ("r" : String) ≠ "t2" by decide]

theorem mkCompressEnv_K (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envLookup (mkCompressEnv s v r w t1 t2) "K" = some (.arr32 shaK) := by
  simp [mkCompressEnv, envLookup, show ("K" : String) ≠ "t1" by decide,
    show ("K" : String) ≠ "t2" by decide,
    show ("K" : String) ≠ "r" by decide]

theorem mkCompressEnv_v (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envLookup (mkCompressEnv s v r w t1 t2) "v" = some (.arr32 v) := by
  simp [mkCompressEnv, envLookup, show ("v" : String) ≠ "t1" by decide,
    show ("v" : String) ≠ "t2" by decide,
    show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "K" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem mkCompressEnv_w (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envLookup (mkCompressEnv s v r w t1 t2) "w" = some (.arr32 w) := by
  simp [mkCompressEnv, envLookup, show ("w" : String) ≠ "t1" by decide,
    show ("w" : String) ≠ "t2" by decide,
    show ("w" : String) ≠ "r" by decide,
    show ("w" : String) ≠ "K" by decide,
    show ("w" : String) ≠ "i" by decide,
    show ("w" : String) ≠ "v" by decide,
    show ("w" : String) ≠ "u" by decide,
    show ("w" : String) ≠ "t" by decide]

theorem compressEnv_update_t1 (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t1' t2 : BitVec 32) :
    envUpdate (mkCompressEnv s v r w t1 t2) "t1" (.u32 t1') =
      some (mkCompressEnv s v r w t1' t2) := by
  simp [mkCompressEnv, envUpdate]

theorem compressEnv_update_t2 (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 t2' : BitVec 32) :
    envUpdate (mkCompressEnv s v r w t1 t2) "t2" (.u32 t2') =
      some (mkCompressEnv s v r w t1 t2') := by
  simp [mkCompressEnv, envUpdate, show ("t2" : String) ≠ "t1" by decide]

theorem compressEnv_update_v (s : List (BitVec 32)) (v v' : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envUpdate (mkCompressEnv s v r w t1 t2) "v" (.arr32 v') =
      some (mkCompressEnv s v' r w t1 t2) := by
  simp [mkCompressEnv, envUpdate, show ("v" : String) ≠ "t1" by decide,
    show ("v" : String) ≠ "t2" by decide,
    show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "K" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem compressEnv_update_r (s : List (BitVec 32)) (v : List (BitVec 32))
    (r r' : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) :
    envUpdate (mkCompressEnv s v r w t1 t2) "r" (.u64 (BitVec.ofNat 64 r')) =
      some (mkCompressEnv s v r' w t1 t2) := by
  simp [mkCompressEnv, envUpdate, show ("r" : String) ≠ "t1" by decide,
    show ("r" : String) ≠ "t2" by decide]

theorem compressCond_eval (s : List (BitVec 32)) (v : List (BitVec 32))
    (r : Nat) (w : List (BitVec 32)) (t1 t2 : BitVec 32) (h : r < 2 ^ 64) :
    evalExpr (.ult (.var "r") (.lit (.u64 (BitVec.ofNat 64 64))))
        (mkCompressEnv s v r w t1 t2) =
      .ok (.b (decide (r < 64))) := by
  have hr := mkCompressEnv_r s v r w t1 t2
  have h64 : (BitVec.ofNat 64 64).toNat = 64 := ofNat64_toNat 64 (by decide)
  simp [evalExpr, hr, litVal, ofNat64_ult r _ h, h64]

/-- Add-back env: counter `j` over the post-round env (`r = 64`
    throughout; `v` is the compressed copy, `st` evolves). -/
def mkShaAddEnv (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32)) : Env :=
  [("j", .u64 (BitVec.ofNat 64 j)), ("r", .u64 (BitVec.ofNat 64 64)),
   ("K", .arr32 shaK), ("i", .u64 (BitVec.ofNat 64 8)),
   ("v", .arr32 v), ("u", .u64 (BitVec.ofNat 64 64)),
   ("t", .u64 (BitVec.ofNat 64 16)), ("w", .arr32 w),
   ("st", .arr32 st)]

theorem mkShaAddEnv_j (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32)) :
    envLookup (mkShaAddEnv v w j st) "j" =
      some (.u64 (BitVec.ofNat 64 j)) := by
  simp [mkShaAddEnv, envLookup]

theorem mkShaAddEnv_v (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32)) :
    envLookup (mkShaAddEnv v w j st) "v" = some (.arr32 v) := by
  simp [mkShaAddEnv, envLookup, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "K" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem mkShaAddEnv_st (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32)) :
    envLookup (mkShaAddEnv v w j st) "st" = some (.arr32 st) := by
  simp [mkShaAddEnv, envLookup, show ("st" : String) ≠ "j" by decide,
    show ("st" : String) ≠ "r" by decide,
    show ("st" : String) ≠ "K" by decide,
    show ("st" : String) ≠ "i" by decide,
    show ("st" : String) ≠ "v" by decide,
    show ("st" : String) ≠ "u" by decide,
    show ("st" : String) ≠ "t" by decide,
    show ("st" : String) ≠ "w" by decide]

theorem shaAddEnv_update_st (v w : List (BitVec 32)) (j : Nat)
    (st st' : List (BitVec 32)) :
    envUpdate (mkShaAddEnv v w j st) "st" (.arr32 st') =
      some (mkShaAddEnv v w j st') := by
  simp [mkShaAddEnv, envUpdate, show ("st" : String) ≠ "j" by decide,
    show ("st" : String) ≠ "r" by decide,
    show ("st" : String) ≠ "K" by decide,
    show ("st" : String) ≠ "i" by decide,
    show ("st" : String) ≠ "v" by decide,
    show ("st" : String) ≠ "u" by decide,
    show ("st" : String) ≠ "t" by decide,
    show ("st" : String) ≠ "w" by decide]

theorem shaAddEnv_update_j (v w : List (BitVec 32)) (j j' : Nat)
    (st : List (BitVec 32)) :
    envUpdate (mkShaAddEnv v w j st) "j" (.u64 (BitVec.ofNat 64 j')) =
      some (mkShaAddEnv v w j' st) := by
  simp [mkShaAddEnv, envUpdate]

theorem shaAddCond_eval (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32)) (h : j < 2 ^ 64) :
    evalExpr (.ult (.var "j") (.lit (.u64 (BitVec.ofNat 64 8))))
        (mkShaAddEnv v w j st) =
      .ok (.b (decide (j < 8))) := by
  have hj := mkShaAddEnv_j v w j st
  have h8 : (BitVec.ofNat 64 8).toNat = 8 := ofNat64_toNat 8 (by decide)
  simp [evalExpr, hj, litVal, ofNat64_ult j _ h, h8]

/-! ### Per-step engines (K4 `roundArrSet`/`addArrSet` precedent) -/

/-- One `w`-cell write in an init env (counter index, value already
    evaluated). -/
theorem initArrSet (F : Nat) (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32)) (ve : CExpr) (v : BitVec 32)
    (ht : t < w.length) (ht64 : t < 2 ^ 64)
    (hv : evalExpr ve (mkInitEnv s t w) = .ok (.u32 v)) :
    evalStmtFuel F (.arrSet "w" (.var "t") ve) (mkInitEnv s t w) =
      .ok (mkInitEnv s t (w.set t v), .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 t).toNat = t := ofNat64_toNat t ht64
  have hiv : evalExpr (.var "t") (mkInitEnv s t w) =
      .ok (.u64 (BitVec.ofNat 64 t)) := by
    simp [evalExpr, mkInitEnv_t]
  have harr := mkInitEnv_w s t w
  have hget : w[(BitVec.ofNat 64 t).toNat]? = some w[t] := by
    rw [htoNat]; exact List.getElem?_eq_getElem ht
  have hu : envUpdate (mkInitEnv s t w) "w"
      (.arr32 (w.set (BitVec.ofNat 64 t).toNat v)) =
      some (mkInitEnv s t (w.set t v)) := by
    rw [htoNat]; exact initEnv_update_w s t w (w.set t v)
  exact evalStmtFuel_arrSet F "w" (.var "t") ve _ _ v w w[t] _ hiv hv harr
    hget hu

/-- One `w`-cell write in a sched env. -/
theorem schedArrSet (F : Nat) (s : List (BitVec 32)) (u : Nat)
    (w : List (BitVec 32)) (ve : CExpr) (v : BitVec 32)
    (hu : u < w.length) (hu64 : u < 2 ^ 64)
    (hv : evalExpr ve (mkSchedEnv s u w) = .ok (.u32 v)) :
    evalStmtFuel F (.arrSet "w" (.var "u") ve) (mkSchedEnv s u w) =
      .ok (mkSchedEnv s u (w.set u v), .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 u).toNat = u := ofNat64_toNat u hu64
  have hiv : evalExpr (.var "u") (mkSchedEnv s u w) =
      .ok (.u64 (BitVec.ofNat 64 u)) := by
    simp [evalExpr, mkSchedEnv_u]
  have harr := mkSchedEnv_w s u w
  have hget : w[(BitVec.ofNat 64 u).toNat]? = some w[u] := by
    rw [htoNat]; exact List.getElem?_eq_getElem hu
  have huu : envUpdate (mkSchedEnv s u w) "w"
      (.arr32 (w.set (BitVec.ofNat 64 u).toNat v)) =
      some (mkSchedEnv s u (w.set u v)) := by
    rw [htoNat]; exact schedEnv_update_w s u w (w.set u v)
  exact evalStmtFuel_arrSet F "w" (.var "u") ve _ _ v w w[u] _ hiv hv harr
    hget huu

/-- One `v`-cell write in a vinit env. -/
theorem vinitArrSet (F : Nat) (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32)) (ve : CExpr) (x : BitVec 32)
    (hi : i < v.length) (hi64 : i < 2 ^ 64)
    (hv : evalExpr ve (mkVinitEnv s i v w) = .ok (.u32 x)) :
    evalStmtFuel F (.arrSet "v" (.var "i") ve) (mkVinitEnv s i v w) =
      .ok (mkVinitEnv s i (v.set i x) w, .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat i hi64
  have hiv : evalExpr (.var "i") (mkVinitEnv s i v w) =
      .ok (.u64 (BitVec.ofNat 64 i)) := by
    simp [evalExpr, mkVinitEnv_i]
  have harr := mkVinitEnv_v s i v w
  have hget : v[(BitVec.ofNat 64 i).toNat]? = some v[i] := by
    rw [htoNat]; exact List.getElem?_eq_getElem hi
  have hu : envUpdate (mkVinitEnv s i v w) "v"
      (.arr32 (v.set (BitVec.ofNat 64 i).toNat x)) =
      some (mkVinitEnv s i (v.set i x) w) := by
    rw [htoNat]; exact vinitEnv_update_v s i v (v.set i x) w
  exact evalStmtFuel_arrSet F "v" (.var "i") ve _ _ x v v[i] _ hiv hv harr
    hget hu

/-- One `v`-cell write in a compress env (literal index, value
    already evaluated). -/
theorem compressArrSet (F : Nat) (s : List (BitVec 32))
    (vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 : BitVec 32)
    (t : Nat) (ve : CExpr) (v : BitVec 32)
    (ht : t < vv.length) (ht64 : t < 2 ^ 64)
    (hv : evalExpr ve (mkCompressEnv s vv r w t1 t2) = .ok (.u32 v)) :
    evalStmtFuel F (.arrSet "v" (atU64 t) ve) (mkCompressEnv s vv r w t1 t2) =
      .ok (mkCompressEnv s (vv.set t v) r w t1 t2, .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 t).toNat = t := ofNat64_toNat t ht64
  have hi : evalExpr (atU64 t) (mkCompressEnv s vv r w t1 t2) =
      .ok (.u64 (BitVec.ofNat 64 t)) := by
    simp [atU64, evalExpr, litVal]
  have harr := mkCompressEnv_v s vv r w t1 t2
  have hget : vv[(BitVec.ofNat 64 t).toNat]? = some vv[t] := by
    rw [htoNat]; exact List.getElem?_eq_getElem ht
  have hu : envUpdate (mkCompressEnv s vv r w t1 t2) "v"
      (.arr32 (vv.set (BitVec.ofNat 64 t).toNat v)) =
      some (mkCompressEnv s (vv.set t v) r w t1 t2) := by
    rw [htoNat]; exact compressEnv_update_v s vv (vv.set t v) r w t1 t2
  exact evalStmtFuel_arrSet F "v" (atU64 t) ve _ _ v vv vv[t] _ hi hv harr
    hget hu

/-- Post-`t1` env: the entry env with `t1` shadow-bound to `T1`.
    `envExtend` conses, so the stale slot stays behind — lookups
    agree with the rebuilt env, but the terms are not equal, hence
    the post-`let` chain lives in this shadow world (an `rfl`
    `henv`-style equation would be false). -/
def compEnv1 (s vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 T1 : BitVec 32) : Env :=
  envExtend (mkCompressEnv s vv r w t1 t2) "t1" (.u32 T1)

/-- Post-`t1`,`t2` env. -/
def compEnv2 (s vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 T1 T2 : BitVec 32) : Env :=
  envExtend (compEnv1 s vv r w t1 t2 T1) "t2" (.u32 T2)

theorem compEnv1_v (s vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 T1 : BitVec 32) :
    envLookup (compEnv1 s vv r w t1 t2 T1) "v" = some (.arr32 vv) := by
  simp [compEnv1, envExtend, mkCompressEnv, envLookup,
    show ("v" : String) ≠ "t1" by decide,
    show ("v" : String) ≠ "t2" by decide,
    show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "K" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem compEnv2_v (s vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 T1 T2 : BitVec 32) :
    envLookup (compEnv2 s vv r w t1 t2 T1 T2) "v" = some (.arr32 vv) := by
  simp [compEnv2, envExtend, compEnv1, mkCompressEnv, envLookup,
    show ("v" : String) ≠ "t2" by decide,
    show ("v" : String) ≠ "t1" by decide,
    show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "K" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem compEnv2_t1 (s vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 T1 T2 : BitVec 32) :
    envLookup (compEnv2 s vv r w t1 t2 T1 T2) "t1" = some (.u32 T1) := by
  simp [compEnv2, compEnv1, envExtend, mkCompressEnv, envLookup,
    show ("t1" : String) ≠ "t2" by decide]

theorem compEnv2_t2 (s vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 T1 T2 : BitVec 32) :
    envLookup (compEnv2 s vv r w t1 t2 T1 T2) "t2" = some (.u32 T2) := by
  simp [compEnv2, envExtend, envLookup]

theorem compEnv2_update_v (s vv vv' : List (BitVec 32)) (r : Nat)
    (w : List (BitVec 32)) (t1 t2 T1 T2 : BitVec 32) :
    envUpdate (compEnv2 s vv r w t1 t2 T1 T2) "v" (.arr32 vv') =
      some (compEnv2 s vv' r w t1 t2 T1 T2) := by
  simp [compEnv2, envExtend, compEnv1, mkCompressEnv, envUpdate,
    show ("v" : String) ≠ "t2" by decide,
    show ("v" : String) ≠ "t1" by decide,
    show ("v" : String) ≠ "r" by decide,
    show ("v" : String) ≠ "K" by decide,
    show ("v" : String) ≠ "i" by decide]

/-- One `v`-cell write in a post-`let` (shadow) env (literal index,
    value already evaluated; mirrors `compressArrSet`). -/
theorem compEnv2ArrSet (F : Nat) (s : List (BitVec 32))
    (vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 T1 T2 : BitVec 32)
    (t : Nat) (ve : CExpr) (v : BitVec 32)
    (ht : t < vv.length) (ht64 : t < 2 ^ 64)
    (hv : evalExpr ve (compEnv2 s vv r w t1 t2 T1 T2) = .ok (.u32 v)) :
    evalStmtFuel F (.arrSet "v" (atU64 t) ve)
        (compEnv2 s vv r w t1 t2 T1 T2) =
      .ok (compEnv2 s (vv.set t v) r w t1 t2 T1 T2, .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 t).toNat = t := ofNat64_toNat t ht64
  have hi : evalExpr (atU64 t) (compEnv2 s vv r w t1 t2 T1 T2) =
      .ok (.u64 (BitVec.ofNat 64 t)) := by
    simp [atU64, evalExpr, litVal]
  have harr := compEnv2_v s vv r w t1 t2 T1 T2
  have hget : vv[(BitVec.ofNat 64 t).toNat]? = some vv[t] := by
    rw [htoNat]; exact List.getElem?_eq_getElem ht
  have hu : envUpdate (compEnv2 s vv r w t1 t2 T1 T2) "v"
      (.arr32 (vv.set (BitVec.ofNat 64 t).toNat v)) =
      some (compEnv2 s (vv.set t v) r w t1 t2 T1 T2) := by
    rw [htoNat]; exact compEnv2_update_v s vv (vv.set t v) r w t1 t2 T1 T2
  exact evalStmtFuel_arrSet F "v" (atU64 t) ve _ _ v vv vv[t] _ hi hv harr
    hget hu

/-- One `st`-cell write in an add env. -/
theorem shaAddArrSet (F : Nat) (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32)) (ve : CExpr) (x : BitVec 32)
    (hj : j < st.length) (hj64 : j < 2 ^ 64)
    (hv : evalExpr ve (mkShaAddEnv v w j st) = .ok (.u32 x)) :
    evalStmtFuel F (.arrSet "st" (.var "j") ve) (mkShaAddEnv v w j st) =
      .ok (mkShaAddEnv v w j (st.set j x), .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have hjv : evalExpr (.var "j") (mkShaAddEnv v w j st) =
      .ok (.u64 (BitVec.ofNat 64 j)) := by
    simp [evalExpr, mkShaAddEnv_j]
  have harr := mkShaAddEnv_st v w j st
  have hget : st[(BitVec.ofNat 64 j).toNat]? = some st[j] := by
    rw [htoNat]; exact List.getElem?_eq_getElem hj
  have hu : envUpdate (mkShaAddEnv v w j st) "st"
      (.arr32 (st.set (BitVec.ofNat 64 j).toNat x)) =
      some (mkShaAddEnv v w j (st.set j x)) := by
    rw [htoNat]; exact shaAddEnv_update_st v w j st (st.set j x)
  exact evalStmtFuel_arrSet F "st" (.var "j") ve _ _ x st st[j] _ hjv hv
    harr hget hu

/-! ### Loop-body evaluation -/

/-- One block-copy iteration: `w[t] = st[8+t]; t++` (any fuel: both
    steps are loop-free). -/
theorem initBody_eval (F : Nat) (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32))
    (ht16 : t < 16) (hs : 24 ≤ s.length) (hw : w.length = 64)
    (ht64 : t < 2 ^ 64) :
    evalStmtFuel F initBody (mkInitEnv s t w) =
      .ok (mkInitEnv s (t + 1) (w.set t s[8 + t]), .fellThrough) := by
  have hidx : evalExpr
      (.uadd (.lit (.u64 (BitVec.ofNat 64 8))) (.var "t"))
      (mkInitEnv s t w) = .ok (.u64 (BitVec.ofNat 64 (8 + t))) := by
    simp only [evalExpr, mkInitEnv_t, litVal, ofNat64_add 8 t (by omega)]
  have htoNat : (BitVec.ofNat 64 (8 + t)).toNat = 8 + t :=
    ofNat64_toNat _ (by omega)
  have hget : s[8 + t]? = some s[8 + t] :=
    List.getElem?_eq_getElem (by omega)
  have hv : evalExpr
      (.idxu "st" (.uadd (.lit (.u64 (BitVec.ofNat 64 8))) (.var "t")))
      (mkInitEnv s t w) = .ok (.u32 s[8 + t]) := by
    simp only [evalExpr, mkInitEnv_st, mkInitEnv_t, litVal, ofNat64_add 8 t (by omega), htoNat, hget]
  have harr := initArrSet F s t w _ _ (by omega) ht64 hv
  have huaddt : evalExpr (.uadd (.var "t") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkInitEnv s t (w.set t s[8 + t])) =
      .ok (.u64 (BitVec.ofNat 64 (t + 1))) := by
    simp only [evalExpr, mkInitEnv_t, litVal, ofNat64_add_one]
  have hupdt : envUpdate (mkInitEnv s t (w.set t s[8 + t])) "t"
      (.u64 (BitVec.ofNat 64 (t + 1))) =
      some (mkInitEnv s (t + 1) (w.set t s[8 + t])) :=
    initEnv_update_t s t (t + 1) (w.set t s[8 + t])
  have hassign := evalStmtFuel_assign F "t" _ _ _ _ huaddt hupdt
  rw [initBody, evalStmtFuel_seq_fallthrough F _ _ _ _ harr, hassign]

/-- One work-init iteration: `v[i] = st[i]; i++` (any fuel). -/
theorem vinitBody_eval (F : Nat) (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32))
    (hi8 : i < 8) (hs : 24 ≤ s.length) (hvlen : v.length = 8)
    (hi64 : i < 2 ^ 64) :
    evalStmtFuel F vinitBody (mkVinitEnv s i v w) =
      .ok (mkVinitEnv s (i + 1) (v.set i s[i]) w, .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat i hi64
  have hget : s[i]? = some s[i] := List.getElem?_eq_getElem (by omega)
  have hiv : evalExpr (.var "i") (mkVinitEnv s i v w) =
      .ok (.u64 (BitVec.ofNat 64 i)) := by
    simp [evalExpr, mkVinitEnv_i]
  have hv : evalExpr (.idxu "st" (.var "i")) (mkVinitEnv s i v w) =
      .ok (.u32 s[i]) := by
    simp only [evalExpr, mkVinitEnv_st, mkVinitEnv_i, htoNat, hget]
  have harr := vinitArrSet F s i v w _ _ (by omega) hi64 hv
  have huaddi : evalExpr (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkVinitEnv s i (v.set i s[i]) w) =
      .ok (.u64 (BitVec.ofNat 64 (i + 1))) := by
    simp only [evalExpr, mkVinitEnv_i, litVal, ofNat64_add_one]
  have hupdi : envUpdate (mkVinitEnv s i (v.set i s[i]) w) "i"
      (.u64 (BitVec.ofNat 64 (i + 1))) =
      some (mkVinitEnv s (i + 1) (v.set i s[i]) w) :=
    vinitEnv_update_i s i (i + 1) (v.set i s[i]) w
  have hassign := evalStmtFuel_assign F "i" _ _ _ _ huaddi hupdi
  rw [vinitBody, evalStmtFuel_seq_fallthrough F _ _ _ _ harr, hassign]

/-- One schedule iteration: `w[u] = ...; u++` (any fuel). The four
    reads ground the `usub` indices via `ofNat64_sub`; the six
    rotates go through `rotrE_eval`; the shifts are direct K1
    applications (mirroring `rotlAt_eval`'s `e1`). -/
theorem schedBody_eval (F : Nat) (s : List (BitVec 32)) (u : Nat)
    (w : List (BitVec 32))
    (hu16 : 16 ≤ u) (hu64b : u < 64) (hw : w.length = 64)
    (hu64 : u < 2 ^ 64) :
    evalStmtFuel F schedBody (mkSchedEnv s u w) =
      .ok (mkSchedEnv s (u + 1)
        (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2])),
        .fellThrough) := by
  have huv : evalExpr (.var "u") (mkSchedEnv s u w) =
      .ok (.u64 (BitVec.ofNat 64 u)) := by
    simp [evalExpr, mkSchedEnv_u]
  have hiu16 : evalExpr (.usub (.var "u") (.lit (.u64 (BitVec.ofNat 64 16))))
      (mkSchedEnv s u w) = .ok (.u64 (BitVec.ofNat 64 (u - 16))) := by
    simp only [evalExpr, mkSchedEnv_u, litVal, ofNat64_sub u 16 (by omega) hu64]
  have hiu15 : evalExpr (.usub (.var "u") (.lit (.u64 (BitVec.ofNat 64 15))))
      (mkSchedEnv s u w) = .ok (.u64 (BitVec.ofNat 64 (u - 15))) := by
    simp only [evalExpr, mkSchedEnv_u, litVal, ofNat64_sub u 15 (by omega) hu64]
  have hiu7 : evalExpr (.usub (.var "u") (.lit (.u64 (BitVec.ofNat 64 7))))
      (mkSchedEnv s u w) = .ok (.u64 (BitVec.ofNat 64 (u - 7))) := by
    simp only [evalExpr, mkSchedEnv_u, litVal, ofNat64_sub u 7 (by omega) hu64]
  have hiu2 : evalExpr (.usub (.var "u") (.lit (.u64 (BitVec.ofNat 64 2))))
      (mkSchedEnv s u w) = .ok (.u64 (BitVec.ofNat 64 (u - 2))) := by
    simp only [evalExpr, mkSchedEnv_u, litVal, ofNat64_sub u 2 (by omega) hu64]
  have ht16 : (BitVec.ofNat 64 (u - 16)).toNat = u - 16 :=
    ofNat64_toNat _ (by omega)
  have ht15 : (BitVec.ofNat 64 (u - 15)).toNat = u - 15 :=
    ofNat64_toNat _ (by omega)
  have ht7 : (BitVec.ofNat 64 (u - 7)).toNat = u - 7 :=
    ofNat64_toNat _ (by omega)
  have ht2 : (BitVec.ofNat 64 (u - 2)).toNat = u - 2 :=
    ofNat64_toNat _ (by omega)
  have hgA : w[u - 16]? = some w[u - 16] :=
    List.getElem?_eq_getElem (by omega)
  have hgB : w[u - 15]? = some w[u - 15] :=
    List.getElem?_eq_getElem (by omega)
  have hgC : w[u - 7]? = some w[u - 7] :=
    List.getElem?_eq_getElem (by omega)
  have hgD : w[u - 2]? = some w[u - 2] :=
    List.getElem?_eq_getElem (by omega)
  have hA : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 16))))) (mkSchedEnv s u w) =
      .ok (.u32 w[u - 16]) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 16 (by omega) hu64, ht16, hgA]
  have hB : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15))))) (mkSchedEnv s u w) =
      .ok (.u32 w[u - 15]) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 15 (by omega) hu64, ht15, hgB]
  have hC : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 7))))) (mkSchedEnv s u w) =
      .ok (.u32 w[u - 7]) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 7 (by omega) hu64, ht7, hgC]
  have hD : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 2))))) (mkSchedEnv s u w) =
      .ok (.u32 w[u - 2]) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 2 (by omega) hu64, ht2, hgD]
  have hr7 : evalExpr (rotrE (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15))))) 7) (mkSchedEnv s u w) =
      .ok (.u32 (rotrU32 w[u - 15] 7)) :=
    rotrE_eval _ _ _ 7 hB (ofNat32_toNat 7 (by decide))
      (ofNat32_toNat (32 - 7) (by decide)) (by decide) (by decide)
  have hr18 : evalExpr (rotrE (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15))))) 18) (mkSchedEnv s u w) =
      .ok (.u32 (rotrU32 w[u - 15] 18)) :=
    rotrE_eval _ _ _ 18 hB (ofNat32_toNat 18 (by decide))
      (ofNat32_toNat (32 - 18) (by decide)) (by decide) (by decide)
  have hs3 : evalExpr (.bshr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15)))))
      (.lit (.u32 (BitVec.ofNat 32 3)))) (mkSchedEnv s u w) =
      .ok (.u32 (w[u - 15] >>> 3)) := by
    have h := checkedShiftU32_ok w[u - 15] (BitVec.ofNat 32 3) (· >>> ·)
      (by rw [ofNat32_toNat 3 (by decide)]; decide)
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 15 (by omega) hu64, ht15, hgB]
    rw [h]
    exact u32_map_ok _
  have hr17 : evalExpr (rotrE (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 2))))) 17) (mkSchedEnv s u w) =
      .ok (.u32 (rotrU32 w[u - 2] 17)) :=
    rotrE_eval _ _ _ 17 hD (ofNat32_toNat 17 (by decide))
      (ofNat32_toNat (32 - 17) (by decide)) (by decide) (by decide)
  have hr19 : evalExpr (rotrE (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 2))))) 19) (mkSchedEnv s u w) =
      .ok (.u32 (rotrU32 w[u - 2] 19)) :=
    rotrE_eval _ _ _ 19 hD (ofNat32_toNat 19 (by decide))
      (ofNat32_toNat (32 - 19) (by decide)) (by decide) (by decide)
  have hs10 : evalExpr (.bshr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 2)))))
      (.lit (.u32 (BitVec.ofNat 32 10)))) (mkSchedEnv s u w) =
      .ok (.u32 (w[u - 2] >>> 10)) := by
    have h := checkedShiftU32_ok w[u - 2] (BitVec.ofNat 32 10) (· >>> ·)
      (by rw [ofNat32_toNat 10 (by decide)]; decide)
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 2 (by omega) hu64, ht2, hgD]
    rw [h]
    exact u32_map_ok _
  have hv : evalExpr
      (.uadd
        (.uadd
          (.uadd (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 16)))))
            (.bxor
              (.bxor (rotrE (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 15))))) 7)
                (rotrE (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 15))))) 18))
              (.bshr (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 15)))))
                (.lit (.u32 (BitVec.ofNat 32 3))))))
          (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 7))))))
        (.bxor
          (.bxor (rotrE (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 2))))) 17)
            (rotrE (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 2))))) 19))
          (.bshr (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 2)))))
            (.lit (.u32 (BitVec.ofNat 32 10))))))
      (mkSchedEnv s u w) =
      .ok (.u32 (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2])) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal,
      ofNat64_sub u 16 (by omega) hu64, ofNat64_sub u 15 (by omega) hu64,
      ofNat64_sub u 7 (by omega) hu64, ofNat64_sub u 2 (by omega) hu64,
      ht16, ht15, ht7, ht2, hgA, hgB, hgC, hgD,
      hr7, hr18, hr17, hr19,
      checkedShiftU32_ok w[u - 15] (BitVec.ofNat 32 3) (· >>> ·)
        (by rw [ofNat32_toNat 3 (by decide)]; decide),
      checkedShiftU32_ok w[u - 2] (BitVec.ofNat 32 10) (· >>> ·)
        (by rw [ofNat32_toNat 10 (by decide)]; decide),
      ofNat32_toNat 3 (by decide), ofNat32_toNat 10 (by decide),
      Except.map,
      sV1, sV2, sV3, sV4, sV5, sV6, sV7, sV8, sV9, sV10, sV11]
  have harr := schedArrSet F s u w _ _ (by omega) hu64 hv
  have huaddu : evalExpr (.uadd (.var "u") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkSchedEnv s u (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2]))) =
      .ok (.u64 (BitVec.ofNat 64 (u + 1))) := by
    simp only [evalExpr, mkSchedEnv_u, litVal, ofNat64_add_one]
  have hupdu : envUpdate
      (mkSchedEnv s u (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2])))
      "u" (.u64 (BitVec.ofNat 64 (u + 1))) =
      some (mkSchedEnv s (u + 1)
        (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2]))) :=
    schedEnv_update_u s u (u + 1)
      (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2]))
  have hassign := evalStmtFuel_assign F "u" _ _ _ _ huaddu hupdu
  rw [schedBody, evalStmtFuel_seq_fallthrough F _ _ _ _ harr, hassign]

/-- One add-back iteration: `st[j] += v[j]; j++` (any fuel: both
    steps are loop-free). -/
theorem shaAddBody_eval (F : Nat) (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32))
    (hj8 : j < 8) (hst : 8 ≤ st.length) (hvlen : v.length = 8)
    (hj64 : j < 2 ^ 64) :
    evalStmtFuel F shaAddBody (mkShaAddEnv v w j st) =
      .ok (mkShaAddEnv v w (j + 1) (st.set j (st[j] + v[j])),
        .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have hget : st[j]? = some st[j] := List.getElem?_eq_getElem (by omega)
  have hgetv : v[j]? = some v[j] := List.getElem?_eq_getElem (by omega)
  have hv : evalExpr (.uadd (.idxu "st" (.var "j")) (.idxu "v" (.var "j")))
      (mkShaAddEnv v w j st) = .ok (.u32 (st[j] + v[j])) := by
    simp only [evalExpr, mkShaAddEnv_st, mkShaAddEnv_v, mkShaAddEnv_j,
      htoNat, hget, hgetv]
  have harr := shaAddArrSet F v w j st _ _ (by omega) hj64 hv
  have huaddj : evalExpr (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkShaAddEnv v w j (st.set j (st[j] + v[j]))) =
      .ok (.u64 (BitVec.ofNat 64 (j + 1))) := by
    simp only [evalExpr, mkShaAddEnv_j, litVal, ofNat64_add_one]
  have hupdj : envUpdate (mkShaAddEnv v w j (st.set j (st[j] + v[j]))) "j"
      (.u64 (BitVec.ofNat 64 (j + 1))) =
      some (mkShaAddEnv v w (j + 1) (st.set j (st[j] + v[j]))) :=
    shaAddEnv_update_j v w j (j + 1) (st.set j (st[j] + v[j]))
  have hassign := evalStmtFuel_assign F "j" _ _ _ _ huaddj hupdj
  rw [shaAddBody, evalStmtFuel_seq_fallthrough F _ _ _ _ harr, hassign]

-- Giant single-fragment bridge below (temps plus eight stores plus
-- extensionality reassembly): raise the heartbeat budget as in K4.
set_option maxHeartbeats 1000000
/-- One compression round evaluates to `roundStep` (any fuel:
    loop-free). `t1`/`t2` evaluate once over pristine reads; the
    eight stores chain through `compressArrSet`; the eval-order chain
    is `roundStep` by extensionality (same positions — the `cons8`
    shaping puts `vv` in constructor form for the `roundStep`
    match). -/
theorem compressFrag_eval (F : Nat) (s : List (BitVec 32))
    (vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 : BitVec 32)
    (hv8 : vv.length = 8) (hw64 : w.length = 64)
    (hr64 : r < 64) (hr642 : r < 2 ^ 64) :
    evalStmtFuel F compressFrag (mkCompressEnv s vv r w t1 t2) =
      .ok (compEnv2 s (roundStep vv w r) r w t1 t2
        (cV6 vv[0] vv[1] vv[2] vv[3] vv[4] vv[5] vv[6] vv[7] w[r] shaK[r])
        (cV12 vv[0] vv[1] vv[2] vv[3] vv[4] vv[5] vv[6] vv[7] w[r] shaK[r]),
        .fellThrough) := by
  obtain ⟨A, B, C, D, E, Ff, G, H, rfl⟩ :
      ∃ A B C D E Ff G H, vv = [A, B, C, D, E, Ff, G, H] := by
    exact ⟨vv[0], vv[1], vv[2], vv[3], vv[4], vv[5], vv[6], vv[7],
      cons8 vv hv8⟩
  -- Normalize the conclusion's `([A..H])[k]` projections (definitional).
  show evalStmtFuel F compressFrag (mkCompressEnv s [A, B, C, D, E, Ff, G, H]
      r w t1 t2) =
    .ok (compEnv2 s (roundStep [A, B, C, D, E, Ff, G, H] w r) r w t1 t2
      (cV6 A B C D E Ff G H w[r] shaK[r])
      (cV12 A B C D E Ff G H w[r] shaK[r]), .fellThrough)
  have htoNat0 : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by decide)
  have htoNat1 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have htoNat2 : (BitVec.ofNat 64 2).toNat = 2 := ofNat64_toNat 2 (by decide)
  have htoNat3 : (BitVec.ofNat 64 3).toNat = 3 := ofNat64_toNat 3 (by decide)
  have htoNat4 : (BitVec.ofNat 64 4).toNat = 4 := ofNat64_toNat 4 (by decide)
  have htoNat5 : (BitVec.ofNat 64 5).toNat = 5 := ofNat64_toNat 5 (by decide)
  have htoNat6 : (BitVec.ofNat 64 6).toNat = 6 := ofNat64_toNat 6 (by decide)
  have htoNat7 : (BitVec.ofNat 64 7).toNat = 7 := ofNat64_toNat 7 (by decide)
  have hgetw : w[r]? = some w[r] :=
    List.getElem?_eq_getElem (by omega)
  have hgetk : shaK[r]? = some shaK[r] := by
    have := shaK_length
    exact List.getElem?_eq_getElem (by omega)
  have hEv := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
  have hEw := mkCompressEnv_w s [A, B, C, D, E, Ff, G, H] r w t1 t2
  have hEk := mkCompressEnv_K s [A, B, C, D, E, Ff, G, H] r w t1 t2
  have hEr := mkCompressEnv_r s [A, B, C, D, E, Ff, G, H] r w t1 t2
  have htoNatrE : (BitVec.ofNat 64 r).toNat = r := ofNat64_toNat r hr642
  have hg4 : ([A, B, C, D, E, Ff, G, H])[4]? = some E := by simp
  have hg5 : ([A, B, C, D, E, Ff, G, H])[5]? = some Ff := by simp
  have hg6 : ([A, B, C, D, E, Ff, G, H])[6]? = some G := by simp
  have hg7 : ([A, B, C, D, E, Ff, G, H])[7]? = some H := by simp
  have hE4lit : evalExpr (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4))))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 E) := by
    simp only [evalExpr, litVal, hEv, htoNat4, hg4]
  have hc6lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4)))) 6)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 E 6)) := by
    exact rotrE_eval _ _ _ 6 hE4lit (ofNat32_toNat 6 (by decide))
      (ofNat32_toNat (32 - 6) (by decide)) (by decide) (by decide)
  have hc11lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4)))) 11)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 E 11)) := by
    exact rotrE_eval _ _ _ 11 hE4lit (ofNat32_toNat 11 (by decide))
      (ofNat32_toNat (32 - 11) (by decide)) (by decide) (by decide)
  have hc25lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4)))) 25)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 E 25)) := by
    exact rotrE_eval _ _ _ 25 hE4lit (ofNat32_toNat 25 (by decide))
      (ofNat32_toNat (32 - 25) (by decide)) (by decide) (by decide)
  -- Reads and rotates, uniform over the temp params (nothing here
  -- depends on `t1`/`t2`, so each fact is proved once and used in
  -- both the entry env and the post-`t1` env).
  have hA : ∀ t1 t2, evalExpr (.idxu "v" (atU64 0))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 A) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat0]
    simp
  have hB : ∀ t1 t2, evalExpr (.idxu "v" (atU64 1))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 B) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat1]
    simp
  have hC : ∀ t1 t2, evalExpr (.idxu "v" (atU64 2))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 C) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat2]
    simp
  have hD : ∀ t1 t2, evalExpr (.idxu "v" (atU64 3))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 D) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat3]
    simp
  have hE : ∀ t1 t2, evalExpr (.idxu "v" (atU64 4))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 E) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat4]
    simp
  have hF : ∀ t1 t2, evalExpr (.idxu "v" (atU64 5))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 Ff) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat5]
    simp
  have hG : ∀ t1 t2, evalExpr (.idxu "v" (atU64 6))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 G) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat6]
    simp
  have hH : ∀ t1 t2, evalExpr (.idxu "v" (atU64 7))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 H) := by
    intro t1 t2
    have hx := mkCompressEnv_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, litVal, atU64, hx, htoNat7]
    simp
  have hWT : ∀ t1 t2, evalExpr (.idxu "w" (.var "r"))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 w[r]) := by
    intro t1 t2
    have hrv : evalExpr (.var "r")
        (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
        .ok (.u64 (BitVec.ofNat 64 r)) := by
      simp [evalExpr, mkCompressEnv_r]
    have htoNatr : (BitVec.ofNat 64 r).toNat = r := ofNat64_toNat r hr642
    have hw := mkCompressEnv_w s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, hw, mkCompressEnv_r, htoNatr, hgetw]
  have hKK : ∀ t1 t2, evalExpr (.idxu "K" (.var "r"))
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 shaK[r]) := by
    intro t1 t2
    have hrv : evalExpr (.var "r")
        (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
        .ok (.u64 (BitVec.ofNat 64 r)) := by
      simp [evalExpr, mkCompressEnv_r]
    have htoNatr : (BitVec.ofNat 64 r).toNat = r := ofNat64_toNat r hr642
    have hk := mkCompressEnv_K s [A, B, C, D, E, Ff, G, H] r w t1 t2
    simp only [evalExpr, hk, mkCompressEnv_r, htoNatr, hgetk]
  have hc6 : ∀ t1 t2, evalExpr (rotrE (.idxu "v" (atU64 4)) 6)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 E 6)) := by
    intro t1 t2
    exact rotrE_eval _ _ _ 6 (hE t1 t2) (ofNat32_toNat 6 (by decide))
      (ofNat32_toNat (32 - 6) (by decide)) (by decide) (by decide)
  have hc11 : ∀ t1 t2, evalExpr (rotrE (.idxu "v" (atU64 4)) 11)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 E 11)) := by
    intro t1 t2
    exact rotrE_eval _ _ _ 11 (hE t1 t2) (ofNat32_toNat 11 (by decide))
      (ofNat32_toNat (32 - 11) (by decide)) (by decide) (by decide)
  have hc25 : ∀ t1 t2, evalExpr (rotrE (.idxu "v" (atU64 4)) 25)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 E 25)) := by
    intro t1 t2
    exact rotrE_eval _ _ _ 25 (hE t1 t2) (ofNat32_toNat 25 (by decide))
      (ofNat32_toNat (32 - 25) (by decide)) (by decide) (by decide)
  have hc2 : ∀ t1 t2, evalExpr (rotrE (.idxu "v" (atU64 0)) 2)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 A 2)) := by
    intro t1 t2
    exact rotrE_eval _ _ _ 2 (hA t1 t2) (ofNat32_toNat 2 (by decide))
      (ofNat32_toNat (32 - 2) (by decide)) (by decide) (by decide)
  have hc13 : ∀ t1 t2, evalExpr (rotrE (.idxu "v" (atU64 0)) 13)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 A 13)) := by
    intro t1 t2
    exact rotrE_eval _ _ _ 13 (hA t1 t2) (ofNat32_toNat 13 (by decide))
      (ofNat32_toNat (32 - 13) (by decide)) (by decide) (by decide)
  have hc22 : ∀ t1 t2, evalExpr (rotrE (.idxu "v" (atU64 0)) 22)
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (rotrU32 A 22)) := by
    intro t1 t2
    exact rotrE_eval _ _ _ 22 (hA t1 t2) (ofNat32_toNat 22 (by decide))
      (ofNat32_toNat (32 - 22) (by decide)) (by decide) (by decide)
  have hT1 : evalExpr t1Expr
      (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2) =
      .ok (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) := by
    simp only [t1Expr, evalExpr, hEv, hEw, hEk, hEr, atU64, litVal,
      htoNat4, htoNat5, htoNat6, htoNat7, htoNatrE, hgetw, hgetk,
      hg4, hg5, hg6, hg7,
      hc6lit, hc11lit, hc25lit, cV1, cV2, cV3, cV4, cV5, cV6]
  have hletT1 := evalStmtFuel_let_ F "t1" (.u 32) t1Expr
    (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2)
    (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) hT1
  have henvT1 : envExtend (mkCompressEnv s [A, B, C, D, E, Ff, G, H] r w t1 t2)
      "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) =
      compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r]) := rfl
  have hE1v := compEnv1_v s [A, B, C, D, E, Ff, G, H] r w t1 t2
    (cV6 A B C D E Ff G H w[r] shaK[r])
  have hgetv0 : ([A, B, C, D, E, Ff, G, H])[0]? = some A := by simp
  have hgetv1 : ([A, B, C, D, E, Ff, G, H])[1]? = some B := by simp
  have hgetv2 : ([A, B, C, D, E, Ff, G, H])[2]? = some C := by simp
  have hA0lit : evalExpr (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0))))
      (compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r])) = .ok (.u32 A) := by
    simp only [evalExpr, litVal, hE1v, htoNat0, hgetv0]
  have hc2lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0)))) 2)
      (compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 (rotrU32 A 2)) := by
    exact rotrE_eval _ _ _ 2 hA0lit (ofNat32_toNat 2 (by decide))
      (ofNat32_toNat (32 - 2) (by decide)) (by decide) (by decide)
  have hc13lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0)))) 13)
      (compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 (rotrU32 A 13)) := by
    exact rotrE_eval _ _ _ 13 hA0lit (ofNat32_toNat 13 (by decide))
      (ofNat32_toNat (32 - 13) (by decide)) (by decide) (by decide)
  have hc22lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0)))) 22)
      (compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 (rotrU32 A 22)) := by
    exact rotrE_eval _ _ _ 22 hA0lit (ofNat32_toNat 22 (by decide))
      (ofNat32_toNat (32 - 22) (by decide)) (by decide) (by decide)
  have hT2 : evalExpr t2Expr
      (compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) := by
    simp only [t2Expr, evalExpr, hE1v, atU64, litVal,
      htoNat0, htoNat1, htoNat2, hgetv0, hgetv1, hgetv2,
      hc2lit, hc13lit, hc22lit, cV7, cV8, cV9, cV10, cV11, cV12]
  have hletT2 := evalStmtFuel_let_ F "t2" (.u 32) t2Expr
    (compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
      (cV6 A B C D E Ff G H w[r] shaK[r]))
    (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) hT2
  have henvT2 : envExtend
      (compEnv1 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r]))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) =
      compEnv2 s [A, B, C, D, E, Ff, G, H] r w t1 t2
        (cV6 A B C D E Ff G H w[r] shaK[r])
        (cV12 A B C D E Ff G H w[r] shaK[r]) := rfl
  have hxT := compEnv2_v s [A, B, C, D, E, Ff, G, H] r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
  have ht1v : evalExpr (.var "t1")
      (compEnv2 s [A, B, C, D, E, Ff, G, H] r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) := by
    simp [evalExpr, compEnv2_t1]
  have ht2v : evalExpr (.var "t2")
      (compEnv2 s [A, B, C, D, E, Ff, G, H] r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) := by
    simp [evalExpr, compEnv2_t2]
  have hv76 : evalExpr (.idxu "v" (atU64 6))
      (compEnv2 s [A, B, C, D, E, Ff, G, H] r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 G) := by
    simp only [evalExpr, litVal, atU64, hxT, htoNat6]
    simp
  have e1 := compEnv2ArrSet F s [A, B, C, D, E, Ff, G, H] r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r]) 7 _ _
    (by simp) (by decide) hv76
  have hv65 : evalExpr (.idxu "v" (atU64 5))
      (compEnv2 s ([A, B, C, D, E, Ff, G, H].set 7 G) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 Ff) := by
    have hx1 := compEnv2_v s ([A, B, C, D, E, Ff, G, H].set 7 G) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    have hg : (([A, B, C, D, E, Ff, G, H].set 7 G)[5]? = some Ff) := by simp
    simp only [evalExpr, litVal, atU64, hx1, htoNat5, hg]
  have e2 := compEnv2ArrSet F s ([A, B, C, D, E, Ff, G, H].set 7 G) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    6 _ _ (by simp) (by decide) hv65
  have hv54 : evalExpr (.idxu "v" (atU64 4))
      (compEnv2 s (([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff) r w
        t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) = .ok (.u32 E) := by
    have hx2 := compEnv2_v s
      (([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    have hg : ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff)[4]? =
      some E) := by simp
    simp only [evalExpr, litVal, atU64, hx2, htoNat4, hg]
  have e3 := compEnv2ArrSet F s
    (([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r]) 5 _ _
    (by simp) (by decide) hv54
  have hvD : evalExpr (.idxu "v" (atU64 3))
      (compEnv2 s
        ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E) r w
        t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) = .ok (.u32 D) := by
    have hx3 := compEnv2_v s
      ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    have hg : (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E)[3]? =
      some D) := by simp
    simp only [evalExpr, litVal, atU64, hx3, htoNat3, hg]
  have hx3d := compEnv2_v s
      ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
  have hgd : (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E)[3]? =
      some D) := by simp
  have hvT1D : evalExpr (.uadd (.idxu "v" (atU64 3)) (.var "t1"))
      (compEnv2 s
        ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E) r w
        t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) = .ok (.u32 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))) := by
    have ht1x := compEnv2_t1 s
      ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    simp only [evalExpr, litVal, atU64, hx3d, htoNat3, hgd, ht1x]
  have e4 := compEnv2ArrSet F s
    ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r]) 4 _ _
    (by simp) (by decide) hvT1D
  have hvC : evalExpr (.idxu "v" (atU64 2))
      (compEnv2 s
        (((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
          5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) = .ok (.u32 C) := by
    have hx4 := compEnv2_v s
      (((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    have hg : ((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set
      6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r])))[2]? = some C) := by simp
    simp only [evalExpr, litVal, atU64, hx4, htoNat2, hg]
  have e5 := compEnv2ArrSet F s
    (((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
      5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r]) 3 _ _
    (by simp) (by decide) hvC
  have hvB : evalExpr (.idxu "v" (atU64 1))
      (compEnv2 s
        ((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
          5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) = .ok (.u32 B) := by
    have hx5 := compEnv2_v s
      ((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    have hg : (((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set
      6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C)[1]? = some B) := by simp
    simp only [evalExpr, litVal, atU64, hx5, htoNat1, hg]
  have e6 := compEnv2ArrSet F s
    ((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
      5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r]) 2 _ _
    (by simp) (by decide) hvB
  have hvA : evalExpr (.idxu "v" (atU64 0))
      (compEnv2 s
        (((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
          5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) =
      .ok (.u32 A) := by
    have hx6 := compEnv2_v s
      (((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    have hg : ((((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set
      6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B)[0]? = some A) := by
      simp
    simp only [evalExpr, litVal, atU64, hx6, htoNat0, hg]
  have e7 := compEnv2ArrSet F s
    (((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
      5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r]) 1 _ _
    (by simp) (by decide) hvA
  have hvT : evalExpr (.uadd (.var "t1") (.var "t2"))
      (compEnv2 s
        ((((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set
          6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A) r w
        t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])) = .ok (.u32 ((cV6 A B C D E Ff G H w[r] shaK[r]) + (cV12 A B C D E Ff G H w[r] shaK[r]))) := by
    have ht1y := compEnv2_t1 s
      ((((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set
        6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    have ht2y := compEnv2_t2 s
      ((((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set
        6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    simp only [evalExpr, ht1y, ht2y]
  have e8 := compEnv2ArrSet F s
    ((((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set
      6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A) r w t1 t2 (cV6 A B C D E Ff G H w[r] shaK[r]) (cV12 A B C D E Ff G H w[r] shaK[r])
    0 _ _ (by simp) (by decide) hvT
  -- The eval-order chain is `roundStep`: same eight positions, so
  -- extensionality plus an `omega` case split (the eight live cases
  -- evaluate both chains by `simp`; the rest contradict lengths).
  have hbridge :
      (((((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A).set 0 ((cV6 A B C D E Ff G H w[r] shaK[r]) + (cV12 A B C D E Ff G H w[r] shaK[r]))) =
      roundStep [A, B, C, D, E, Ff, G, H] w r := by
    have hrr : roundStep [A, B, C, D, E, Ff, G, H] w r =
        [(cV6 A B C D E Ff G H w[r] shaK[r]) + (cV12 A B C D E Ff G H w[r] shaK[r]), A, B, C, D + (cV6 A B C D E Ff G H w[r] shaK[r]), E, Ff, G] := by
      simp only [roundStep, hgetw, hgetk, shaS1, shaCh, shaS0, shaMaj,
        cV1, cV2, cV3, cV4, cV5, cV6, cV7, cV8, cV9, cV10, cV11, cV12]
    rw [hrr]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 8
    · have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
          i = 7 := by omega
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hc <;> simp
    · rw [List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by simp; omega)]
  rw [compressFrag,
    evalStmtFuel_seq_fallthrough F _ _ _ _ hletT1, henvT1,
    evalStmtFuel_seq_fallthrough F _ _ _ _ hletT2, henvT2,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e1,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e2,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e3,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e4,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e5,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e6,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e7,
    e8, hbridge]

/-- Frame preservation across a `v`-cell update: only the `v` lookup
    changes. Bundles six `envLookup_envUpdate_diff` applications so
    each of the eight round stores costs one line. -/
theorem compressFrame_update (ρ ρ' : Env) (new : Value)
    (hu : envUpdate ρ "v" new = some ρ') :
    envLookup ρ' "r" = envLookup ρ "r" ∧
    envLookup ρ' "w" = envLookup ρ "w" ∧
    envLookup ρ' "K" = envLookup ρ "K" ∧
    envLookup ρ' "st" = envLookup ρ "st" ∧
    envLookup ρ' "t1" = envLookup ρ "t1" ∧
    envLookup ρ' "t2" = envLookup ρ "t2" := by
  exact ⟨envLookup_envUpdate_diff _ _ _ _ _ hu (by decide),
    envLookup_envUpdate_diff _ _ _ _ _ hu (by decide),
    envLookup_envUpdate_diff _ _ _ _ _ hu (by decide),
    envLookup_envUpdate_diff _ _ _ _ _ hu (by decide),
    envLookup_envUpdate_diff _ _ _ _ _ hu (by decide),
    envLookup_envUpdate_diff _ _ _ _ _ hu (by decide)⟩

/-- One `v`-cell write over an abstract env: the update equation is an
    explicit hypothesis (existential post-envs never match literal
    shapes). Mirrors `compEnv2ArrSet`. -/
theorem transferArrSet (F : Nat) (ρ ρ' : Env) (CUR : List (BitVec 32))
    (t : Nat) (ve : CExpr) (VAL : BitVec 32)
    (ht : t < CUR.length)
    (hv : evalExpr ve ρ = .ok (.u32 VAL))
    (hcur : envLookup ρ "v" = some (.arr32 CUR))
    (hget : CUR[(BitVec.ofNat 64 t).toNat]? = some CUR[t])
    (hu : envUpdate ρ "v" (.arr32 (CUR.set (BitVec.ofNat 64 t).toNat VAL)) =
      some ρ') :
    evalStmtFuel F (.arrSet "v" (atU64 t) ve) ρ =
      .ok (ρ', .fellThrough) := by
  have hi : evalExpr (atU64 t) ρ = .ok (.u64 (BitVec.ofNat 64 t)) := by
    simp [atU64, evalExpr, litVal]
  exact evalStmtFuel_arrSet F "v" (atU64 t) ve _ _ VAL CUR CUR[t] _ hi hv
    hcur hget hu

/-- One compression round over an abstract env: evaluation is
    lookup-determined, so the exact-env certificate replays with the
    entry lookups as hypotheses and existential post-envs
    (`envUpdate_some_of_lookup`, ArraySort precedent) for the eight
    stores. The conclusion pins `v` absolutely and frames the rest. -/
theorem compressFrag_transfer (F : Nat) (ρ : Env)
    (vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (hv8 : vv.length = 8) (hw64 : w.length = 64)
    (hr64 : r < 64) (hr642 : r < 2 ^ 64)
    (hρv : envLookup ρ "v" = some (.arr32 vv))
    (hρw : envLookup ρ "w" = some (.arr32 w))
    (hρK : envLookup ρ "K" = some (.arr32 shaK))
    (hρr : envLookup ρ "r" = some (.u64 (BitVec.ofNat 64 r))) :
    ∃ ρ', evalStmtFuel F compressFrag ρ = .ok (ρ', .fellThrough)
      ∧ envLookup ρ' "v" = some (.arr32 (roundStep vv w r))
      ∧ envLookup ρ' "r" = envLookup ρ "r"
      ∧ envLookup ρ' "w" = envLookup ρ "w"
      ∧ envLookup ρ' "K" = envLookup ρ "K"
      ∧ envLookup ρ' "st" = envLookup ρ "st" := by
  obtain ⟨A, B, C, D, E, Ff, G, H, rfl⟩ :
      ∃ A B C D E Ff G H, vv = [A, B, C, D, E, Ff, G, H] := by
    exact ⟨vv[0], vv[1], vv[2], vv[3], vv[4], vv[5], vv[6], vv[7],
      cons8 vv hv8⟩
  have htoNat0 : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by decide)
  have htoNat1 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have htoNat2 : (BitVec.ofNat 64 2).toNat = 2 := ofNat64_toNat 2 (by decide)
  have htoNat3 : (BitVec.ofNat 64 3).toNat = 3 := ofNat64_toNat 3 (by decide)
  have htoNat4 : (BitVec.ofNat 64 4).toNat = 4 := ofNat64_toNat 4 (by decide)
  have htoNat5 : (BitVec.ofNat 64 5).toNat = 5 := ofNat64_toNat 5 (by decide)
  have htoNat6 : (BitVec.ofNat 64 6).toNat = 6 := ofNat64_toNat 6 (by decide)
  have htoNat7 : (BitVec.ofNat 64 7).toNat = 7 := ofNat64_toNat 7 (by decide)
  have hgetw : w[r]? = some w[r] :=
    List.getElem?_eq_getElem (by omega)
  have hgetk : shaK[r]? = some shaK[r] := by
    have := shaK_length
    exact List.getElem?_eq_getElem (by omega)
  have hg4 : ([A, B, C, D, E, Ff, G, H])[4]? = some E := by simp
  have hg5 : ([A, B, C, D, E, Ff, G, H])[5]? = some Ff := by simp
  have hg6 : ([A, B, C, D, E, Ff, G, H])[6]? = some G := by simp
  have hg7 : ([A, B, C, D, E, Ff, G, H])[7]? = some H := by simp
  have hE4lit : evalExpr (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4)))) ρ =
      .ok (.u32 E) := by
    simp only [evalExpr, litVal, hρv, htoNat4, hg4]
  have hc6lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4)))) 6)
      ρ = .ok (.u32 (rotrU32 E 6)) := by
    exact rotrE_eval _ _ _ 6 hE4lit (ofNat32_toNat 6 (by decide))
      (ofNat32_toNat (32 - 6) (by decide)) (by decide) (by decide)
  have hc11lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4)))) 11)
      ρ = .ok (.u32 (rotrU32 E 11)) := by
    exact rotrE_eval _ _ _ 11 hE4lit (ofNat32_toNat 11 (by decide))
      (ofNat32_toNat (32 - 11) (by decide)) (by decide) (by decide)
  have hc25lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 4)))) 25)
      ρ = .ok (.u32 (rotrU32 E 25)) := by
    exact rotrE_eval _ _ _ 25 hE4lit (ofNat32_toNat 25 (by decide))
      (ofNat32_toNat (32 - 25) (by decide)) (by decide) (by decide)
  -- Reads and rotates over the entry env (nothing here depends on the
  -- temp params, so the entry facts feed `t1Expr` directly and the
  -- post-`t1` facts below re-derive the `v` reads via shadowing).
  have htoNatrE : (BitVec.ofNat 64 r).toNat = r := ofNat64_toNat r hr642
  have hA : evalExpr (.idxu "v" (atU64 0)) ρ = .ok (.u32 A) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat0]
    simp
  have hB : evalExpr (.idxu "v" (atU64 1)) ρ = .ok (.u32 B) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat1]
    simp
  have hC : evalExpr (.idxu "v" (atU64 2)) ρ = .ok (.u32 C) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat2]
    simp
  have hD : evalExpr (.idxu "v" (atU64 3)) ρ = .ok (.u32 D) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat3]
    simp
  have hE : evalExpr (.idxu "v" (atU64 4)) ρ = .ok (.u32 E) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat4]
    simp
  have hF : evalExpr (.idxu "v" (atU64 5)) ρ = .ok (.u32 Ff) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat5]
    simp
  have hG : evalExpr (.idxu "v" (atU64 6)) ρ = .ok (.u32 G) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat6]
    simp
  have hH : evalExpr (.idxu "v" (atU64 7)) ρ = .ok (.u32 H) := by
    simp only [evalExpr, litVal, atU64, hρv, htoNat7]
    simp
  have hWT : evalExpr (.idxu "w" (.var "r")) ρ = .ok (.u32 w[r]) := by
    simp only [evalExpr, hρw, hρr, htoNatrE, hgetw]
  have hKK : evalExpr (.idxu "K" (.var "r")) ρ = .ok (.u32 shaK[r]) := by
    simp only [evalExpr, hρK, hρr, htoNatrE, hgetk]
  have hc6 : evalExpr (rotrE (.idxu "v" (atU64 4)) 6) ρ =
      .ok (.u32 (rotrU32 E 6)) :=
    rotrE_eval _ _ _ 6 hE (ofNat32_toNat 6 (by decide))
      (ofNat32_toNat (32 - 6) (by decide)) (by decide) (by decide)
  have hc11 : evalExpr (rotrE (.idxu "v" (atU64 4)) 11) ρ =
      .ok (.u32 (rotrU32 E 11)) :=
    rotrE_eval _ _ _ 11 hE (ofNat32_toNat 11 (by decide))
      (ofNat32_toNat (32 - 11) (by decide)) (by decide) (by decide)
  have hc25 : evalExpr (rotrE (.idxu "v" (atU64 4)) 25) ρ =
      .ok (.u32 (rotrU32 E 25)) :=
    rotrE_eval _ _ _ 25 hE (ofNat32_toNat 25 (by decide))
      (ofNat32_toNat (32 - 25) (by decide)) (by decide) (by decide)
  have hc2 : evalExpr (rotrE (.idxu "v" (atU64 0)) 2) ρ =
      .ok (.u32 (rotrU32 A 2)) :=
    rotrE_eval _ _ _ 2 hA (ofNat32_toNat 2 (by decide))
      (ofNat32_toNat (32 - 2) (by decide)) (by decide) (by decide)
  have hc13 : evalExpr (rotrE (.idxu "v" (atU64 0)) 13) ρ =
      .ok (.u32 (rotrU32 A 13)) :=
    rotrE_eval _ _ _ 13 hA (ofNat32_toNat 13 (by decide))
      (ofNat32_toNat (32 - 13) (by decide)) (by decide) (by decide)
  have hc22 : evalExpr (rotrE (.idxu "v" (atU64 0)) 22) ρ =
      .ok (.u32 (rotrU32 A 22)) :=
    rotrE_eval _ _ _ 22 hA (ofNat32_toNat 22 (by decide))
      (ofNat32_toNat (32 - 22) (by decide)) (by decide) (by decide)
  have hT1 : evalExpr t1Expr ρ =
      .ok (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) := by
    simp only [t1Expr, evalExpr, hρv, hρw, hρK, hρr, atU64, litVal,
      htoNat4, htoNat5, htoNat6, htoNat7, htoNatrE, hgetw, hgetk,
      hg4, hg5, hg6, hg7,
      hc6lit, hc11lit, hc25lit, cV1, cV2, cV3, cV4, cV5, cV6]
  have hletT1 := evalStmtFuel_let_ F "t1" (.u 32) t1Expr ρ
    (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) hT1
  -- Post-`t1` reads: `v` via shadowing (the `t2` expression reads
  -- only `v`, so no `w`/`K`/`r` facts are needed here).
  have hρav : envLookup
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r]))) "v" =
      some (.arr32 [A, B, C, D, E, Ff, G, H]) := by
    simp [envExtend, envLookup, hρv, show ("v" : String) ≠ "t1" by decide]
  have hgetv0 : ([A, B, C, D, E, Ff, G, H])[0]? = some A := by simp
  have hgetv1 : ([A, B, C, D, E, Ff, G, H])[1]? = some B := by simp
  have hgetv2 : ([A, B, C, D, E, Ff, G, H])[2]? = some C := by simp
  have hA0lit : evalExpr (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0))))
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 A) := by
    simp only [evalExpr, litVal, hρav, htoNat0, hgetv0]
  have hc2lit : evalExpr (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0)))) 2)
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 (rotrU32 A 2)) := by
    exact rotrE_eval _ _ _ 2 hA0lit (ofNat32_toNat 2 (by decide))
      (ofNat32_toNat (32 - 2) (by decide)) (by decide) (by decide)
  have hc13lit : evalExpr
      (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0)))) 13)
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 (rotrU32 A 13)) := by
    exact rotrE_eval _ _ _ 13 hA0lit (ofNat32_toNat 13 (by decide))
      (ofNat32_toNat (32 - 13) (by decide)) (by decide) (by decide)
  have hc22lit : evalExpr
      (rotrE (.idxu "v" (.lit (.u64 (BitVec.ofNat 64 0)))) 22)
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 (rotrU32 A 22)) := by
    exact rotrE_eval _ _ _ 22 hA0lit (ofNat32_toNat 22 (by decide))
      (ofNat32_toNat (32 - 22) (by decide)) (by decide) (by decide)
  have hT2 : evalExpr t2Expr
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) := by
    simp only [t2Expr, evalExpr, hρav, atU64, litVal,
      htoNat0, htoNat1, htoNat2, hgetv0, hgetv1, hgetv2,
      hc2lit, hc13lit, hc22lit, cV7, cV8, cV9, cV10, cV11, cV12]
  have hletT2 := evalStmtFuel_let_ F "t2" (.u 32) t2Expr
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
    (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) hT2
  -- Post-`t2` reads and frame: `v`/`t1`/`t2` absolutely, the rest as
  -- equalities back to the entry env (two shadowing layers).
  have hρbv : envLookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "v" =
      some (.arr32 [A, B, C, D, E, Ff, G, H]) := by
    have h1 : envLookup (envExtend
        (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
        "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "v" =
        envLookup (envExtend ρ "t1"
          (.u32 (cV6 A B C D E Ff G H w[r] shaK[r]))) "v" := by
      simp [envExtend, envLookup, show ("v" : String) ≠ "t2" by decide]
    rw [h1]; exact hρav
  have hρbt1 : envLookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "t1" =
      some (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) := by
    simp [envExtend, envLookup, show ("t1" : String) ≠ "t2" by decide]
  have hρbt2 : envLookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "t2" =
      some (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) := by
    simp [envExtend, envLookup]
  have ht1v : evalExpr (.var "t1") (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) :=
    evalExpr_var_hit _ _ _ hρbt1
  have ht2v : evalExpr (.var "t2") (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) :=
    evalExpr_var_hit _ _ _ hρbt2
  have hρbr : envLookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "r" =
      envLookup ρ "r" := by
    simp [envExtend, envLookup, show ("r" : String) ≠ "t1" by decide,
      show ("r" : String) ≠ "t2" by decide]
  have hρbw : envLookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "w" =
      envLookup ρ "w" := by
    simp [envExtend, envLookup, show ("w" : String) ≠ "t1" by decide,
      show ("w" : String) ≠ "t2" by decide]
  have hρbK : envLookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "K" =
      envLookup ρ "K" := by
    simp [envExtend, envLookup, show ("K" : String) ≠ "t1" by decide,
      show ("K" : String) ≠ "t2" by decide]
  have hρbst : envLookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "st" =
      envLookup ρ "st" := by
    simp [envExtend, envLookup, show ("st" : String) ≠ "t1" by decide,
      show ("st" : String) ≠ "t2" by decide]
  -- Eight stores high-to-low. Each: the store-value eval fact, the
  -- existential post-env, its `v` lookup (normalized to literal
  -- indices), the frame bundle, and the arrSet step.
  have hv76 : evalExpr (.idxu "v" (atU64 6)) (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) =
      .ok (.u32 G) := by
    simp only [evalExpr, litVal, atU64, hρbv, htoNat6]
    simp
  have hget₇ : ([A, B, C, D, E, Ff, G, H][(BitVec.ofNat 64 7).toNat]? =
      some ([A, B, C, D, E, Ff, G, H][7]'(by simp))) := by
    rw [htoNat7]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup (envExtend
      (envExtend ρ "t1" (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])))
      "t2" (.u32 (cV12 A B C D E Ff G H w[r] shaK[r]))) "v"
    (.arr32 [A, B, C, D, E, Ff, G, H])
    (.arr32 (([A, B, C, D, E, Ff, G, H].set (BitVec.ofNat 64 7).toNat G)))
    hρbv
  have hvself₁ := envLookup_envUpdate_same _ _ _ _ hu₁
  rw [htoNat7] at hvself₁
  obtain ⟨fr₁, fw₁, fK₁, fst₁, ft1₁, ft2₁⟩ := compressFrame_update _ _ _ hu₁
  have e1 := transferArrSet F _ _ _ 7 _ G (by simp) hv76 hρbv
    hget₇ hu₁
  have hv65 : evalExpr (.idxu "v" (atU64 5)) ρ₁ = .ok (.u32 Ff) := by
    have hg : ((([A, B, C, D, E, Ff, G, H].set 7 G))[5]? = some Ff) := by simp
    simp only [evalExpr, litVal, atU64, hvself₁, htoNat5, hg]
  have hget₆ : ((([A, B, C, D, E, Ff, G, H].set 7 G))[
      (BitVec.ofNat 64 6).toNat]? =
      some ((([A, B, C, D, E, Ff, G, H].set 7 G))[6]'(by simp))) := by
    rw [htoNat6]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "v"
    (.arr32 (([A, B, C, D, E, Ff, G, H].set 7 G)))
    (.arr32 ((([A, B, C, D, E, Ff, G, H].set 7 G).set
      (BitVec.ofNat 64 6).toNat Ff))) hvself₁
  have hvself₂ := envLookup_envUpdate_same _ _ _ _ hu₂
  rw [htoNat6] at hvself₂
  obtain ⟨fr₂, fw₂, fK₂, fst₂, ft1₂, ft2₂⟩ := compressFrame_update _ _ _ hu₂
  have e2 := transferArrSet F _ _ _ 6 _ Ff (by simp) hv65 hvself₁
    hget₆ hu₂
  have hv54 : evalExpr (.idxu "v" (atU64 4)) ρ₂ = .ok (.u32 E) := by
    have hg : (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff))[4]? =
      some E) := by simp
    simp only [evalExpr, litVal, atU64, hvself₂, htoNat4, hg]
  have hget₅ : (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff))[
      (BitVec.ofNat 64 5).toNat]? =
      some (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff))[5]'(by simp))) := by
    rw [htoNat5]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "v"
    (.arr32 ((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff)))
    (.arr32 (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set
      (BitVec.ofNat 64 5).toNat E))) hvself₂
  have hvself₃ := envLookup_envUpdate_same _ _ _ _ hu₃
  rw [htoNat5] at hvself₃
  obtain ⟨fr₃, fw₃, fK₃, fst₃, ft1₃, ft2₃⟩ := compressFrame_update _ _ _ hu₃
  have e3 := transferArrSet F _ _ _ 5 _ E (by simp) hv54 hvself₂
    hget₅ hu₃
  have ht1₄ : envLookup ρ₃ "t1" =
      some (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) := by
    rw [ft1₃, ft1₂, ft1₁]; exact hρbt1
  have hvT1D : evalExpr (.uadd (.idxu "v" (atU64 3)) (.var "t1")) ρ₃ =
      .ok (.u32 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))) := by
    have hg : ((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E))[3]? =
      some D) := by simp
    have ht1x := ht1₄
    simp only [evalExpr, litVal, atU64, hvself₃, htoNat3, hg, ht1x]
  have hget₄ : ((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E))[
      (BitVec.ofNat 64 4).toNat]? =
      some ((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set
        5 E))[4]'(by simp))) := by
    rw [htoNat4]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₄, hu₄⟩ := envUpdate_some_of_lookup ρ₃ "v"
    (.arr32 (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E)))
    (.arr32 ((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      (BitVec.ofNat 64 4).toNat (D + (cV6 A B C D E Ff G H w[r] shaK[r])))))
    hvself₃
  have hvself₄ := envLookup_envUpdate_same _ _ _ _ hu₄
  rw [htoNat4] at hvself₄
  obtain ⟨fr₄, fw₄, fK₄, fst₄, ft1₄l, ft2₄l⟩ := compressFrame_update _ _ _ hu₄
  have e4 := transferArrSet F _ _ _ 4 _ _ (by simp) hvT1D hvself₃
    hget₄ hu₄
  have hvC : evalExpr (.idxu "v" (atU64 2)) ρ₄ = .ok (.u32 C) := by
    have hg : (((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))))[2]? = some C) := by simp
    simp only [evalExpr, litVal, atU64, hvself₄, htoNat2, hg]
  have hget₃ : (((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))))[
      (BitVec.ofNat 64 3).toNat]? =
      some (((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))))[3]'(by simp))) := by
    rw [htoNat3]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₅, hu₅⟩ := envUpdate_some_of_lookup ρ₄ "v"
    (.arr32 (((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))))
    (.arr32 ((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set
      (BitVec.ofNat 64 3).toNat C)) hvself₄
  have hvself₅ := envLookup_envUpdate_same _ _ _ _ hu₅
  rw [htoNat3] at hvself₅
  obtain ⟨fr₅, fw₅, fK₅, fst₅, ft1₅, ft2₅⟩ := compressFrame_update _ _ _ hu₅
  have e5 := transferArrSet F _ _ _ 3 _ C (by simp) hvC hvself₄
    hget₃ hu₅
  have hvB : evalExpr (.idxu "v" (atU64 1)) ρ₅ = .ok (.u32 B) := by
    have hg : ((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C))[1]? =
      some B) := by simp
    simp only [evalExpr, litVal, atU64, hvself₅, htoNat1, hg]
  have hget₂ : ((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C))[
      (BitVec.ofNat 64 2).toNat]? =
      some ((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C))[2]'(by simp))) := by
    rw [htoNat2]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup ρ₅ "v"
    (.arr32 ((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C))
    (.arr32 (((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set
      (BitVec.ofNat 64 2).toNat B)) hvself₅
  have hvself₆ := envLookup_envUpdate_same _ _ _ _ hu₆
  rw [htoNat2] at hvself₆
  obtain ⟨fr₆, fw₆, fK₆, fst₆, ft1₆, ft2₆⟩ := compressFrame_update _ _ _ hu₆
  have e6 := transferArrSet F _ _ _ 2 _ B (by simp) hvB hvself₅
    hget₂ hu₆
  have hvA : evalExpr (.idxu "v" (atU64 0)) ρ₆ = .ok (.u32 A) := by
    have hg : (((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B))[0]? =
      some A) := by simp
    simp only [evalExpr, litVal, atU64, hvself₆, htoNat0, hg]
  have hget₁ : (((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B))[
      (BitVec.ofNat 64 1).toNat]? =
      some (((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set
        2 B))[1]'(by simp))) := by
    rw [htoNat1]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₇, hu₇⟩ := envUpdate_some_of_lookup ρ₆ "v"
    (.arr32 (((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B))
    (.arr32 ((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set
      (BitVec.ofNat 64 1).toNat A)) hvself₆
  have hvself₇ := envLookup_envUpdate_same _ _ _ _ hu₇
  rw [htoNat1] at hvself₇
  obtain ⟨fr₇, fw₇, fK₇, fst₇, ft1₇, ft2₇⟩ := compressFrame_update _ _ _ hu₇
  have e7 := transferArrSet F _ _ _ 1 _ A (by simp) hvA hvself₆
    hget₁ hu₇
  have ht1₇ : envLookup ρ₇ "t1" =
      some (.u32 (cV6 A B C D E Ff G H w[r] shaK[r])) := by
    rw [ft1₇, ft1₆, ft1₅, ft1₄l, ft1₃, ft1₂, ft1₁]; exact hρbt1
  have ht2₇ : envLookup ρ₇ "t2" =
      some (.u32 (cV12 A B C D E Ff G H w[r] shaK[r])) := by
    rw [ft2₇, ft2₆, ft2₅, ft2₄l, ft2₃, ft2₂, ft2₁]; exact hρbt2
  have hvT : evalExpr (.uadd (.var "t1") (.var "t2")) ρ₇ =
      .ok (.u32 ((cV6 A B C D E Ff G H w[r] shaK[r]) +
        (cV12 A B C D E Ff G H w[r] shaK[r]))) := by
    have ht1y := ht1₇
    have ht2y := ht2₇
    simp only [evalExpr, ht1y, ht2y]
  have hget₀ : (((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A)[(BitVec.ofNat 64 0).toNat]? =
      some (((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A)[0]'(by simp))) := by
    rw [htoNat0]; exact List.getElem?_eq_getElem (by simp)
  obtain ⟨ρ₈, hu₈⟩ := envUpdate_some_of_lookup ρ₇ "v"
    (.arr32 ((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set
      1 A))
    (.arr32 (((((((([A, B, C, D, E, Ff, G, H].set 7 G).set 6 Ff).set 5 E).set
      4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set
      1 A).set (BitVec.ofNat 64 0).toNat ((cV6 A B C D E Ff G H w[r] shaK[r]) +
        (cV12 A B C D E Ff G H w[r] shaK[r])))) hvself₇
  have hvself₈ := envLookup_envUpdate_same _ _ _ _ hu₈
  rw [htoNat0] at hvself₈
  obtain ⟨fr₈, fw₈, fK₈, fst₈, ft1₈, ft2₈⟩ := compressFrame_update _ _ _ hu₈
  have e8 := transferArrSet F _ _ _ 0 _ _ (by simp) hvT hvself₇
    hget₀ hu₈
  -- The eval-order chain is `roundStep`: same eight positions, so
  -- extensionality plus an `omega` case split (mirrors the
  -- exact-env certificate's bridge).
  have hbridge :
      (((((((((A :: B :: C :: D :: E :: Ff :: G :: H :: []).set 7 G).set 6 Ff).set
        5 E).set 4 (D + (cV6 A B C D E Ff G H w[r] shaK[r]))).set 3 C).set 2 B).set 1 A).set 0 ((cV6 A B C D E Ff G H w[r] shaK[r]) + (cV12 A B C D E Ff G H w[r] shaK[r]))) =
      roundStep [A, B, C, D, E, Ff, G, H] w r := by
    have hrr : roundStep [A, B, C, D, E, Ff, G, H] w r =
        [(cV6 A B C D E Ff G H w[r] shaK[r]) + (cV12 A B C D E Ff G H w[r] shaK[r]), A, B, C, D + (cV6 A B C D E Ff G H w[r] shaK[r]), E, Ff, G] := by
      simp only [roundStep, hgetw, hgetk, shaS1, shaCh, shaS0, shaMaj,
        cV1, cV2, cV3, cV4, cV5, cV6, cV7, cV8, cV9, cV10, cV11, cV12]
    rw [hrr]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 8
    · have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
          i = 7 := by omega
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hc <;> simp
    · rw [List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by simp; omega)]
  have heval : evalStmtFuel F compressFrag ρ = .ok (ρ₈, .fellThrough) := by
    rw [compressFrag,
      evalStmtFuel_seq_fallthrough F _ _ _ _ hletT1,
      evalStmtFuel_seq_fallthrough F _ _ _ _ hletT2,
      evalStmtFuel_seq_fallthrough F _ _ _ _ e1,
      evalStmtFuel_seq_fallthrough F _ _ _ _ e2,
      evalStmtFuel_seq_fallthrough F _ _ _ _ e3,
      evalStmtFuel_seq_fallthrough F _ _ _ _ e4,
      evalStmtFuel_seq_fallthrough F _ _ _ _ e5,
      evalStmtFuel_seq_fallthrough F _ _ _ _ e6,
      evalStmtFuel_seq_fallthrough F _ _ _ _ e7,
      e8]
  have hvconcl : envLookup ρ₈ "v" =
      some (.arr32 (roundStep [A, B, C, D, E, Ff, G, H] w r)) :=
    hbridge ▸ hvself₈
  have hrconcl : envLookup ρ₈ "r" = envLookup ρ "r" := by
    rw [fr₈, fr₇, fr₆, fr₅, fr₄, fr₃, fr₂, fr₁, hρbr]
  have hwconcl : envLookup ρ₈ "w" = envLookup ρ "w" := by
    rw [fw₈, fw₇, fw₆, fw₅, fw₄, fw₃, fw₂, fw₁, hρbw]
  have hKconcl : envLookup ρ₈ "K" = envLookup ρ "K" := by
    rw [fK₈, fK₇, fK₆, fK₅, fK₄, fK₃, fK₂, fK₁, hρbK]
  have hstconcl : envLookup ρ₈ "st" = envLookup ρ "st" := by
    rw [fst₈, fst₇, fst₆, fst₅, fst₄, fst₃, fst₂, fst₁, hρbst]
  exact ⟨ρ₈, heval, hvconcl, hrconcl, hwconcl, hKconcl, hstconcl⟩
