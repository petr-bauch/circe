/-
Circe.Crypto.Block — the K4 ChaCha20 block function `chacha20_block`
(`tests/c/chacha_block.c`): the first multi-thousand-op corpus entry
(1413 `.cir` lines, 3 `cir.for` loops, 226 `cir.get_element`), verified
against the K3 round spec (`Circe.Crypto.Qr`).

Mirror discipline (K2 precedent): the working copy `x` is a `let_`
whole-list copy of `state` (the C's 16-iteration copy loop has no
observable behavior beyond the copy — the gate pins the loop
structurally via exact op counts, the mirror abstracts it); the ten
double-rounds are one `while (r < 10)` over `roundFrag` (eight inlined
quarter rounds — a 4-writer QR leaf could never pass the pair check,
so the round is inlined, K3 design note); the add-back is one
`while (i < 16)`. Rotation amounts are `u32` literals (`16/12/8/7`,
complements `16/20/24/25`), all `< 32`, so no shift UB arises (K1
`checkedShiftU32` — the amounts never approach the failure case).

Lengths are prefix-generic (K2 precedent): states longer than 16
words pass the tail through untouched; shorter than 16 is `OOB`
(the round loop reads indices `< 16`, so a short state fails loudly
in round one — see `roundFrag_oob`).
-/
import Circe.Emit.Fragment
import Circe.Crypto.Qr

/-! ### Mirror fragments -/

/-- Literal `u64` index: `arrSet` positions are compile-time constants
    (the index expression must evaluate to a `u64` word — an `idxu`
    read would deliver a `u32` and `AssertFail`, cf. the `arrSet`
    equation in `Circe.Eval.Stmt`). -/
def atU64 (i : Nat) : CExpr := .lit (.u64 (BitVec.ofNat 64 i))

/-- `x[i]` read (`u64` index, K2/N9 writer-loop precedent). -/
def xAt (i : Nat) : CExpr := .idxu "x" (.lit (.u64 (BitVec.ofNat 64 i)))

/-- Rotate-left-by-`n` over `x[i]` (K1 leaves composed: `bshl`/`bshr`
    over `u32` literal amounts joined by `bor`). -/
def rotlAt (i n : Nat) : CExpr :=
  .bor (.bshl (xAt i) (.lit (.u32 (BitVec.ofNat 32 n))))
    (.bshr (xAt i) (.lit (.u32 (BitVec.ofNat 32 (32 - n)))))

/-- One inlined quarter round over `x[a], x[b], x[c], x[d]` (the RFC
    8439 §2.1 macro: four add-xor-roll lines, twelve word-stores). -/
def qrFrag (a b c d : Nat) : CStmt :=
  .seq (.arrSet "x" (atU64 a) (.uadd (xAt a) (xAt b)))
  (.seq (.arrSet "x" (atU64 d) (.bxor (xAt d) (xAt a)))
  (.seq (.arrSet "x" (atU64 d) (rotlAt d 16))
  (.seq (.arrSet "x" (atU64 c) (.uadd (xAt c) (xAt d)))
  (.seq (.arrSet "x" (atU64 b) (.bxor (xAt b) (xAt c)))
  (.seq (.arrSet "x" (atU64 b) (rotlAt b 12))
  (.seq (.arrSet "x" (atU64 a) (.uadd (xAt a) (xAt b)))
  (.seq (.arrSet "x" (atU64 d) (.bxor (xAt d) (xAt a)))
  (.seq (.arrSet "x" (atU64 d) (rotlAt d 8))
  (.seq (.arrSet "x" (atU64 c) (.uadd (xAt c) (xAt d)))
  (.seq (.arrSet "x" (atU64 b) (.bxor (xAt b) (xAt c)))
    (.arrSet "x" (atU64 b) (rotlAt b 7))))))))))))

/-- One double round: four column QRs then four diagonal QRs (RFC
    8439 §2.3 inner block — mirrors `chachaRound`). -/
def roundFrag : CStmt :=
  .seq (qrFrag 0 4 8 12)
  (.seq (qrFrag 1 5 9 13)
  (.seq (qrFrag 2 6 10 14)
  (.seq (qrFrag 3 7 11 15)
  (.seq (qrFrag 0 5 10 15)
  (.seq (qrFrag 1 6 11 12)
  (.seq (qrFrag 2 7 8 13)
    (qrFrag 3 4 9 14)))))))

/-- Round-loop body: one double round, then `r++`. -/
def roundBody : CStmt :=
  .seq roundFrag
    (.assign "r" (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The ten-double-round loop (`cir.for` over `r in [0, 10)`). -/
def roundWhile : CStmt :=
  .while_ (.ult (.var "r") (.lit (.u64 (BitVec.ofNat 64 10)))) roundBody

/-- Add-back body: `state[i] += x[i]; i++` (one `cir.add` + one
    word-store, the third `cir.for` step region). -/
def addBody : CStmt :=
  .seq (.arrSet "state" (.var "i")
          (.uadd (.idxu "state" (.var "i")) (.idxu "x" (.var "i"))))
       (.assign "i" (.uadd (.var "i")
         (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The add-back loop (`cir.for` over `i in [0, 16)`). -/
def addWhile : CStmt :=
  .while_ (.ult (.var "i") (.lit (.u64 (BitVec.ofNat 64 16)))) addBody

/-- Canonical CoreIR for `tests/c/chacha_block.c`: whole-list copy of
    the 16-word state, ten double-rounds over the copy, add-back over
    `state`, returning the state buffer. -/
def chachaBlockFunc : Func :=
  ⟨"chacha20_block",
   [{ name := "state", ty := .array (.u 32) 16, role := .mutBorrow 0 }],
   .array (.u 32) 16,
   .seq (.let_ "x" (.array (.u 32) 16) (.var "state"))
   (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq roundWhile
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq addWhile (.return_ (.var "state"))))))⟩

/-! ### Value spec -/

/-- Add-back: `orig` with the first `n` words bumped by `rnd`
    (out-of-bounds indices read `0` via `getD`; unreachable under the
    length hypotheses the forward checks). -/
def addBackList (orig rnd : List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => orig
  | n+1 =>
    ((addBackList orig rnd n).set n
      ((orig[n]?.getD 0) + (rnd[n]?.getD 0)))

/-- Unfolding the last step (definitional). -/
theorem addBackList_succ (orig rnd : List (BitVec 32)) (n : Nat) :
    addBackList orig rnd (n + 1) =
      ((addBackList orig rnd n).set n
        ((orig[n]?.getD 0) + (rnd[n]?.getD 0))) := rfl

/-- The add-back keeps its length. -/
theorem addBackList_length (orig rnd : List (BitVec 32)) (n : Nat) :
    (addBackList orig rnd n).length = orig.length := by
  induction n generalizing orig with
  | zero => rfl
  | succ k ih => simp [addBackList, ih, List.length_set]

/-- Rounds keep the state length (`qrAt` preserves it). -/
theorem chachaRound_length (s : List (BitVec 32)) :
    (chachaRound s).length = s.length := by
  simp [chachaRound, qrAt_length]

/-- Any number of rounds keeps the state length. -/
theorem chachaRounds_length (n : Nat) (s : List (BitVec 32)) :
    (chachaRounds n s).length = s.length := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp [chachaRounds, chachaRound_length, ih]

/-- Value-level forward for `chacha20_block`: ten double-rounds over
    the input, added back word-wise; `OOB` below 16 words (the round
    loop reads indices `< 16` — C would read out of bounds). Longer
    states pass the tail through (K2 prefix-generic precedent). -/
def chachaBlockFwd (s : List (BitVec 32)) : Result Value :=
  if 16 ≤ s.length then
    .ok (.arr32 (addBackList s (chachaRounds 10 s) 16))
  else .error .OOB

/-! ### Round-env lemmas -/

/-- Round-loop env: round index `k`, working copy `cur`, input `s`. -/
def mkRoundEnv (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) : Env :=
  [("r", .u64 (BitVec.ofNat 64 k)), ("x", .arr32 cur), ("state", .arr32 s)]

theorem mkRoundEnv_r (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkRoundEnv s k cur) "r" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkRoundEnv, envLookup]

theorem mkRoundEnv_x (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkRoundEnv s k cur) "x" = some (.arr32 cur) := by
  simp [mkRoundEnv, envLookup, show ("x" : String) ≠ "r" by decide]

theorem mkRoundEnv_state (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) :
    envLookup (mkRoundEnv s k cur) "state" = some (.arr32 s) := by
  simp [mkRoundEnv, envLookup, show ("state" : String) ≠ "r" by decide,
    show ("state" : String) ≠ "x" by decide]

/-- Updating `x` in a round env stays a round env. -/
theorem roundEnv_update_x (s : List (BitVec 32)) (k : Nat)
    (cur v : List (BitVec 32)) :
    envUpdate (mkRoundEnv s k cur) "x" (.arr32 v) =
      some (mkRoundEnv s k v) := by
  simp [mkRoundEnv, envUpdate, show ("x" : String) ≠ "r" by decide]

/-- Updating `r` in a round env stays a round env. -/
theorem roundEnv_update_r (s : List (BitVec 32)) (k k' : Nat)
    (cur : List (BitVec 32)) :
    envUpdate (mkRoundEnv s k cur) "r" (.u64 (BitVec.ofNat 64 k')) =
      some (mkRoundEnv s k' cur) := by
  simp [mkRoundEnv, envUpdate]

/-- The round condition reads `r` against the literal bound `10`. -/
theorem roundCond_eval (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (h : k < 2 ^ 64) :
    evalExpr (.ult (.var "r") (.lit (.u64 (BitVec.ofNat 64 10))))
        (mkRoundEnv s k cur) =
      .ok (.b (decide (k < 10))) := by
  have hr := mkRoundEnv_r s k cur
  have h10 : (BitVec.ofNat 64 10).toNat = 10 := ofNat64_toNat 10 (by decide)
  simp [evalExpr, hr, litVal, ofNat64_ult k _ h, h10]

/-- `bor` over two evaluated words (variable subexpressions, so no
    evaluator equation preempts the hypotheses — the compound-`bor`
    assembly at the end of `rotlAt_eval`). -/
theorem evalExpr_bor_ok (a b : CExpr) (ρ : Env) (x y : BitVec 32)
    (ha : evalExpr a ρ = .ok (.u32 x)) (hb : evalExpr b ρ = .ok (.u32 y)) :
    evalExpr (.bor a b) ρ = .ok (.u32 (x ||| y)) := by
  have h : evalExpr (.bor a b) ρ = match evalExpr a ρ, evalExpr b ρ with
      | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x ||| y))
      | .ok _, .ok _ => .error .AssertFail
      | .error e, _ => .error e
      | _, .error e => .error e := rfl
  rw [h, ha, hb]

/-- A `rotlAt` evaluates to the K3 `rotlU32` (both shift amounts are
    `< 32`, so the K1 check always succeeds — the `u32_map_ok`
    rewrites are `exact`, never `simp`, per the `Fragment` note). -/
theorem rotlAt_eval (ρ : Env) (v : BitVec 32) (i n : Nat)
    (hidx : evalExpr (xAt i) ρ = .ok (.u32 v))
    (hn_toNat : (BitVec.ofNat 32 n).toNat = n)
    (hnc_toNat : (BitVec.ofNat 32 (32 - n)).toNat = 32 - n)
    (hn : n < 32) (hn0 : 0 < n) :
    evalExpr (rotlAt i n) ρ = .ok (.u32 (rotlU32 v n)) := by
  have hshl : checkedShiftU32 v (BitVec.ofNat 32 n) (· <<< ·) =
      .ok (v <<< n) := by
    have h := checkedShiftU32_ok v (BitVec.ofNat 32 n) (· <<< ·)
      (by rw [hn_toNat]; exact hn)
    rw [hn_toNat] at h
    exact h
  have hshr : checkedShiftU32 v (BitVec.ofNat 32 (32 - n)) (· >>> ·) =
      .ok (v >>> (32 - n)) := by
    have h := checkedShiftU32_ok v (BitVec.ofNat 32 (32 - n)) (· >>> ·)
      (by rw [hnc_toNat]; omega)
    rw [hnc_toNat] at h
    exact h
  have e1 : evalExpr
        (.bshl (xAt i) (.lit (.u32 (BitVec.ofNat 32 n)))) ρ =
        .ok (.u32 (v <<< n)) := by
    simp only [evalExpr, hidx, litVal]
    rw [hshl]
    exact u32_map_ok _
  have e2 : evalExpr
        (.bshr (xAt i) (.lit (.u32 (BitVec.ofNat 32 (32 - n))))) ρ =
        .ok (.u32 (v >>> (32 - n))) := by
    simp only [evalExpr, hidx, litVal]
    rw [hshr]
    exact u32_map_ok _
  have hbor := evalExpr_bor_ok _ _ ρ _ _ e1 e2
  simp only [rotlAt, hbor, rotlU32]

/-- One `x`-cell write in a round env (the per-step engine behind
    `qrFrag_eval`: literal index, value already evaluated). -/
theorem roundArrSet (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (L : List (BitVec 32)) (t : Nat) (ve : CExpr) (v : BitVec 32)
    (ht : t < L.length) (ht64 : t < 2 ^ 64)
    (hv : evalExpr ve (mkRoundEnv s k L) = .ok (.u32 v)) :
    evalStmtFuel F (.arrSet "x" (atU64 t) ve) (mkRoundEnv s k L) =
      .ok (mkRoundEnv s k (L.set t v), .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 t).toNat = t := ofNat64_toNat t ht64
  have hi : evalExpr (atU64 t) (mkRoundEnv s k L) =
      .ok (.u64 (BitVec.ofNat 64 t)) := by
    simp [atU64, evalExpr, litVal]
  have harr := mkRoundEnv_x s k L
  have hget : L[(BitVec.ofNat 64 t).toNat]? = some L[t] := by
    rw [htoNat]; exact List.getElem?_eq_getElem ht
  have hu : envUpdate (mkRoundEnv s k L) "x"
      (.arr32 (L.set (BitVec.ofNat 64 t).toNat v)) =
      some (mkRoundEnv s k (L.set t v)) := by
    rw [htoNat]; exact roundEnv_update_x s k L (L.set t v)
  exact evalStmtFuel_arrSet F "x" (atU64 t) ve _ _ v L L[t] _ hi hv harr
    hget hu

/-! ### Quarter-round evaluation -/

/-- QR working values over reads `A B C D`, mirroring `qrStep`'s
    let-chain exactly (one definition site so the eval chain and the
    `qrAt` bridge cannot drift; ignored positions are `_`-prefixed to
    keep the uniform 4-tuple shape without linter noise). -/
def qrV1 (A B _C _D : BitVec 32) : BitVec 32 := A + B
def qrV2 (A B C D : BitVec 32) : BitVec 32 := D ^^^ qrV1 A B C D
def qrV3 (A B C D : BitVec 32) : BitVec 32 := rotlU32 (qrV2 A B C D) 16
def qrV4 (A B C D : BitVec 32) : BitVec 32 := C + qrV3 A B C D
def qrV5 (A B C D : BitVec 32) : BitVec 32 := B ^^^ qrV4 A B C D
def qrV6 (A B C D : BitVec 32) : BitVec 32 := rotlU32 (qrV5 A B C D) 12
def qrV7 (A B C D : BitVec 32) : BitVec 32 := qrV1 A B C D + qrV6 A B C D
def qrV8 (A B C D : BitVec 32) : BitVec 32 := qrV3 A B C D ^^^ qrV7 A B C D
def qrV9 (A B C D : BitVec 32) : BitVec 32 := rotlU32 (qrV8 A B C D) 8
def qrV10 (A B C D : BitVec 32) : BitVec 32 := qrV4 A B C D + qrV9 A B C D
def qrV11 (A B C D : BitVec 32) : BitVec 32 := qrV6 A B C D ^^^ qrV10 A B C D
def qrV12 (A B C D : BitVec 32) : BitVec 32 := rotlU32 (qrV11 A B C D) 7

-- Giant single-command bridge proof below (twelve eval steps plus
-- extensionality reassembly): the default 200000-heartbeat budget starves
-- the late tactics even though every step is linear, so raise it here.
set_option maxHeartbeats 1000000
/-- One inlined quarter round evaluates to `qrAt` (any fuel:
    loop-free). The twelve writes chain through `roundArrSet`; the
    eval-order write chain differs from `qrAt`'s constructor order, so
    the bridge `hbridge` goes by extensionality (same indices,
    distinct cells — `hqr` first rephrases `qrAt` in `qrV` form). -/
theorem qrFrag_eval (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (a b c d : Nat)
    (hqr : a < cur.length ∧ b < cur.length ∧ c < cur.length ∧ d < cur.length)
    (h64 : a < 2 ^ 64 ∧ b < 2 ^ 64 ∧ c < 2 ^ 64 ∧ d < 2 ^ 64)
    (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) :
    evalStmtFuel F (qrFrag a b c d) (mkRoundEnv s k cur) =
      .ok (mkRoundEnv s k (qrAt cur a b c d), .fellThrough) := by
  obtain ⟨ha, hb, hc, hd⟩ := hqr
  obtain ⟨ha64, hb64, hc64, hd64⟩ := h64
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hdist
  have htoNat_a : (BitVec.ofNat 64 a).toNat = a := ofNat64_toNat a ha64
  have htoNat_b : (BitVec.ofNat 64 b).toNat = b := ofNat64_toNat b hb64
  have htoNat_c : (BitVec.ofNat 64 c).toNat = c := ofNat64_toNat c hc64
  have htoNat_d : (BitVec.ofNat 64 d).toNat = d := ofNat64_toNat d hd64
  have hgeta0 : cur[a]? = some cur[a] := List.getElem?_eq_getElem ha
  have hgetb0 : cur[b]? = some cur[b] := List.getElem?_eq_getElem hb
  have hgetc0 : cur[c]? = some cur[c] := List.getElem?_eq_getElem hc
  have hgetd0 : cur[d]? = some cur[d] := List.getElem?_eq_getElem hd
  have hxa0 := mkRoundEnv_x s k cur
  have hixa : evalExpr (xAt a) (mkRoundEnv s k cur) = .ok (.u32 cur[a]) := by
    simp only [xAt, evalExpr, litVal, hxa0, htoNat_a, hgeta0]
  have hixb : evalExpr (xAt b) (mkRoundEnv s k cur) = .ok (.u32 cur[b]) := by
    simp only [xAt, evalExpr, litVal, hxa0, htoNat_b, hgetb0]
  have hixc : evalExpr (xAt c) (mkRoundEnv s k cur) = .ok (.u32 cur[c]) := by
    simp only [xAt, evalExpr, litVal, hxa0, htoNat_c, hgetc0]
  have hixd : evalExpr (xAt d) (mkRoundEnv s k cur) = .ok (.u32 cur[d]) := by
    simp only [xAt, evalExpr, litVal, hxa0, htoNat_d, hgetd0]
  -- Step 1: `x[a] += x[b]`.
  have hv1 : evalExpr (.uadd (xAt a) (xAt b)) (mkRoundEnv s k cur) =
      .ok (.u32 (qrV1 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hixa, hixb, qrV1]
  have e1 := roundArrSet F s k cur a _ _ ha ha64 hv1
  -- Step 2: `x[d] ^= x[a]` (reads the just-written `a`).
  have hg2d : (cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d]))[d]? =
      some cur[d] := by
    simp only [List.getElem?_set_ne had, hgetd0]
  have hg2a : (cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d]))[a]? =
      some (qrV1 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self ha
  have hx1 := mkRoundEnv_x s k
    (cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d]))
  have hix2d : evalExpr (xAt d)
        (mkRoundEnv s k (cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 cur[d]) := by
    simp only [xAt, evalExpr, litVal, hx1, htoNat_d, hg2d]
  have hix2a : evalExpr (xAt a)
        (mkRoundEnv s k (cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV1 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx1, htoNat_a, hg2a]
  have hv2 : evalExpr (.bxor (xAt d) (xAt a))
        (mkRoundEnv s k (cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV2 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hix2d, hix2a, qrV2]
  have e2 := roundArrSet F s k _ d _ _
    (by simp only [List.length_set]; exact hd) hd64 hv2
  -- Step 3: `x[d] = rotl(x[d], 16)`.
  have hg3d : ((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d]))[d]? =
      some (qrV2 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hd)
  have hx2 := mkRoundEnv_x s k
    ((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d]))
  have hix3d : evalExpr (xAt d)
        (mkRoundEnv s k ((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV2 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx2, htoNat_d, hg3d]
  have hv3 : evalExpr (rotlAt d 16)
        (mkRoundEnv s k ((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV3 cur[a] cur[b] cur[c] cur[d])) :=
    rotlAt_eval _ _ d 16 hix3d (ofNat32_toNat 16 (by decide))
      (ofNat32_toNat (32 - 16) (by decide)) (by decide) (by decide)
  have e3 := roundArrSet F s k _ d _ _
    (by simp only [List.length_set]; exact hd) hd64 hv3
  -- Step 4: `x[c] += x[d]`.
  have hg4c : (((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d]))[c]? = some cur[c] := by
    simp only [List.getElem?_set_ne hcd.symm, List.getElem?_set_ne hac,
      hgetc0]
  have hg4d : (((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d]))[d]? =
      some (qrV3 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hd)
  have hx3 := mkRoundEnv_x s k
    (((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d]))
  have hix4c : evalExpr (xAt c)
        (mkRoundEnv s k (((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 cur[c]) := by
    simp only [xAt, evalExpr, litVal, hx3, htoNat_c, hg4c]
  have hix4d : evalExpr (xAt d)
        (mkRoundEnv s k (((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV3 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx3, htoNat_d, hg4d]
  have hv4 : evalExpr (.uadd (xAt c) (xAt d))
        (mkRoundEnv s k (((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV4 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hix4c, hix4d, qrV4]
  have e4 := roundArrSet F s k _ c _ _
    (by simp only [List.length_set]; exact hc) hc64 hv4
  -- Step 5: `x[b] ^= x[c]`.
  have hg5b : ((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d]))[b]? = some cur[b] := by
    simp only [List.getElem?_set_ne hbc.symm, List.getElem?_set_ne hbd.symm,
      List.getElem?_set_ne hab, hgetb0]
  have hg5c : ((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d]))[c]? =
      some (qrV4 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hc)
  have hx4 := mkRoundEnv_x s k
    ((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d]))
  have hix5b : evalExpr (xAt b)
        (mkRoundEnv s k ((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 cur[b]) := by
    simp only [xAt, evalExpr, litVal, hx4, htoNat_b, hg5b]
  have hix5c : evalExpr (xAt c)
        (mkRoundEnv s k ((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV4 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx4, htoNat_c, hg5c]
  have hv5 : evalExpr (.bxor (xAt b) (xAt c))
        (mkRoundEnv s k ((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV5 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hix5b, hix5c, qrV5]
  have e5 := roundArrSet F s k _ b _ _
    (by simp only [List.length_set]; exact hb) hb64 hv5
  -- Step 6: `x[b] = rotl(x[b], 12)`.
  have hg6b : (((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d]))[b]? =
      some (qrV5 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hb)
  have hx5 := mkRoundEnv_x s k
    (((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d]))
  have hix6b : evalExpr (xAt b)
        (mkRoundEnv s k (((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV5 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx5, htoNat_b, hg6b]
  have hv6 : evalExpr (rotlAt b 12)
        (mkRoundEnv s k (((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV6 cur[a] cur[b] cur[c] cur[d])) :=
    rotlAt_eval _ _ b 12 hix6b (ofNat32_toNat 12 (by decide))
      (ofNat32_toNat (32 - 12) (by decide)) (by decide) (by decide)
  have e6 := roundArrSet F s k _ b _ _
    (by simp only [List.length_set]; exact hb) hb64 hv6
  -- Step 7: `x[a] += x[b]` (reads the round-1 `a`, the new `b`).
  have hg7a : ((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d]))[a]? =
      some (qrV1 cur[a] cur[b] cur[c] cur[d]) := by
    simp only [List.getElem?_set_ne hab.symm, List.getElem?_set_ne hac.symm,
      List.getElem?_set_ne had.symm, List.getElem?_set_self, ha]
  have hg7b : ((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d]))[b]? =
      some (qrV6 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hb)
  have hx6 := mkRoundEnv_x s k
    ((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d]))
  have hix7a : evalExpr (xAt a)
        (mkRoundEnv s k ((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV1 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx6, htoNat_a, hg7a]
  have hix7b : evalExpr (xAt b)
        (mkRoundEnv s k ((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV6 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx6, htoNat_b, hg7b]
  have hv7 : evalExpr (.uadd (xAt a) (xAt b))
        (mkRoundEnv s k ((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV7 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hix7a, hix7b, qrV7]
  have e7 := roundArrSet F s k _ a _ _
    (by simp only [List.length_set]; exact ha) ha64 hv7
  -- Step 8: `x[d] ^= x[a]`.
  have hg8d : (((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d]))[d]? =
      some (qrV3 cur[a] cur[b] cur[c] cur[d]) := by
    simp only [List.getElem?_set_ne had, List.getElem?_set_ne hbd,
      List.getElem?_set_ne hcd, List.getElem?_set_self,
      List.length_set, hd]
  have hg8a : (((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d]))[a]? =
      some (qrV7 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact ha)
  have hx7 := mkRoundEnv_x s k
    (((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d]))
  have hix8d : evalExpr (xAt d)
        (mkRoundEnv s k (((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV3 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx7, htoNat_d, hg8d]
  have hix8a : evalExpr (xAt a)
        (mkRoundEnv s k (((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV7 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx7, htoNat_a, hg8a]
  have hv8 : evalExpr (.bxor (xAt d) (xAt a))
        (mkRoundEnv s k (((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV8 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hix8d, hix8a, qrV8]
  have e8 := roundArrSet F s k _ d _ _
    (by simp only [List.length_set]; exact hd) hd64 hv8
  -- Step 9: `x[d] = rotl(x[d], 8)`.
  have hg9d : ((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d]))[d]? =
      some (qrV8 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hd)
  have hx8 := mkRoundEnv_x s k
    ((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d]))
  have hix9d : evalExpr (xAt d)
        (mkRoundEnv s k ((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV8 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx8, htoNat_d, hg9d]
  have hv9 : evalExpr (rotlAt d 8)
        (mkRoundEnv s k ((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV9 cur[a] cur[b] cur[c] cur[d])) :=
    rotlAt_eval _ _ d 8 hix9d (ofNat32_toNat 8 (by decide))
      (ofNat32_toNat (32 - 8) (by decide)) (by decide) (by decide)
  have e9 := roundArrSet F s k _ d _ _
    (by simp only [List.length_set]; exact hd) hd64 hv9
  -- Step 10: `x[c] += x[d]`.
  have hg10c : (((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d]))[c]? =
      some (qrV4 cur[a] cur[b] cur[c] cur[d]) := by
    simp only [List.getElem?_set_ne hcd.symm, List.getElem?_set_ne hac,
      List.getElem?_set_ne hbc, List.getElem?_set_self,
      List.length_set, hc]
  have hg10d : (((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d]))[d]? =
      some (qrV9 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hd)
  have hx9 := mkRoundEnv_x s k
    (((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d]))
  have hix10c : evalExpr (xAt c)
        (mkRoundEnv s k (((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV4 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx9, htoNat_c, hg10c]
  have hix10d : evalExpr (xAt d)
        (mkRoundEnv s k (((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV9 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx9, htoNat_d, hg10d]
  have hv10 : evalExpr (.uadd (xAt c) (xAt d))
        (mkRoundEnv s k (((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV10 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hix10c, hix10d, qrV10]
  have e10 := roundArrSet F s k _ c _ _
    (by simp only [List.length_set]; exact hc) hc64 hv10
  -- Step 11: `x[b] ^= x[c]`.
  have hg11b : ((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV10 cur[a] cur[b] cur[c] cur[d]))[b]? =
      some (qrV6 cur[a] cur[b] cur[c] cur[d]) := by
    simp only [List.getElem?_set_ne hbc.symm, List.getElem?_set_ne hbd.symm,
      List.getElem?_set_ne hab, List.getElem?_set_self,
      List.length_set, hb]
  have hg11c : ((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV10 cur[a] cur[b] cur[c] cur[d]))[c]? =
      some (qrV10 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hc)
  have hx10 := mkRoundEnv_x s k
    ((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV10 cur[a] cur[b] cur[c] cur[d]))
  have hix11b : evalExpr (xAt b)
        (mkRoundEnv s k ((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV6 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx10, htoNat_b, hg11b]
  have hix11c : evalExpr (xAt c)
        (mkRoundEnv s k ((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV10 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx10, htoNat_c, hg11c]
  have hv11 : evalExpr (.bxor (xAt b) (xAt c))
        (mkRoundEnv s k ((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV11 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [evalExpr, hix11b, hix11c, qrV11]
  have e11 := roundArrSet F s k _ b _ _
    (by simp only [List.length_set]; exact hb) hb64 hv11
  -- Step 12: `x[b] = rotl(x[b], 7)`.
  have hg12b : (((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV10 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV11 cur[a] cur[b] cur[c] cur[d]))[b]? =
      some (qrV11 cur[a] cur[b] cur[c] cur[d]) :=
    List.getElem?_set_self (by simp only [List.length_set]; exact hb)
  have hx11 := mkRoundEnv_x s k
    (((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
      (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
      (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
      (qrV10 cur[a] cur[b] cur[c] cur[d])).set b
      (qrV11 cur[a] cur[b] cur[c] cur[d]))
  have hix12b : evalExpr (xAt b)
        (mkRoundEnv s k (((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV11 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV11 cur[a] cur[b] cur[c] cur[d])) := by
    simp only [xAt, evalExpr, litVal, hx11, htoNat_b, hg12b]
  have hv12 : evalExpr (rotlAt b 7)
        (mkRoundEnv s k (((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV11 cur[a] cur[b] cur[c] cur[d]))) =
      .ok (.u32 (qrV12 cur[a] cur[b] cur[c] cur[d])) :=
    rotlAt_eval _ _ b 7 hix12b (ofNat32_toNat 7 (by decide))
      (ofNat32_toNat (32 - 7) (by decide)) (by decide) (by decide)
  have e12 := roundArrSet F s k _ b _ _
    (by simp only [List.length_set]; exact hb) hb64 hv12
  -- `qrAt` in `qrV` form (unfolds the spec to the same values).
  have hqr : qrAt cur a b c d =
      (((cur.set a (qrV7 cur[a] cur[b] cur[c] cur[d])).set b
        (qrV12 cur[a] cur[b] cur[c] cur[d])).set c
        (qrV10 cur[a] cur[b] cur[c] cur[d])).set d
        (qrV9 cur[a] cur[b] cur[c] cur[d]) := by
    simp only [qrAt, hgeta0, hgetb0, hgetc0, hgetd0, qrStep, qrV1, qrV2,
      qrV3, qrV4, qrV5, qrV6, qrV7, qrV8, qrV9, qrV10, qrV11, qrV12]
  -- The eval-order chain is `qrAt`: same indices, distinct cells, so
  -- extensionality plus a case split on the read position (the five
  -- live cases peel to identical `qrV` values; the rest contradict
  -- the six pairwise-distinct hypotheses).
  have hbridge :
      ((((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
        (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
        (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
        (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
        (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
        (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
        (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
        (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
        (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
        (qrV10 cur[a] cur[b] cur[c] cur[d])).set b
        (qrV11 cur[a] cur[b] cur[c] cur[d])).set b
        (qrV12 cur[a] cur[b] cur[c] cur[d])) =
      qrAt cur a b c d := by
    -- `getElem?` form: no proof arguments, so `rw` on the read
    -- position is motive-clean and peels need no length side-goals
    -- (`getElem?_set_ne` takes only the disequality).
    rw [hqr]
    apply List.ext_getElem?
    intro i
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      by_cases hic : i = c <;> by_cases hid : i = d
    · exact absurd (hia.symm.trans hib) hab
    · exact absurd (hia.symm.trans hib) hab
    · exact absurd (hia.symm.trans hib) hab
    · exact absurd (hia.symm.trans hib) hab
    · exact absurd (hia.symm.trans hic) hac
    · exact absurd (hia.symm.trans hic) hac
    · exact absurd (hia.symm.trans hid) had
    · rw [hia]
      have sLa : (((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d]))[a]? =
          some (qrV7 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self (by simp only [List.length_set]; exact ha)
      have sRa : (cur.set a (qrV7 cur[a] cur[b] cur[c] cur[d]))[a]? =
          some (qrV7 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self ha
      simp only [List.getElem?_set_ne hab.symm, List.getElem?_set_ne hac.symm,
        List.getElem?_set_ne had.symm, sLa, sRa]
    · exact absurd (hib.symm.trans hic) hbc
    · exact absurd (hib.symm.trans hic) hbc
    · exact absurd (hib.symm.trans hid) hbd
    · rw [hib]
      -- LHS outermost is already the target cell: `sLb` fires with
      -- no peels (full-chain peels time out — factored out).
      have sLb : ((((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV11 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV12 cur[a] cur[b] cur[c] cur[d]))[b]? =
          some (qrV12 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self (by simp only [List.length_set]; exact hb)
      have sRb : ((cur.set a (qrV7 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV12 cur[a] cur[b] cur[c] cur[d]))[b]? =
          some (qrV12 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self (by simp only [List.length_set]; exact hb)
      rw [sLb]
      simp only [List.getElem?_set_ne hbd.symm, List.getElem?_set_ne hbc.symm,
        sRb]
    · exact absurd (hic.symm.trans hid) hcd
    · rw [hic]
      have sLc : ((((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d]))[c]? =
          some (qrV10 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self (by simp only [List.length_set]; exact hc)
      have sRc : (((cur.set a (qrV7 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV12 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d]))[c]? =
          some (qrV10 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self (by simp only [List.length_set]; exact hc)
      simp only [List.getElem?_set_ne hbc,
        List.getElem?_set_ne hcd.symm, sLc, sRc]
    · rw [hid]
      have sLd : (((((((((cur.set a (qrV1 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV2 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV3 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV4 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV5 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV6 cur[a] cur[b] cur[c] cur[d])).set a
          (qrV7 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV8 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d]))[d]? =
          some (qrV9 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self (by simp only [List.length_set]; exact hd)
      have sRd : ((((cur.set a (qrV7 cur[a] cur[b] cur[c] cur[d])).set b
          (qrV12 cur[a] cur[b] cur[c] cur[d])).set c
          (qrV10 cur[a] cur[b] cur[c] cur[d])).set d
          (qrV9 cur[a] cur[b] cur[c] cur[d]))[d]? =
          some (qrV9 cur[a] cur[b] cur[c] cur[d]) :=
        List.getElem?_set_self (by simp only [List.length_set]; exact hd)
      simp only [List.getElem?_set_ne hcd,
        List.getElem?_set_ne hbd, sLd, sRd]
    · have e1 : a ≠ i := Ne.symm hia
      have e2 : b ≠ i := Ne.symm hib
      have e3 : c ≠ i := Ne.symm hic
      have e4 : d ≠ i := Ne.symm hid
      simp only [List.getElem?_set_ne e1, List.getElem?_set_ne e2,
        List.getElem?_set_ne e3, List.getElem?_set_ne e4]
  -- Assemble: unfold, collapse the twelve `seq`s with the step facts
  -- (the conditional `seq_fallthrough` fed explicitly — as a `simp`
  -- side-condition it never fires), then rephrase the eval-order chain
  -- as `qrAt` via `hbridge` (which goes directly to `qrAt`; `hqr`
  -- is used inside `hbridge`'s case analysis).
  rw [qrFrag,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e1,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e2,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e3,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e4,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e5,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e6,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e7,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e8,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e9,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e10,
    evalStmtFuel_seq_fallthrough F _ _ _ _ e11,
    e12, hbridge]

/-! ### Double-round evaluation -/

/-- One double round evaluates to `chachaRound` (any fuel: loop-free).
    Each of the eight column/diagonal QRs applies `qrFrag_eval` at
    concrete indices (all `< 16 ≤ cur.length` by `omega` over the
    `qrAt_length` facts, `< 2 ^ 64` and pairwise-distinct by `decide`);
    the resulting eight-deep `qrAt` nest is `chachaRound` by `rfl`
    (which the final `rw` discharges). -/
theorem roundFrag_eval (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (h16 : 16 ≤ cur.length) :
    evalStmtFuel F roundFrag (mkRoundEnv s k cur) =
      .ok (mkRoundEnv s k (chachaRound cur), .fellThrough) := by
  have hL1 : (qrAt cur 0 4 8 12).length = cur.length :=
    qrAt_length _ _ _ _ _
  have hL2 : (qrAt (qrAt cur 0 4 8 12) 1 5 9 13).length = cur.length := by
    rw [qrAt_length, hL1]
  have hL3 : (qrAt (qrAt (qrAt cur 0 4 8 12) 1 5 9 13) 2 6 10 14).length
      = cur.length := by
    rw [qrAt_length, hL2]
  have hL4 : (qrAt (qrAt (qrAt (qrAt cur 0 4 8 12) 1 5 9 13) 2 6 10 14)
      3 7 11 15).length = cur.length := by
    rw [qrAt_length, hL3]
  have hL5 : (qrAt (qrAt (qrAt (qrAt (qrAt cur 0 4 8 12) 1 5 9 13)
      2 6 10 14) 3 7 11 15) 0 5 10 15).length = cur.length := by
    rw [qrAt_length, hL4]
  have hL6 : (qrAt (qrAt (qrAt (qrAt (qrAt (qrAt cur 0 4 8 12) 1 5 9 13)
      2 6 10 14) 3 7 11 15) 0 5 10 15) 1 6 11 12).length = cur.length := by
    rw [qrAt_length, hL5]
  have hL7 : (qrAt (qrAt (qrAt (qrAt (qrAt (qrAt (qrAt cur 0 4 8 12)
      1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15) 1 6 11 12)
      2 7 8 13).length = cur.length := by
    rw [qrAt_length, hL6]
  have q1 := qrFrag_eval F s k cur 0 4 8 12
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have q2 := qrFrag_eval F s k (qrAt cur 0 4 8 12) 1 5 9 13
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have q3 := qrFrag_eval F s k (qrAt (qrAt cur 0 4 8 12) 1 5 9 13)
      2 6 10 14
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have q4 := qrFrag_eval F s k (qrAt (qrAt (qrAt cur 0 4 8 12) 1 5 9 13)
      2 6 10 14) 3 7 11 15
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have q5 := qrFrag_eval F s k (qrAt (qrAt (qrAt (qrAt cur 0 4 8 12)
      1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have q6 := qrFrag_eval F s k (qrAt (qrAt (qrAt (qrAt (qrAt cur 0 4 8 12)
      1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15) 1 6 11 12
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have q7 := qrFrag_eval F s k (qrAt (qrAt (qrAt (qrAt (qrAt (qrAt cur
      0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15) 1 6 11 12)
      2 7 8 13
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have q8 := qrFrag_eval F s k (qrAt (qrAt (qrAt (qrAt (qrAt (qrAt
      (qrAt cur 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) 0 5 10 15)
      1 6 11 12) 2 7 8 13) 3 4 9 14
    ⟨by omega, by omega, by omega, by omega⟩
    ⟨by decide, by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  rw [roundFrag,
    evalStmtFuel_seq_fallthrough F _ _ _ _ q1,
    evalStmtFuel_seq_fallthrough F _ _ _ _ q2,
    evalStmtFuel_seq_fallthrough F _ _ _ _ q3,
    evalStmtFuel_seq_fallthrough F _ _ _ _ q4,
    evalStmtFuel_seq_fallthrough F _ _ _ _ q5,
    evalStmtFuel_seq_fallthrough F _ _ _ _ q6,
    evalStmtFuel_seq_fallthrough F _ _ _ _ q7,
    q8, chachaRound]

/-! ### Round-loop evaluation -/

/-- One loop iteration: a double round over `x`, then `r++` (any fuel:
    both steps are loop-free; the counter bump is unconditional
    `ofNat64_add_one` since `BitVec` wraps by definition). -/
theorem roundBody_eval (F : Nat) (s : List (BitVec 32)) (r : Nat)
    (cur : List (BitVec 32)) (h16 : 16 ≤ cur.length) :
    evalStmtFuel F roundBody (mkRoundEnv s r cur) =
      .ok (mkRoundEnv s (r + 1) (chachaRound cur), .fellThrough) := by
  have hfrag := roundFrag_eval F s r cur h16
  -- Unfold past the `.var`/`.lit` leaves to the `envLookup` match,
  -- then close with the round-env lookup (the `evalExpr`-level facts
  -- sit above the unfolded form and cannot fire).
  have huadd : evalExpr
      (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkRoundEnv s r (chachaRound cur)) =
      .ok (.u64 (BitVec.ofNat 64 (r + 1))) := by
    simp only [evalExpr, mkRoundEnv_r, litVal, ofNat64_add_one]
  have hupd : envUpdate (mkRoundEnv s r (chachaRound cur)) "r"
      (.u64 (BitVec.ofNat 64 (r + 1))) =
      some (mkRoundEnv s (r + 1) (chachaRound cur)) :=
    roundEnv_update_r s r (r + 1) (chachaRound cur)
  have hassign := evalStmtFuel_assign F "r" _ _ _ _ huadd hupd
  rw [roundBody, evalStmtFuel_seq_fallthrough F _ _ _ _ hfrag, hassign]

/-- The ten-double-round loop evaluates to `chachaRounds 10` (fuel
    induction mirroring `xorWhile_correct`; the invariant phrases the
    remaining rounds suffix-style since `chachaRounds` composes
    inside-out: `chachaRounds (10 - r) cur = chachaRounds 10 cur0`). -/
theorem roundWhile_correct (F : Nat) (s : List (BitVec 32))
    (cur0 : List (BitVec 32)) (r : Nat) (cur : List (BitVec 32))
    (hr : r ≤ 10) (h16 : 16 ≤ cur.length)
    (hcur : chachaRounds (10 - r) cur = chachaRounds 10 cur0)
    (hF : 10 - r ≤ F) :
    evalStmtFuel F roundWhile (mkRoundEnv s r cur) =
      .ok (mkRoundEnv s 10 (chachaRounds 10 cur0), .fellThrough) := by
  induction F generalizing r cur with
  | zero =>
    have hr10 : r = 10 := by omega
    subst hr10
    have hcond := roundCond_eval s 10 cur (by decide)
    have hcondF : evalExpr (.ult (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 10)))) (mkRoundEnv s 10 cur) =
        .ok (.b false) := by
      simpa using hcond
    have hdone : cur = chachaRounds 10 cur0 := hcur
    rw [hdone] at hcondF ⊢
    simp [roundWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcondF]
  | succ F ih =>
    by_cases hlt : r < 10
    · have hr64 : r < 2 ^ 64 := by omega
      have hcond := roundCond_eval s r cur hr64
      have hcondT : evalExpr (.ult (.var "r")
            (.lit (.u64 (BitVec.ofNat 64 10)))) (mkRoundEnv s r cur) =
          .ok (.b true) := by
        simpa [hlt] using hcond
      have hbody := roundBody_eval F s r cur h16
      have hstep : evalStmtFuel (F + 1) roundWhile (mkRoundEnv s r cur)
          = evalStmtFuel F roundWhile
            (mkRoundEnv s (r + 1) (chachaRound cur)) := by
        simp [roundWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcondT, hbody]
      rw [hstep]
      have hr' : r + 1 ≤ 10 := by omega
      have h16' : 16 ≤ (chachaRound cur).length := by
        rw [chachaRound_length]; exact h16
      have e1 : 10 - (r + 1) = 10 - r - 1 := by omega
      have e2 : 10 - r = (10 - r - 1) + 1 := by omega
      have hcur' : chachaRounds (10 - (r + 1)) (chachaRound cur) =
          chachaRounds 10 cur0 := by
        rw [e1, ← chachaRounds_succ, ← e2]
        exact hcur
      exact ih (r + 1) (chachaRound cur) hr' h16' hcur' (by omega)
    · have hr10 : r = 10 := by omega
      subst hr10
      have hcond := roundCond_eval s 10 cur (by decide)
      have hcondF : evalExpr (.ult (.var "r")
            (.lit (.u64 (BitVec.ofNat 64 10)))) (mkRoundEnv s 10 cur) =
          .ok (.b false) := by
        simpa using hcond
      have hdone : cur = chachaRounds 10 cur0 := hcur
      rw [hdone] at hcondF ⊢
      simp [roundWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondF]

/-! ### Add-back evaluation -/

/-- Add-phase env: the `i` counter consed over the post-round env
    (`r = 10` throughout; `x` is the rounded copy, `state` evolves). -/
def mkAddEnv (rnd : List (BitVec 32)) (i : Nat)
    (st : List (BitVec 32)) : Env :=
  [("i", .u64 (BitVec.ofNat 64 i)), ("r", .u64 (BitVec.ofNat 64 10)),
   ("x", .arr32 rnd), ("state", .arr32 st)]

theorem mkAddEnv_i (rnd : List (BitVec 32)) (i : Nat)
    (st : List (BitVec 32)) :
    envLookup (mkAddEnv rnd i st) "i" =
      some (.u64 (BitVec.ofNat 64 i)) := by
  simp [mkAddEnv, envLookup]

theorem mkAddEnv_x (rnd : List (BitVec 32)) (i : Nat)
    (st : List (BitVec 32)) :
    envLookup (mkAddEnv rnd i st) "x" = some (.arr32 rnd) := by
  simp [mkAddEnv, envLookup, show ("x" : String) ≠ "i" by decide,
    show ("x" : String) ≠ "r" by decide]

theorem mkAddEnv_state (rnd : List (BitVec 32)) (i : Nat)
    (st : List (BitVec 32)) :
    envLookup (mkAddEnv rnd i st) "state" = some (.arr32 st) := by
  simp [mkAddEnv, envLookup, show ("state" : String) ≠ "i" by decide,
    show ("state" : String) ≠ "r" by decide,
    show ("state" : String) ≠ "x" by decide]

/-- Updating `state` in an add env stays an add env. -/
theorem mkAddEnv_update_state (rnd : List (BitVec 32)) (i : Nat)
    (st st' : List (BitVec 32)) :
    envUpdate (mkAddEnv rnd i st) "state" (.arr32 st') =
      some (mkAddEnv rnd i st') := by
  simp [mkAddEnv, envUpdate, show ("state" : String) ≠ "i" by decide,
    show ("state" : String) ≠ "r" by decide,
    show ("state" : String) ≠ "x" by decide]

/-- Updating `i` in an add env stays an add env. -/
theorem mkAddEnv_update_i (rnd : List (BitVec 32)) (i i' : Nat)
    (st : List (BitVec 32)) :
    envUpdate (mkAddEnv rnd i st) "i" (.u64 (BitVec.ofNat 64 i')) =
      some (mkAddEnv rnd i' st) := by
  simp [mkAddEnv, envUpdate]

/-- The add-back condition reads `i` against the literal bound `16`. -/
theorem addCond_eval (rnd : List (BitVec 32)) (i : Nat)
    (st : List (BitVec 32)) (h : i < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.lit (.u64 (BitVec.ofNat 64 16))))
        (mkAddEnv rnd i st) =
      .ok (.b (decide (i < 16))) := by
  have hi := mkAddEnv_i rnd i st
  have h16 : (BitVec.ofNat 64 16).toNat = 16 := ofNat64_toNat 16 (by decide)
  simp [evalExpr, hi, litVal, ofNat64_ult i _ h, h16]

/-- Add-back only touches visited cells: reads at or past the frontier
    see the original state (induction on the visited prefix; the fresh
    write is at `k < j`, hence invisible). -/
theorem addBackList_get_untouched (orig rnd : List (BitVec 32))
    (n j : Nat) (h : n ≤ j) :
    (addBackList orig rnd n)[j]? = orig[j]? := by
  induction n generalizing j with
  | zero => rfl
  | succ k ih =>
    have hkj : k ≠ j := by omega
    have hkj' : k ≤ j := by omega
    rw [addBackList_succ, List.getElem?_set_ne hkj, ih j hkj']

/-- One add-back word-store (any fuel: single step). -/
theorem addArrSet (F : Nat) (rnd : List (BitVec 32)) (i : Nat)
    (st : List (BitVec 32)) (ve : CExpr) (v : BitVec 32)
    (hi : i < st.length) (hi64 : i < 2 ^ 64)
    (hv : evalExpr ve (mkAddEnv rnd i st) = .ok (.u32 v)) :
    evalStmtFuel F (.arrSet "state" (.var "i") ve) (mkAddEnv rnd i st) =
      .ok (mkAddEnv rnd i (st.set i v), .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat i hi64
  have hiv : evalExpr (.var "i") (mkAddEnv rnd i st) =
      .ok (.u64 (BitVec.ofNat 64 i)) := by
    simp [evalExpr, mkAddEnv_i]
  have harr := mkAddEnv_state rnd i st
  have hget : st[(BitVec.ofNat 64 i).toNat]? = some st[i] := by
    rw [htoNat]; exact List.getElem?_eq_getElem hi
  have hu : envUpdate (mkAddEnv rnd i st) "state"
      (.arr32 (st.set (BitVec.ofNat 64 i).toNat v)) =
      some (mkAddEnv rnd i (st.set i v)) := by
    rw [htoNat]; exact mkAddEnv_update_state rnd i st (st.set i v)
  exact evalStmtFuel_arrSet F "state" (.var "i") ve _ _ v st st[i] _ hiv hv
    harr hget hu

/-- One add-back iteration: `state[i] += x[i]; i++` (any fuel: both
    steps are loop-free). -/
theorem addBody_eval (F : Nat) (rnd : List (BitVec 32)) (i : Nat)
    (st : List (BitVec 32))
    (his : i < st.length) (hix : i < rnd.length) (hi64 : i < 2 ^ 64) :
    evalStmtFuel F addBody (mkAddEnv rnd i st) =
      .ok (mkAddEnv rnd (i + 1) (st.set i (st[i] + rnd[i])),
        .fellThrough) := by
  have htoNat : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat i hi64
  have hgets : st[i]? = some st[i] := List.getElem?_eq_getElem his
  have hgetx : rnd[i]? = some rnd[i] := List.getElem?_eq_getElem hix
  -- Raw `.idxu` scrutinees (no shielding def like `xAt`) are preempted
  -- by `evalExpr`'s equation lemmas, so `evalExpr`-level facts cannot
  -- fire: close at the unfolded `envLookup` level instead.
  have hv : evalExpr
      (.uadd (.idxu "state" (.var "i")) (.idxu "x" (.var "i")))
      (mkAddEnv rnd i st) = .ok (.u32 (st[i] + rnd[i])) := by
    simp only [evalExpr, mkAddEnv_state, mkAddEnv_x, mkAddEnv_i, htoNat,
      hgets, hgetx]
  have harr := addArrSet F rnd i st _ _ his hi64 hv
  have huaddi : evalExpr (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkAddEnv rnd i (st.set i (st[i] + rnd[i]))) =
      .ok (.u64 (BitVec.ofNat 64 (i + 1))) := by
    simp only [evalExpr, mkAddEnv_i, litVal, ofNat64_add_one]
  have hupdi : envUpdate (mkAddEnv rnd i (st.set i (st[i] + rnd[i]))) "i"
      (.u64 (BitVec.ofNat 64 (i + 1))) =
      some (mkAddEnv rnd (i + 1) (st.set i (st[i] + rnd[i]))) :=
    mkAddEnv_update_i rnd i (i + 1) (st.set i (st[i] + rnd[i]))
  have hassign := evalStmtFuel_assign F "i" _ _ _ _ huaddi hupdi
  rw [addBody, evalStmtFuel_seq_fallthrough F _ _ _ _ harr, hassign]

/-- The add-back loop evaluates to `addBackList orig rnd 16` (fuel
    induction mirroring `roundWhile_correct`; the step pushes the
    just-written cell through `addBackList_succ`, grounding both
    reads via `addBackList_get_untouched` and the length facts). -/
theorem addWhile_correct (F : Nat) (rnd orig : List (BitVec 32))
    (i : Nat) (st : List (BitVec 32))
    (hi : i ≤ 16) (h16o : 16 ≤ orig.length) (h16r : 16 ≤ rnd.length)
    (hst : st = addBackList orig rnd i)
    (hF : 16 - i ≤ F) :
    evalStmtFuel F addWhile (mkAddEnv rnd i st) =
      .ok (mkAddEnv rnd 16 (addBackList orig rnd 16), .fellThrough) := by
  induction F generalizing i st with
  | zero =>
    have hi16 : i = 16 := by omega
    subst hi16
    have hcond := addCond_eval rnd 16 st (by decide)
    have hcondF : evalExpr (.ult (.var "i")
          (.lit (.u64 (BitVec.ofNat 64 16)))) (mkAddEnv rnd 16 st) =
        .ok (.b false) := by
      simpa using hcond
    rw [hst] at hcondF ⊢
    simp [addWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcondF]
  | succ F ih =>
    by_cases hlt : i < 16
    · have hi64 : i < 2 ^ 64 := by omega
      have hcond := addCond_eval rnd i st hi64
      have hcondT : evalExpr (.ult (.var "i")
            (.lit (.u64 (BitVec.ofNat 64 16)))) (mkAddEnv rnd i st) =
          .ok (.b true) := by
        simpa [hlt] using hcond
      have his : i < st.length := by
        rw [hst, addBackList_length]; omega
      have hix : i < rnd.length := by omega
      have hbody := addBody_eval F rnd i st his hix hi64
      have hstep : evalStmtFuel (F + 1) addWhile (mkAddEnv rnd i st)
          = evalStmtFuel F addWhile
            (mkAddEnv rnd (i + 1) (st.set i (st[i] + rnd[i]))) := by
        simp [addWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondT, hbody]
      rw [hstep]
      have hAL : (addBackList orig rnd i).length = orig.length :=
        addBackList_length _ _ _
      have hii : i < (addBackList orig rnd i).length := by omega
      have hABLii : (addBackList orig rnd i)[i] = orig[i] := by
        have hunt := addBackList_get_untouched orig rnd i i (Nat.le_refl i)
        have hget := List.getElem?_eq_getElem hii
        have hgo := List.getElem?_eq_getElem (show i < orig.length by omega)
        rw [hget, hgo] at hunt
        exact Option.some_inj.mp hunt
      have hrnd : rnd[i] = rnd[i]?.getD 0 :=
        (congrArg (·.getD 0)
          (List.getElem?_eq_getElem (show i < rnd.length by omega))).symm
      -- `st` is a generalized variable occurring dependently (`st[i]`),
      -- so `rw [hst]` is ill-moded: `subst` it away instead.
      subst hst
      have hst' : (addBackList orig rnd i).set i
          ((addBackList orig rnd i)[i] + rnd[i]) =
          addBackList orig rnd (i + 1) := by
        have horig : orig[i] = orig[i]?.getD 0 :=
          (congrArg (·.getD 0)
            (List.getElem?_eq_getElem
              (show i < orig.length by omega))).symm
        rw [hABLii, hrnd, horig, addBackList_succ]
      exact ih (i + 1) ((addBackList orig rnd i).set i
        ((addBackList orig rnd i)[i] + rnd[i])) (by omega)
        hst' (by omega)

    · have hi16 : i = 16 := by omega
      subst hi16
      have hcond := addCond_eval rnd 16 st (by decide)
      have hcondF : evalExpr (.ult (.var "i")
            (.lit (.u64 (BitVec.ofNat 64 16)))) (mkAddEnv rnd 16 st) =
          .ok (.b false) := by
        simpa using hcond
      rw [hst] at hcondF ⊢
      simp [addWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondF]

/-! ### Whole-function correctness -/

/-- Forward correctness at any sufficient fuel (mirrors
    `evalFuncFuel_xorN`: the two `let`s bridge by `rfl` to the round
    and add envs, the loops plug in at handler level by unfolding). -/
theorem evalFuncFuel_chachaBlock (F : Nat) (s : List (BitVec 32))
    (h16 : 16 ≤ s.length) (hF : 16 ≤ F) :
    evalFuncFuel F chachaBlockFunc [.arr32 s] = chachaBlockFwd s := by
  cases F with
  | zero => exact False.elim (by omega)
  | succ F =>
    have h16s : 16 ≤ s.length := h16
    have hcur0 : chachaRounds (10 - 0) s = chachaRounds 10 s := by
      rw [Nat.sub_zero]
    have h16r : 16 ≤ (chachaRounds 10 s).length := by
      rw [chachaRounds_length]; exact h16s
    have hst0 : s = addBackList s (chachaRounds 10 s) 0 := rfl
    have hvarRet : evalExpr (.var "state")
        (mkAddEnv (chachaRounds 10 s) 16
          (addBackList s (chachaRounds 10 s) 16)) =
        .ok (.arr32 (addBackList s (chachaRounds 10 s) 16)) := by
      simp [evalExpr, mkAddEnv_state]
    -- Explicit assembly: the mega-`simp` never engages (the `let`
    -- envs do not reduce to the bridge shapes under `simp`), so bind,
    -- collapse the four `seq`s with the step facts, and return.
    -- Literal args list (constructor form, since `{...}` will not
    -- parse here): after `chachaBlockFunc` unfolds, the projection
    -- form `chachaBlockFunc.args` is gone.
    have hbind : bindArgs
        [Param.mk "state" (.array (.u 32) 16) (.mutBorrow 0)]
        [.arr32 s] = some [("state", .arr32 s)] := rfl
    have hvarX : evalExpr (.var "state") [("state", .arr32 s)] =
        .ok (.arr32 s) := by
      simp [evalExpr, envLookup]
    have hletX := evalStmtFuel_let_ (F + 1) "x" (.array (.u 32) 16)
      (.var "state") [("state", .arr32 s)] (.arr32 s) hvarX
    have henvR : envExtend [("state", .arr32 s)] "x" (.arr32 s) =
        [("x", .arr32 s), ("state", .arr32 s)] := rfl
    have hvarR : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("x", .arr32 s), ("state", .arr32 s)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletR := evalStmtFuel_let_ (F + 1) "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("x", .arr32 s), ("state", .arr32 s)]
      (.u64 (BitVec.ofNat 64 0)) hvarR
    have henvR2 : envExtend [("x", .arr32 s), ("state", .arr32 s)] "r"
        (.u64 (BitVec.ofNat 64 0)) = mkRoundEnv s 0 s := rfl
    have hround' : evalStmtFuel (F + 1) roundWhile (mkRoundEnv s 0 s) =
        .ok (mkRoundEnv s 10 (chachaRounds 10 s), .fellThrough) :=
      roundWhile_correct (F + 1) s s 0 s (Nat.zero_le _) h16s hcur0
        (by omega)
    have hvarI : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (mkRoundEnv s 10 (chachaRounds 10 s)) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletI := evalStmtFuel_let_ (F + 1) "i" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (mkRoundEnv s 10 (chachaRounds 10 s))
      (.u64 (BitVec.ofNat 64 0)) hvarI
    have henvA : envExtend (mkRoundEnv s 10 (chachaRounds 10 s)) "i"
        (.u64 (BitVec.ofNat 64 0)) =
        mkAddEnv (chachaRounds 10 s) 0 s := rfl
    have hadd' : evalStmtFuel (F + 1) addWhile
        (mkAddEnv (chachaRounds 10 s) 0 s) =
        .ok (mkAddEnv (chachaRounds 10 s) 16
          (addBackList s (chachaRounds 10 s) 16), .fellThrough) :=
      addWhile_correct (F + 1) (chachaRounds 10 s) s 0 s (Nat.zero_le _)
        h16s h16r hst0 (by omega)
    have hret' : evalStmtFuel (F + 1) (.return_ (.var "state"))
        (mkAddEnv (chachaRounds 10 s) 16
          (addBackList s (chachaRounds 10 s) 16)) =
        .ok (mkAddEnv (chachaRounds 10 s) 16
          (addBackList s (chachaRounds 10 s) 16),
          .returned (.arr32 (addBackList s (chachaRounds 10 s) 16))) :=
      evalStmtFuel_return _ _ _ _ hvarRet
    simp only [evalFuncFuel, chachaBlockFunc, hbind]
    rw [evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletX, henvR,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletR, henvR2,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hround',
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletI, henvA,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hadd', hret']
    simp [chachaBlockFwd, h16]

/-- `emit_correct` for `chacha20_block` at the default fuel. -/
theorem emit_correct_chachaBlock (s : List (BitVec 32))
    (h16 : 16 ≤ s.length) (hfuel : 16 ≤ EVAL_FUEL) :
    evalFunc chachaBlockFunc [.arr32 s] = chachaBlockFwd s :=
  evalFuncFuel_chachaBlock EVAL_FUEL s h16 hfuel

/-! ### Out-of-bounds legs -/

/-- `arrSet` whose value errors propagates it (any fuel; mirrors
    `evalStmtFuel_arrSet_oob`, which covers the write-missing case —
    every K4 failure hits a read first, so this is the one we need). -/
theorem evalStmtFuel_arrSet_err (F : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (n : BitVec 64) (e : Panic)
    (hi : evalExpr ie ρ = .ok (.u64 n))
    (hv : evalExpr ve ρ = .error e) :
    evalStmtFuel F (.arrSet x ie ve) ρ = .error e := by
  cases F <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv]

/-- The first column QR errors when the state is short (`≤ 12` words):
    with `a = 0` missing nothing runs; with `b = 4` missing the first
    store fails; otherwise the first store succeeds and the second
    fails reading `d = 12`. -/
theorem qrFrag1_oob (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (h : cur.length ≤ 12) :
    evalStmtFuel F (qrFrag 0 4 8 12) (mkRoundEnv s k cur) =
      .error .OOB := by
  by_cases h0 : cur.length = 0
  · -- Length 0: the first store fails reading `a = 0`.
    have hgeta : cur[0]? = none := List.getElem?_eq_none (by omega)
    have htoNat0 : (BitVec.ofNat 64 0).toNat = 0 :=
      ofNat64_toNat 0 (by decide)
    have hxa : evalExpr (xAt 0) (mkRoundEnv s k cur) = .error .OOB := by
      simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat0, hgeta]
    have hval : evalExpr (.uadd (xAt 0) (xAt 4)) (mkRoundEnv s k cur) =
        .error .OOB := by
      simp only [evalExpr, hxa]
    have hidx : evalExpr (atU64 0) (mkRoundEnv s k cur) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [atU64, evalExpr, litVal]
    have herr : evalStmtFuel F
        (.arrSet "x" (atU64 0) (.uadd (xAt 0) (xAt 4)))
        (mkRoundEnv s k cur) = .error .OOB :=
      evalStmtFuel_arrSet_err F "x" _ _ _ _ _ hidx hval
    rw [qrFrag, evalStmtFuel_seq_err F _ _ _ _ herr]
  · by_cases h4 : cur.length ≤ 4
    · -- Length 1–4: `a = 0` reads fine, the first store fails on `b`.
      have htoNat0 : (BitVec.ofNat 64 0).toNat = 0 :=
        ofNat64_toNat 0 (by decide)
      have htoNat4 : (BitVec.ofNat 64 4).toNat = 4 :=
        ofNat64_toNat 4 (by decide)
      have hgeta : cur[0]? = some cur[0] :=
        List.getElem?_eq_getElem (by omega)
      have hgetb : cur[4]? = none := List.getElem?_eq_none (by omega)
      have hxa0 : evalExpr (xAt 0) (mkRoundEnv s k cur) =
          .ok (.u32 cur[0]) := by
        simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat0, hgeta]
      have hxb4 : evalExpr (xAt 4) (mkRoundEnv s k cur) = .error .OOB := by
        simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat4, hgetb]
      have hval : evalExpr (.uadd (xAt 0) (xAt 4)) (mkRoundEnv s k cur) =
          .error .OOB := by
        simp only [evalExpr, hxa0, hxb4]
      have hidx : evalExpr (atU64 0) (mkRoundEnv s k cur) =
          .ok (.u64 (BitVec.ofNat 64 0)) := by
        simp [atU64, evalExpr, litVal]
      have herr : evalStmtFuel F
          (.arrSet "x" (atU64 0) (.uadd (xAt 0) (xAt 4)))
          (mkRoundEnv s k cur) = .error .OOB :=
        evalStmtFuel_arrSet_err F "x" _ _ _ _ _ hidx hval
      rw [qrFrag, evalStmtFuel_seq_err F _ _ _ _ herr]
    · -- Length 5–12: the first store succeeds, the second fails on `d`.
      have htoNat0 : (BitVec.ofNat 64 0).toNat = 0 :=
        ofNat64_toNat 0 (by decide)
      have htoNat4 : (BitVec.ofNat 64 4).toNat = 4 :=
        ofNat64_toNat 4 (by decide)
      have hxa0 : evalExpr (xAt 0) (mkRoundEnv s k cur) =
          .ok (.u32 cur[0]) := by
        simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat0,
          List.getElem?_eq_getElem (show 0 < cur.length by omega)]
      have hxb4 : evalExpr (xAt 4) (mkRoundEnv s k cur) =
          .ok (.u32 cur[4]) := by
        simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat4,
          List.getElem?_eq_getElem (show 4 < cur.length by omega)]
      have hv1 : evalExpr (.uadd (xAt 0) (xAt 4)) (mkRoundEnv s k cur) =
          .ok (.u32 (cur[0] + cur[4])) := by
        simp only [evalExpr, hxa0, hxb4]
      have h1 := roundArrSet F s k cur 0 _ _ (by omega) (by decide) hv1
      have htoNat12 : (BitVec.ofNat 64 12).toNat = 12 :=
        ofNat64_toNat 12 (by decide)
      have hgetd : ((cur.set 0 (cur[0] + cur[4]))[12]? = none) := by
        rw [List.getElem?_set_ne (by decide : (0 : Nat) ≠ 12)]
        exact List.getElem?_eq_none (by omega)
      have hxd : evalExpr (xAt 12)
          (mkRoundEnv s k (cur.set 0 (cur[0] + cur[4]))) =
          .error .OOB := by
        simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat12, hgetd]
      have hval2 : evalExpr (.bxor (xAt 12) (xAt 0))
          (mkRoundEnv s k (cur.set 0 (cur[0] + cur[4]))) =
          .error .OOB := by
        simp only [evalExpr, hxd]
      have hidx2 : evalExpr (atU64 12)
          (mkRoundEnv s k (cur.set 0 (cur[0] + cur[4]))) =
          .ok (.u64 (BitVec.ofNat 64 12)) := by
        simp [atU64, evalExpr, litVal]
      have herr2 : evalStmtFuel F
          (.arrSet "x" (atU64 12) (.bxor (xAt 12) (xAt 0)))
          (mkRoundEnv s k (cur.set 0 (cur[0] + cur[4]))) =
          .error .OOB :=
        evalStmtFuel_arrSet_err F "x" _ _ _ _ _ hidx2 hval2
      rw [qrFrag, evalStmtFuel_seq_fallthrough F _ _ _ _ h1,
        evalStmtFuel_seq_err F _ _ _ _ herr2]

/-- The second column QR errors at length exactly 13: its first store
    succeeds (`1, 5 < 13`), the second fails reading `d = 13`. -/
theorem qrFrag2_oob (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (h : cur.length = 13) :
    evalStmtFuel F (qrFrag 1 5 9 13) (mkRoundEnv s k cur) =
      .error .OOB := by
  have htoNat1 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have htoNat5 : (BitVec.ofNat 64 5).toNat = 5 := ofNat64_toNat 5 (by decide)
  have hxa1 : evalExpr (xAt 1) (mkRoundEnv s k cur) =
      .ok (.u32 cur[1]) := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat1,
      List.getElem?_eq_getElem (show 1 < cur.length by omega)]
  have hxb5 : evalExpr (xAt 5) (mkRoundEnv s k cur) =
      .ok (.u32 cur[5]) := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat5,
      List.getElem?_eq_getElem (show 5 < cur.length by omega)]
  have hv1 : evalExpr (.uadd (xAt 1) (xAt 5)) (mkRoundEnv s k cur) =
      .ok (.u32 (cur[1] + cur[5])) := by
    simp only [evalExpr, hxa1, hxb5]
  have h1 := roundArrSet F s k cur 1 _ _ (by omega) (by decide) hv1
  have htoNat13 : (BitVec.ofNat 64 13).toNat = 13 :=
    ofNat64_toNat 13 (by decide)
  have hgetd : ((cur.set 1 (cur[1] + cur[5]))[13]? = none) := by
    rw [List.getElem?_set_ne (by decide : (1 : Nat) ≠ 13)]
    exact List.getElem?_eq_none (by omega)
  have hxd : evalExpr (xAt 13) (mkRoundEnv s k (cur.set 1 (cur[1] + cur[5]))) =
      .error .OOB := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat13, hgetd]
  have hval2 : evalExpr (.bxor (xAt 13) (xAt 1))
      (mkRoundEnv s k (cur.set 1 (cur[1] + cur[5]))) = .error .OOB := by
    simp only [evalExpr, hxd]
  have hidx2 : evalExpr (atU64 13)
      (mkRoundEnv s k (cur.set 1 (cur[1] + cur[5]))) =
      .ok (.u64 (BitVec.ofNat 64 13)) := by
    simp [atU64, evalExpr, litVal]
  have herr2 : evalStmtFuel F
      (.arrSet "x" (atU64 13) (.bxor (xAt 13) (xAt 1)))
      (mkRoundEnv s k (cur.set 1 (cur[1] + cur[5]))) = .error .OOB :=
    evalStmtFuel_arrSet_err F "x" _ _ _ _ _ hidx2 hval2
  rw [qrFrag, evalStmtFuel_seq_fallthrough F _ _ _ _ h1,
    evalStmtFuel_seq_err F _ _ _ _ herr2]

/-- The third column QR errors at length exactly 14 (same shape). -/
theorem qrFrag3_oob (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (h : cur.length = 14) :
    evalStmtFuel F (qrFrag 2 6 10 14) (mkRoundEnv s k cur) =
      .error .OOB := by
  have htoNat2 : (BitVec.ofNat 64 2).toNat = 2 := ofNat64_toNat 2 (by decide)
  have htoNat6 : (BitVec.ofNat 64 6).toNat = 6 := ofNat64_toNat 6 (by decide)
  have hxa2 : evalExpr (xAt 2) (mkRoundEnv s k cur) =
      .ok (.u32 cur[2]) := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat2,
      List.getElem?_eq_getElem (show 2 < cur.length by omega)]
  have hxb6 : evalExpr (xAt 6) (mkRoundEnv s k cur) =
      .ok (.u32 cur[6]) := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat6,
      List.getElem?_eq_getElem (show 6 < cur.length by omega)]
  have hv1 : evalExpr (.uadd (xAt 2) (xAt 6)) (mkRoundEnv s k cur) =
      .ok (.u32 (cur[2] + cur[6])) := by
    simp only [evalExpr, hxa2, hxb6]
  have h1 := roundArrSet F s k cur 2 _ _ (by omega) (by decide) hv1
  have htoNat14 : (BitVec.ofNat 64 14).toNat = 14 :=
    ofNat64_toNat 14 (by decide)
  have hgetd : ((cur.set 2 (cur[2] + cur[6]))[14]? = none) := by
    rw [List.getElem?_set_ne (by decide : (2 : Nat) ≠ 14)]
    exact List.getElem?_eq_none (by omega)
  have hxd : evalExpr (xAt 14) (mkRoundEnv s k (cur.set 2 (cur[2] + cur[6]))) =
      .error .OOB := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat14, hgetd]
  have hval2 : evalExpr (.bxor (xAt 14) (xAt 2))
      (mkRoundEnv s k (cur.set 2 (cur[2] + cur[6]))) = .error .OOB := by
    simp only [evalExpr, hxd]
  have hidx2 : evalExpr (atU64 14)
      (mkRoundEnv s k (cur.set 2 (cur[2] + cur[6]))) =
      .ok (.u64 (BitVec.ofNat 64 14)) := by
    simp [atU64, evalExpr, litVal]
  have herr2 : evalStmtFuel F
      (.arrSet "x" (atU64 14) (.bxor (xAt 14) (xAt 2)))
      (mkRoundEnv s k (cur.set 2 (cur[2] + cur[6]))) = .error .OOB :=
    evalStmtFuel_arrSet_err F "x" _ _ _ _ _ hidx2 hval2
  rw [qrFrag, evalStmtFuel_seq_fallthrough F _ _ _ _ h1,
    evalStmtFuel_seq_err F _ _ _ _ herr2]

/-- The fourth column QR errors at length exactly 15 (same shape). -/
theorem qrFrag4_oob (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (h : cur.length = 15) :
    evalStmtFuel F (qrFrag 3 7 11 15) (mkRoundEnv s k cur) =
      .error .OOB := by
  have htoNat3 : (BitVec.ofNat 64 3).toNat = 3 := ofNat64_toNat 3 (by decide)
  have htoNat7 : (BitVec.ofNat 64 7).toNat = 7 := ofNat64_toNat 7 (by decide)
  have hxa3 : evalExpr (xAt 3) (mkRoundEnv s k cur) =
      .ok (.u32 cur[3]) := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat3,
      List.getElem?_eq_getElem (show 3 < cur.length by omega)]
  have hxb7 : evalExpr (xAt 7) (mkRoundEnv s k cur) =
      .ok (.u32 cur[7]) := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat7,
      List.getElem?_eq_getElem (show 7 < cur.length by omega)]
  have hv1 : evalExpr (.uadd (xAt 3) (xAt 7)) (mkRoundEnv s k cur) =
      .ok (.u32 (cur[3] + cur[7])) := by
    simp only [evalExpr, hxa3, hxb7]
  have h1 := roundArrSet F s k cur 3 _ _ (by omega) (by decide) hv1
  have htoNat15 : (BitVec.ofNat 64 15).toNat = 15 :=
    ofNat64_toNat 15 (by decide)
  have hgetd : ((cur.set 3 (cur[3] + cur[7]))[15]? = none) := by
    rw [List.getElem?_set_ne (by decide : (3 : Nat) ≠ 15)]
    exact List.getElem?_eq_none (by omega)
  have hxd : evalExpr (xAt 15) (mkRoundEnv s k (cur.set 3 (cur[3] + cur[7]))) =
      .error .OOB := by
    simp only [xAt, evalExpr, litVal, mkRoundEnv_x, htoNat15, hgetd]
  have hval2 : evalExpr (.bxor (xAt 15) (xAt 3))
      (mkRoundEnv s k (cur.set 3 (cur[3] + cur[7]))) = .error .OOB := by
    simp only [evalExpr, hxd]
  have hidx2 : evalExpr (atU64 15)
      (mkRoundEnv s k (cur.set 3 (cur[3] + cur[7]))) =
      .ok (.u64 (BitVec.ofNat 64 15)) := by
    simp [atU64, evalExpr, litVal]
  have herr2 : evalStmtFuel F
      (.arrSet "x" (atU64 15) (.bxor (xAt 15) (xAt 3)))
      (mkRoundEnv s k (cur.set 3 (cur[3] + cur[7]))) = .error .OOB :=
    evalStmtFuel_arrSet_err F "x" _ _ _ _ _ hidx2 hval2
  rw [qrFrag, evalStmtFuel_seq_fallthrough F _ _ _ _ h1,
    evalStmtFuel_seq_err F _ _ _ _ herr2]

/-- A short state errors in the first column QR touching a missing
    cell (`≤ 12`: the first; `13`/`14`/`15`: the second/third/fourth
    after the earlier ones succeed via `qrFrag_eval`). -/
theorem roundFrag_oob (F : Nat) (s : List (BitVec 32)) (k : Nat)
    (cur : List (BitVec 32)) (hshort : cur.length < 16) :
    evalStmtFuel F roundFrag (mkRoundEnv s k cur) = .error .OOB := by
  have hcases : cur.length ≤ 12 ∨ cur.length = 13 ∨ cur.length = 14 ∨
      cur.length = 15 := by omega
  obtain h|h|h|h := hcases
  · have herr := qrFrag1_oob F s k cur h
    rw [roundFrag, evalStmtFuel_seq_err F _ _ _ _ herr]
  · have q1 := qrFrag_eval F s k cur 0 4 8 12
      ⟨by omega, by omega, by omega, by omega⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    have herr := qrFrag2_oob F s k (qrAt cur 0 4 8 12) (by
      rw [qrAt_length]; omega)
    rw [roundFrag, evalStmtFuel_seq_fallthrough F _ _ _ _ q1,
      evalStmtFuel_seq_err F _ _ _ _ herr]
  · have hL1 : (qrAt cur 0 4 8 12).length = cur.length :=
      qrAt_length _ _ _ _ _
    have q1 := qrFrag_eval F s k cur 0 4 8 12
      ⟨by omega, by omega, by omega, by omega⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    have q2 := qrFrag_eval F s k (qrAt cur 0 4 8 12) 1 5 9 13
      ⟨by omega, by omega, by omega, by omega⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    have herr := qrFrag3_oob F s k
      (qrAt (qrAt cur 0 4 8 12) 1 5 9 13) (by rw [qrAt_length, hL1]; omega)
    rw [roundFrag, evalStmtFuel_seq_fallthrough F _ _ _ _ q1,
      evalStmtFuel_seq_fallthrough F _ _ _ _ q2,
      evalStmtFuel_seq_err F _ _ _ _ herr]
  · have hL1 : (qrAt cur 0 4 8 12).length = cur.length :=
      qrAt_length _ _ _ _ _
    have hL2 : (qrAt (qrAt cur 0 4 8 12) 1 5 9 13).length = cur.length := by
      rw [qrAt_length, hL1]
    have q1 := qrFrag_eval F s k cur 0 4 8 12
      ⟨by omega, by omega, by omega, by omega⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    have q2 := qrFrag_eval F s k (qrAt cur 0 4 8 12) 1 5 9 13
      ⟨by omega, by omega, by omega, by omega⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    have q3 := qrFrag_eval F s k (qrAt (qrAt cur 0 4 8 12) 1 5 9 13)
        2 6 10 14
      ⟨by omega, by omega, by omega, by omega⟩
      ⟨by decide, by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    have herr := qrFrag4_oob F s k
      (qrAt (qrAt (qrAt cur 0 4 8 12) 1 5 9 13) 2 6 10 14) (by
        rw [qrAt_length, hL2]; omega)
    rw [roundFrag, evalStmtFuel_seq_fallthrough F _ _ _ _ q1,
      evalStmtFuel_seq_fallthrough F _ _ _ _ q2,
      evalStmtFuel_seq_fallthrough F _ _ _ _ q3,
      evalStmtFuel_seq_err F _ _ _ _ herr]

/-- One loop iteration on a short state errors in the double round
    (the trailing `r++` never runs). -/
theorem roundBody_oob (F : Nat) (s : List (BitVec 32)) (r : Nat)
    (cur : List (BitVec 32)) (hshort : cur.length < 16) :
    evalStmtFuel F roundBody (mkRoundEnv s r cur) = .error .OOB := by
  have herr := roundFrag_oob F s r cur hshort
  rw [roundBody, evalStmtFuel_seq_err F _ _ _ _ herr]

/-- The round loop on a short state errors on entry (`r = 0 < 10`,
    so the condition holds and the first body runs at fuel `F`). -/
theorem roundWhile_oob (F : Nat) (s : List (BitVec 32))
    (cur : List (BitVec 32)) (hshort : cur.length < 16) :
    evalStmtFuel (F + 1) roundWhile (mkRoundEnv s 0 cur) =
      .error .OOB := by
  have hcond := roundCond_eval s 0 cur (by decide)
  have hcondT : evalExpr (.ult (.var "r")
        (.lit (.u64 (BitVec.ofNat 64 10)))) (mkRoundEnv s 0 cur) =
      .ok (.b true) := by
    simpa using hcond
  have hbodyErr : evalStmtFuel F roundBody (mkRoundEnv s 0 cur) =
      .error .OOB :=
    roundBody_oob F s 0 cur hshort
  simp [roundWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
    hcondT, hbodyErr]

/-- OOB corollary: a short input state fails loudly (mirrors
    `evalFuncFuel_xorN_oob`; needs one fuel unit to enter the loop). -/
theorem evalFuncFuel_chachaBlock_oob (F : Nat) (s : List (BitVec 32))
    (hshort : s.length < 16) (hF : 1 ≤ F) :
    evalFuncFuel F chachaBlockFunc [.arr32 s] = .error .OOB := by
  cases F with
  | zero => exact False.elim (by omega)
  | succ F =>
    have hbind : bindArgs
        [Param.mk "state" (.array (.u 32) 16) (.mutBorrow 0)]
        [.arr32 s] = some [("state", .arr32 s)] := rfl
    have hvarX : evalExpr (.var "state") [("state", .arr32 s)] =
        .ok (.arr32 s) := by
      simp [evalExpr, envLookup]
    have hletX := evalStmtFuel_let_ (F + 1) "x" (.array (.u 32) 16)
      (.var "state") [("state", .arr32 s)] (.arr32 s) hvarX
    have henvR : envExtend [("state", .arr32 s)] "x" (.arr32 s) =
        [("x", .arr32 s), ("state", .arr32 s)] := rfl
    have hvarR : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("x", .arr32 s), ("state", .arr32 s)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletR := evalStmtFuel_let_ (F + 1) "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("x", .arr32 s), ("state", .arr32 s)]
      (.u64 (BitVec.ofNat 64 0)) hvarR
    have henvR2 : envExtend [("x", .arr32 s), ("state", .arr32 s)] "r"
        (.u64 (BitVec.ofNat 64 0)) = mkRoundEnv s 0 s := rfl
    have hroundErr : evalStmtFuel (F + 1) roundWhile (mkRoundEnv s 0 s) =
        .error .OOB :=
      roundWhile_oob F s s hshort
    simp only [evalFuncFuel, chachaBlockFunc, hbind]
    rw [evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletX, henvR,
      evalStmtFuel_seq_fallthrough (F + 1) _ _ _ _ hletR, henvR2,
      evalStmtFuel_seq_err (F + 1) _ _ _ _ hroundErr]
