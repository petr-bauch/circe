/-
Circe.Crypto.Qr — the ChaCha20 quarter round as a pure fold (K3).

No C corpus, no gate admission: a 4-writer QR leaf could never pass
the 2+-pointer pair check, so the quarter round is only ever inlined
(K4 inlines it into the block function). This module is the spec K4
verifies against: `rotlU32` composes the shifts explicitly (rotl
stays unadmitted per K1 — the `rotl_u32` reject row), grounded in
the verified K1 shift leaves via the `shl`/`shr` bridges below;
`qrStep` is the RFC 8439 §2.1 four-line macro over wrapping `+`
(total — unsigned wrap is well-defined in C, so no leaf is needed
at spec level); `qrAt` applies it to a state vector (columns and
diagonals in K4). The §2.1.1 test vector is pinned by computation
(`qrStep_kat`), cross-checked two independent ways before
check-in: 6+ web sources for RFC 8439 agree on the words, and a
from-pseudocode Python implementation reproduces them (`MATCH`).
-/
import Circe.Emit.Bitwise

/-- Rotate left by a (nat) amount, shifts composed explicitly. -/
def rotlU32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- The left shift inside `rotlU32` is exactly what the verified
    `shl_u32` leaf computes at a fixed in-range amount. -/
theorem rotlU32_shl (x : BitVec 32) (k : Nat)
    (hk32 : k < 2 ^ 32) (hk : k < 32) :
    shlU32Fwd x (BitVec.ofNat 32 k) = .ok (.u32 (x <<< k)) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hlt : (BitVec.ofNat 32 k).toNat < 32 := by rw [hkk]; exact hk
  rw [shlU32Fwd, checkedShiftU32_ok _ _ _ hlt, hkk]
  rfl

/-- The right shift inside `rotlU32` is exactly what the verified
    `shr_u32` leaf computes at a fixed in-range amount. -/
theorem rotlU32_shr (x : BitVec 32) (k : Nat)
    (hk32 : k < 2 ^ 32) (hk : k < 32) (hk0 : 0 < k) :
    shrU32Fwd x (BitVec.ofNat 32 (32 - k)) =
      .ok (.u32 (x >>> (32 - k))) := by
  have hkk : (BitVec.ofNat 32 (32 - k)).toNat = 32 - k :=
    ofNat32_toNat _ (by omega)
  have hlt : (BitVec.ofNat 32 (32 - k)).toNat < 32 := by
    rw [hkk]; omega
  rw [shrU32Fwd, checkedShiftU32_ok _ _ _ hlt, hkk]
  rfl

/-- One ChaCha20 quarter round (RFC 8439 §2.1): four add-xor-roll
    lines over wrapping `u32` addition. -/
def qrStep (a b c d : BitVec 32) :
    BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  let a1 := a + b
  let d1 := rotlU32 (d ^^^ a1) 16
  let c1 := c + d1
  let b1 := rotlU32 (b ^^^ c1) 12
  let a2 := a1 + b1
  let d2 := rotlU32 (d1 ^^^ a2) 8
  let c2 := c1 + d2
  let b2 := rotlU32 (b1 ^^^ c2) 7
  (a2, b2, c2, d2)

/-- The RFC 8439 §2.1.1 test vector, by computation. -/
theorem qrStep_kat :
    qrStep 0x11111111 0x01020304 0x9b8d6f43 0x01234567 =
      (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb) := by
  decide

/-- The zero quarter round is fixed (second KAT leg). -/
theorem qrStep_zero :
    qrStep 0 0 0 0 = (0, 0, 0, 0) := by
  decide

/-- Apply the quarter round to four state words by index (out of
    range keeps the state — unreachable under the index hypotheses
    K4 checks). -/
def qrAt (s : List (BitVec 32)) (ai bi ci di : Nat) :
    List (BitVec 32) :=
  match s[ai]?, s[bi]?, s[ci]?, s[di]? with
  | some a, some b, some c, some d =>
    let (a', b', c', d') := qrStep a b c d
    (((s.set ai a').set bi b').set ci c').set di d'
  | _, _, _, _ => s

/-- The application preserves the state length. -/
theorem qrAt_length (s : List (BitVec 32)) (ai bi ci di : Nat) :
    (qrAt s ai bi ci di).length = s.length := by
  simp only [qrAt]
  split
  · simp [List.length_set]
  · rfl

/-- Indices outside the four touched words read back unchanged. -/
theorem qrAt_other (s : List (BitVec 32)) (ai bi ci di j : Nat)
    (h1 : j ≠ ai) (h2 : j ≠ bi) (h3 : j ≠ ci) (h4 : j ≠ di) :
    (qrAt s ai bi ci di)[j]? = s[j]? := by
  simp only [qrAt]
  split
  · simp [List.getElem?_set_ne h4.symm, List.getElem?_set_ne h3.symm,
      List.getElem?_set_ne h2.symm, List.getElem?_set_ne h1.symm]
  · rfl

/-- The §2.1.1 vector through the state applier (composition check:
    `qrAt` over `[a,b,c,d]` is `qrStep`). -/
theorem qrAt_kat :
    qrAt [0x11111111, 0x01020304, 0x9b8d6f43, 0x01234567] 0 1 2 3 =
      [0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb] := by
  decide
