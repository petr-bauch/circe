/-
Circe.Crypto.Sha — the SHA-256 compression function as a pure fold (K5).

Spec only (K5b): the gate shape (`isSha256Shape`, K5a) admits the
corpus; the `Func` and its proofs land in K5c, dispatch with them.
Formulation constraints (see the corpus header): rotates compose
shifts explicitly (no rotate leaf — K3 precedent), grounded in the
verified K1 shift leaves via the bridges below; `shaCh` uses the
no-complement identity `z ^ (x & (y ^ z))` (no u32 `cir.not` leaf
anywhere in the subset — `shaCh_correct` pins it to the FIPS
definition); `+` is wrapping (total — unsigned wrap is
well-defined in C, so no leaf is needed at spec level, K3
precedent). `and`/`or`/`xor` need no bridge lemmas: the K1
forwards are definitional (`andU32Fwd a b = .ok (.u32 (a &&& b))`
by `rfl`, likewise `or`/`xor`), so K5c uses `rfl` directly.
The "abc" vector is pinned by computation (`sha256Compress_kat`),
cross-checked two independent ways before check-in: hashlib's
`sha256(b"abc")` and a from-pseudocode Python implementation
(which also validates the K-constant transcription and the
no-complement `Ch` spelling — both exercised every round).
-/
import Circe.Emit.Bitwise

/-- Rotate right by a (nat) amount, shifts composed explicitly. -/
def rotrU32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- The right shift inside `rotrU32` is exactly what the verified
    `shr_u32` leaf computes at a fixed in-range amount. -/
theorem rotrU32_shr (x : BitVec 32) (k : Nat)
    (hk32 : k < 2 ^ 32) (hk : k < 32) :
    shrU32Fwd x (BitVec.ofNat 32 k) = .ok (.u32 (x >>> k)) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hlt : (BitVec.ofNat 32 k).toNat < 32 := by rw [hkk]; exact hk
  rw [shrU32Fwd, checkedShiftU32_ok _ _ _ hlt, hkk]
  rfl

/-- The left shift inside `rotrU32` is exactly what the verified
    `shl_u32` leaf computes at a fixed in-range complement amount. -/
theorem rotrU32_shl (x : BitVec 32) (k : Nat)
    (hk32 : k < 2 ^ 32) (hk : k < 32) (hk0 : 0 < k) :
    shlU32Fwd x (BitVec.ofNat 32 (32 - k)) =
      .ok (.u32 (x <<< (32 - k))) := by
  have hkk : (BitVec.ofNat 32 (32 - k)).toNat = 32 - k :=
    ofNat32_toNat _ (by omega)
  have hlt : (BitVec.ofNat 32 (32 - k)).toNat < 32 := by
    rw [hkk]; omega
  rw [shlU32Fwd, checkedShiftU32_ok _ _ _ hlt, hkk]
  rfl

/-- FIPS 180-4 §4.1.2: the big Sigma functions (three-rotor). -/
def shaS0 (x : BitVec 32) : BitVec 32 :=
  rotrU32 x 2 ^^^ rotrU32 x 13 ^^^ rotrU32 x 22

def shaS1 (x : BitVec 32) : BitVec 32 :=
  rotrU32 x 6 ^^^ rotrU32 x 11 ^^^ rotrU32 x 25

/-- FIPS 180-4 §4.1.2: the small sigma functions (schedule). -/
def shas0 (x : BitVec 32) : BitVec 32 :=
  rotrU32 x 7 ^^^ rotrU32 x 18 ^^^ (x >>> 3)

def shas1 (x : BitVec 32) : BitVec 32 :=
  rotrU32 x 17 ^^^ rotrU32 x 19 ^^^ (x >>> 10)

/-- Choose, no-complement spelling (no u32 NOT leaf in the subset). -/
def shaCh (x y z : BitVec 32) : BitVec 32 :=
  z ^^^ (x &&& (y ^^^ z))

/-- Majority (needs no complement). -/
def shaMaj (x y z : BitVec 32) : BitVec 32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- The no-complement `Ch` is the FIPS definition
    (`(x∧y)⊕(¬x∧z)`): both select `y` under `x = 1` and `z` under
    `x = 0`, bit by bit. -/
theorem shaCh_correct (x y z : BitVec 32) :
    shaCh x y z = (x &&& y) ^^^ ((~~~x) &&& z) := by
  unfold shaCh
  bv_decide

/-! ### Block copy and work init (loop specs for K5c) -/

/-- Copy `st[8+t]` into `w[t]` (the first `cir.for` fills the
    16-word block prefix of the 64-word schedule). -/
def initStep (w s : List (BitVec 32)) (t : Nat) : List (BitVec 32) :=
  match s[8 + t]? with
  | some x => w.set t x
  | none => w

/-- The copy preserves the schedule length. -/
theorem initStep_length (w s : List (BitVec 32)) (t : Nat) :
    (initStep w s t).length = w.length := by
  simp only [initStep]
  split
  · simp [List.length_set]
  · rfl

/-- Copy words `t, t+1, ...` for `fuel` steps (the C runs
    `initLoop 16 0` over the zeroed schedule). -/
def initLoop : Nat → Nat → List (BitVec 32) → List (BitVec 32) →
    List (BitVec 32)
  | 0, _, w, _ => w
  | fuel + 1, t, w, s => initLoop fuel (t + 1) (initStep w s t) s

/-- Unfolding one copy off the front (definitional). -/
theorem initLoop_succ (fuel t : Nat) (w s : List (BitVec 32)) :
    initLoop (fuel + 1) t w s =
      initLoop fuel (t + 1) (initStep w s t) s := rfl

/-- The copy preserves the schedule length. -/
theorem initLoop_length (fuel t : Nat) (w s : List (BitVec 32)) :
    (initLoop fuel t w s).length = w.length := by
  induction fuel generalizing t w with
  | zero => rfl
  | succ fuel ih => simp [initLoop_succ, initStep_length, ih]

/-- Copy `st[i]` into `v[i]` (the third `cir.for` fills the
    working vars from the digest head). -/
def vinitStep (v s : List (BitVec 32)) (i : Nat) : List (BitVec 32) :=
  match s[i]? with
  | some x => v.set i x
  | none => v

/-- The copy preserves the working-vector length. -/
theorem vinitStep_length (v s : List (BitVec 32)) (i : Nat) :
    (vinitStep v s i).length = v.length := by
  simp only [vinitStep]
  split
  · simp [List.length_set]
  · rfl

/-- Copy words `i, i+1, ...` for `fuel` steps (the C runs
    `vinitLoop 8 0` over the zeroed working vars). -/
def vinitLoop : Nat → Nat → List (BitVec 32) → List (BitVec 32) →
    List (BitVec 32)
  | 0, _, v, _ => v
  | fuel + 1, i, v, s => vinitLoop fuel (i + 1) (vinitStep v s i) s

/-- Unfolding one copy off the front (definitional). -/
theorem vinitLoop_succ (fuel i : Nat) (v s : List (BitVec 32)) :
    vinitLoop (fuel + 1) i v s =
      vinitLoop fuel (i + 1) (vinitStep v s i) s := rfl

/-- The copy preserves the working-vector length. -/
theorem vinitLoop_length (fuel i : Nat) (v s : List (BitVec 32)) :
    (vinitLoop fuel i v s).length = v.length := by
  induction fuel generalizing i v with
  | zero => rfl
  | succ fuel ih => simp [vinitLoop_succ, vinitStep_length, ih]

/-! ### Message schedule (FIPS 180-4 §6.2.2) -/

/-- Set schedule word `t` (`w[t-16] + s0 + w[t-7] + s1`); out of
    range keeps the list (unreachable under the length hypotheses
    K5c checks — same contract as K4's `qrAt`). -/
def schedStep (w : List (BitVec 32)) (t : Nat) : List (BitVec 32) :=
  match w[t]?, w[t - 16]?, w[t - 15]?, w[t - 7]?, w[t - 2]? with
  | some _, some a, some b, some c, some d =>
    w.set t (a + shas0 b + c + shas1 d)
  | _, _, _, _, _ => w

/-- The application preserves the list length. -/
theorem schedStep_length (w : List (BitVec 32)) (t : Nat) :
    (schedStep w t).length = w.length := by
  simp only [schedStep]
  split
  · simp [List.length_set]
  · rfl

/-- Fill `t, t+1, ...` for `fuel` steps (the C runs
    `schedLoop 48 16` over the 16-word block prefix). -/
def schedLoop : Nat → Nat → List (BitVec 32) → List (BitVec 32)
  | 0, _, w => w
  | fuel + 1, t, w => schedLoop fuel (t + 1) (schedStep w t)

/-- Unfolding one step off the front (definitional). -/
theorem schedLoop_succ (fuel t : Nat) (w : List (BitVec 32)) :
    schedLoop (fuel + 1) t w =
      schedLoop fuel (t + 1) (schedStep w t) := rfl

/-- The fill preserves the list length. -/
theorem schedLoop_length (fuel t : Nat) (w : List (BitVec 32)) :
    (schedLoop fuel t w).length = w.length := by
  induction fuel generalizing t w with
  | zero => rfl
  | succ fuel ih => simp [schedLoop_succ, schedStep_length, ih]

/-! ### Compression rounds (FIPS 180-4 §6.2.2) -/

/-- The 64 round constants (first 32 bits of the fractional parts of
    the cube roots of the first 64 primes; transcription validated by
    the Python oracle — every word is exercised each KAT run). -/
def shaK : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
   0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
   0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
   0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
   0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
   0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
   0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
   0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
   0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- All 64 constants are present. -/
theorem shaK_length : shaK.length = 64 := by decide

/-- One compression round over the 8 working vars
    (`[a,b,c,d,e,f,g,h]`), reading schedule word `t`; anything
    short keeps `v` (K5c checks lengths — same contract as `qrAt`). -/
def roundStep (v w : List (BitVec 32)) (t : Nat) :
    List (BitVec 32) :=
  match v, w[t]?, shaK[t]? with
  | [a, b, c, d, e, f, g, h], some wt, some k =>
    let t1 := h + shaS1 e + shaCh e f g + k + wt
    let t2 := shaS0 a + shaMaj a b c
    [t1 + t2, a, b, c, d + t1, e, f, g]
  | _, _, _ => v

/-- A full round preserves an 8-word working vector's length. -/
theorem roundStep_length (v w : List (BitVec 32)) (t : Nat) :
    (roundStep v w t).length = v.length := by
  simp only [roundStep]
  split
  · next a b c d e f g h _ _ _ _ _ =>
    simp_all
  · rfl

/-- Rounds `t, t+1, ...` for `fuel` steps (the C runs
    `compressLoop 64 0`). -/
def compressLoop : Nat → Nat → List (BitVec 32) → List (BitVec 32) →
    List (BitVec 32)
  | 0, _, v, _ => v
  | fuel + 1, t, v, w => compressLoop fuel (t + 1) (roundStep v w t) w

/-- Unfolding one round off the front (definitional). -/
theorem compressLoop_succ (fuel t : Nat) (v w : List (BitVec 32)) :
    compressLoop (fuel + 1) t v w =
      compressLoop fuel (t + 1) (roundStep v w t) w := rfl

/-- The rounds preserve the working-vector length. -/
theorem compressLoop_length (fuel t : Nat) (v w : List (BitVec 32)) :
    (compressLoop fuel t v w).length = v.length := by
  induction fuel generalizing t v with
  | zero => rfl
  | succ fuel ih => simp [compressLoop_succ, roundStep_length, ih]

/-! ### Add-back and the top-level fold -/

/-- Add the working vars back into the first 8 state words; the tail
    (block words and beyond) passes through untouched, so the length
    is always the input length. -/
def shaAddBack (s v : List (BitVec 32)) : List (BitVec 32) :=
  List.zipWith (· + ·) (s.take 8) (v.take 8) ++ s.drop 8

/-- The add-back preserves the state length once both sides agree
    on the 8-word prefix (K5c discharges this from the loop
    invariants; short states otherwise truncate like `zipWith`). -/
theorem shaAddBack_length (s v : List (BitVec 32))
    (h : (s.take 8).length = (v.take 8).length) :
    (shaAddBack s v).length = s.length := by
  have h2 : min 8 s.length = min 8 v.length := by
    have h3 := h
    rwa [List.length_take, List.length_take] at h3
  simp only [shaAddBack, List.length_append, List.length_zipWith,
    List.length_take, List.length_drop]
  omega

/-- The full compression fold over the 24-word state (8 digest +
    16 block): schedule, 64 rounds, add-back. Total (like K4's
    forward): short inputs compute junk — the `Func` errors `OOB`
    there (K5c) — while long tails pass through. -/
def sha256CompressFwd (st : List (BitVec 32)) : List (BitVec 32) :=
  let blk := (st.drop 8).take 16
  let w := schedLoop 48 16 (blk ++ List.replicate 48 0)
  let v := compressLoop 64 0 (st.take 8) w
  shaAddBack st v

/-- The fold preserves the state length (rounds preserve the
    take-8 prefix length, so the add-back hypothesis holds). -/
theorem sha256CompressFwd_length (st : List (BitVec 32)) :
    (sha256CompressFwd st).length = st.length := by
  have h : ((st.take 8).length =
    ((compressLoop 64 0 (st.take 8)
      (schedLoop 48 16 ((st.drop 8).take 16 ++ List.replicate 48 0))).take 8).length) := by
    simp only [List.length_take, compressLoop_length]
    omega
  simp only [sha256CompressFwd]
  exact shaAddBack_length _ _ h

-- The 64-round fold needs a deeper kernel stack than the default allows.
set_option maxRecDepth 10000 in
/-- The FIPS 180-4 §8.1.1 "abc" vector, by computation: the fold over
    IV + padded block is the known digest + the block back. -/
theorem sha256Compress_kat :
    sha256CompressFwd
      [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
       0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
       0x61626380, 0x00000000, 0x00000000, 0x00000000,
       0x00000000, 0x00000000, 0x00000000, 0x00000000,
       0x00000000, 0x00000000, 0x00000000, 0x00000000,
       0x00000000, 0x00000000, 0x00000000, 0x00000018] =
      [0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
       0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad,
       0x61626380, 0x00000000, 0x00000000, 0x00000000,
       0x00000000, 0x00000000, 0x00000000, 0x00000000,
       0x00000000, 0x00000000, 0x00000000, 0x00000000,
       0x00000000, 0x00000000, 0x00000000, 0x00000018] := by
  decide
