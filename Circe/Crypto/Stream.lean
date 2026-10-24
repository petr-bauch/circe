/-
Circe.Crypto.Stream — the K6 ChaCha20 stream cipher `chacha20_encrypt`
(`tests/c/chacha20_encrypt.c`): multi-block encryption per RFC 8439
§2.4.1 over the K4 block leaf. First admitted call-in-loop shape (G1):
the outer `cir.while` body holds exactly one `chacha20_block` call
site (plus a 16-word xor loop); the tail `cir.if` holds the second
call site (plus an ntail-word xor loop). The callee is call-free, so
the call resolves via the leaf evaluator at the same fuel (S1
`callRet` discipline); the C1 program-threading loop already runs
loop bodies under the program evaluator.

Mirror discipline: scalars that touch indices or the block counter
are u64 (`off`, `i`, `ntail`, `nwords`); the word counter `b` and
`counter` stay u32 so `state[12] = counter + b` is a plain `uadd`
(K4/K2 precedent: indices into `arrSet`/`idxu` must evaluate to u64
words). `nwords` is u64 in the mirror while the C has u32 — the wrap
divergence is unreachable under the fuel bound (off advances 16 per
iteration, iterations ≤ EVAL_FUEL) and the length hypothesis; the
native fuzz leg pins agreement on all reachable sizes. Longer inputs
pass OOB loudly via the up-front length check (K4/K5 precedent).
-/
import Circe.Emit.Fragment
import Circe.Crypto.Block

/-! ## Mirror fragments -/

/-- u32 word literal. -/
def u32lit (n : Nat) : CExpr := .lit (.u32 (BitVec.ofNat 32 n))

/-- u64 index/amount literal. -/
def u64lit (n : Nat) : CExpr := .lit (.u64 (BitVec.ofNat 64 n))

/-- `key[i]` read (u64 index, K4 `xAt` precedent). -/
def keyAt (i : Nat) : CExpr := .idxu "key" (u64lit i)

/-- `nonce[i]` read. -/
def nonceAt (i : Nat) : CExpr := .idxu "nonce" (u64lit i)

/-- One state-setup store: `st[k] = v`. -/
def stSet (k : Nat) (v : CExpr) : CStmt := .arrSet "st" (u64lit k) v

/-- Block state setup: constants, key words, `counter + b`, nonce
    words (RFC 8439 §2.3 inner block). Identical for full and tail
    blocks — `b` is the running word counter in both. -/
def setupFrag : CStmt :=
  .seq (stSet 0 (u32lit 0x61707865))
  (.seq (stSet 1 (u32lit 0x3320646e))
  (.seq (stSet 2 (u32lit 0x79622d32))
  (.seq (stSet 3 (u32lit 0x6b206574))
  (.seq (stSet 4 (keyAt 0))
  (.seq (stSet 5 (keyAt 1))
  (.seq (stSet 6 (keyAt 2))
  (.seq (stSet 7 (keyAt 3))
  (.seq (stSet 8 (keyAt 4))
  (.seq (stSet 9 (keyAt 5))
  (.seq (stSet 10 (keyAt 6))
  (.seq (stSet 11 (keyAt 7))
  (.seq (stSet 12 (.uadd (.var "counter") (.var "b")))
  (.seq (stSet 13 (nonceAt 0))
  (.seq (stSet 14 (nonceAt 1))
    (stSet 15 (nonceAt 2))))))))))))))))

/-- The admitted block call: `s = chacha20_block(st)` (`callRet` into
    the call-free K4 leaf, resolved by name in the program). -/
def blockCallFrag : CStmt := .callRet "s" "chacha20_block" ["st"]

/-- Xor-loop body: `msg[off+i] ^= s[i]; i++` (K2 `xorBody`
    precedent). -/
def xorBodyFrag : CStmt :=
  .seq (.arrSet "msg" (.uadd (.var "off") (.var "i"))
          (.bxor (.idxu "msg" (.uadd (.var "off") (.var "i")))
            (.idxu "s" (.var "i"))))
       (.assign "i" (.uadd (.var "i") (u64lit 1)))

/-- Full-block xor loop (`i in [0, 16)`). -/
def xorFullFrag : CStmt :=
  .while_ (.ult (.var "i") (u64lit 16)) xorBodyFrag

/-- Tail xor loop (`i in [0, ntail)`). -/
def xorTailFrag : CStmt :=
  .while_ (.ult (.var "i") (.var "ntail")) xorBodyFrag

/-- One full iteration: reset `i`, setup, block call, xor, bump `b`
    and `off`. -/
def fullIterFrag : CStmt :=
  .seq (.assign "i" (u64lit 0))
  (.seq setupFrag
  (.seq blockCallFrag
  (.seq xorFullFrag
  (.seq (.assign "b" (.uadd (.var "b") (u32lit 1)))
        (.assign "off" (.uadd (.var "off") (u64lit 16)))))))

/-- Outer block loop (`off + 16 < nwords + 1`, i.e. `off + 16 ≤
    nwords` without unsigned `≤` in CoreIR). -/
def outerWhileFrag : CStmt :=
  .while_ (.ult (.uadd (.var "off") (u64lit 16))
                 (.uadd (.var "nwords") (u64lit 1))) fullIterFrag

/-- Tail block: reset `i`, setup, block call, partial xor. -/
def tailFrag : CStmt :=
  .seq (.assign "i" (u64lit 0))
  (.seq setupFrag
  (.seq blockCallFrag xorTailFrag))

/-- Canonical CoreIR for `tests/c/chacha20_encrypt.c`. -/
def chacha20EncryptFunc : Func :=
  ⟨"chacha20_encrypt",
   [{ name := "key", ty := .array (.u 32) 8, role := .sharedBorrow },
    { name := "counter", ty := .u 32, role := .owned },
    { name := "nonce", ty := .array (.u 32) 3, role := .sharedBorrow },
    { name := "msg", ty := .array (.u 32) 4096, role := .mutBorrow 0 },
    { name := "nwords", ty := .u 64, role := .owned }],
   .array (.u 32) 4096,
   .seq (.let_ "b" (.u 32) (u32lit 0))
   (.seq (.let_ "off" (.u 64) (u64lit 0))
   (.seq (.let_ "i" (.u 64) (u64lit 0))
   (.seq (.let_ "st" (.array (.u 32) 16)
            (.lit (.arr32 (List.replicate 16 0))))
   (.seq outerWhileFrag
   (.seq (.let_ "ntail" (.u 64)
             (.usub (.var "nwords") (.var "off")))
   (.seq (.if_ (.une (.var "ntail") (u64lit 0)) tailFrag .skip)
         (.return_ (.var "msg"))))))))⟩

/-! ## Pure forward model -/

/-- Block state setup as a word list: constants, key words,
    `counter + b` (u32 wrap, matching the C), nonce words. -/
def encSetup (key : List (BitVec 32)) (counter : BitVec 32) (b : Nat)
    (nonce : List (BitVec 32)) : List (BitVec 32) :=
  [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++
    (key.take 8) ++
    [counter + BitVec.ofNat 32 b] ++
    (nonce.take 3)

/-- The setup always builds exactly 16 words. -/
theorem encSetup_length (key : List (BitVec 32)) (counter : BitVec 32)
    (b : Nat) (nonce : List (BitVec 32))
    (hk : 8 ≤ key.length) (hn : 3 ≤ nonce.length) :
    (encSetup key counter b nonce).length = 16 := by
  simp [encSetup, List.length_take]
  omega

/-- Xor `n` keystream words into `msg` at `off` (out-of-range reads
    keep the old word via `getD`; unreachable under the length
    hypotheses the forward checks). -/
def encXor (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => msg
  | n+1 =>
    ((encXor msg off s n).set (off + n)
      (((encXor msg off s n)[off + n]?.getD 0) ^^^ (s[n]?.getD 0)))

/-- Unfolding the last xor step (definitional). -/
theorem encXor_succ (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) (n : Nat) :
    encXor msg off s (n + 1) =
      ((encXor msg off s n).set (off + n)
        (((encXor msg off s n)[off + n]?.getD 0) ^^^ (s[n]?.getD 0))) :=
  rfl

/-- Xor keeps the message length. -/
theorem encXor_length (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) (n : Nat) :
    (encXor msg off s n).length = msg.length := by
  induction n generalizing msg with
  | zero => rfl
  | succ k ih => simp [encXor, ih, List.length_set]

/-- Value-level forward for `chacha20_encrypt`: fuel-threaded block
    loop mirroring the evaluator (K5/M8 precedent). Up-front length
    checks (`OOB` below the key/nonce/message bounds); each full
    block runs the K4 forward and xors 16 words; the tail xors the
    remainder. Zero fuel is loud. -/
def chacha20EncryptFwd (key : List (BitVec 32)) (counter : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64) (F : Nat) :
    Result Value :=
  match F with
  | 0 => .error .AssertFail
  | F+1 =>
    if 8 ≤ key.length ∧ 3 ≤ nonce.length ∧ nwords.toNat ≤ msg.length then
      match encLoopFwd key counter 0 nonce msg 0 nwords.toNat F with
      | .error e => .error e
      | .ok m => .ok (.arr32 m)
    else .error .OOB
where
  encLoopFwd (key : List (BitVec 32)) (counter : BitVec 32) (b : Nat)
      (nonce msg : List (BitVec 32)) (off nwords : Nat) : Nat →
      Result (List (BitVec 32))
    | 0 => .error .AssertFail
    | F+1 =>
      if off + 16 < nwords + 1 then
        match chachaBlockFwd (encSetup key counter b nonce) with
        | .error e => .error e
        | .ok (.arr32 s) =>
          encLoopFwd key counter (b + 1) nonce
            (encXor msg off s 16) (off + 16) nwords F
        | .ok _ => .error .AssertFail
      else
        let ntail := nwords - off
        if ntail = 0 then .ok msg
        else
          match chachaBlockFwd (encSetup key counter b nonce) with
          | .error e => .error e
          | .ok (.arr32 s) => .ok (encXor msg off s ntail)
          | .ok _ => .error .AssertFail

/-- Fuel-free stream encryption (structural recursion on the remaining
    word count): the reference the rendered forward and the spec stub
    share; the fuel-threaded `chacha20EncryptFwd` is proved equal to it
    at sufficient fuel (K6b). -/
def chacha20EncryptList (key : List (BitVec 32)) (counter : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords off : Nat) (b : Nat) :
    Result (List (BitVec 32)) :=
  if 8 ≤ key.length ∧ 3 ≤ nonce.length ∧ nwords ≤ msg.length then
    if off + 16 < nwords + 1 then
      match chachaBlockFwd (encSetup key counter b nonce) with
      | .error e => .error e
      | .ok (.arr32 s) =>
        chacha20EncryptList key counter nonce
          (encXor msg off s 16) nwords (off + 16) (b + 1)
      | .ok _ => .error .AssertFail
    else
      let ntail := nwords - off
      if ntail = 0 then .ok msg
      else
        match chachaBlockFwd (encSetup key counter b nonce) with
        | .error e => .error e
        | .ok (.arr32 s) => .ok (encXor msg off s ntail)
        | .ok _ => .error .AssertFail
  else .error .OOB
termination_by nwords - off

/-- Program for the stream cipher: the encrypt entry plus the admitted
    K4 block leaf (call resolution by name). -/
def chacha20EncryptProg : Prog := [chacha20EncryptFunc, chachaBlockFunc]
