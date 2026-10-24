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

/-- `stSet` unfolds to the raw `arrSet` (composition rewrite). -/
theorem stSet_eq (k : Nat) (v : CExpr) :
    stSet k v = .arrSet "st" (u64lit k) v := rfl

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

/-- Canonical encrypt env: `st`, `i`, `off`, `b` locals over the five
    params (K5 `mkInitEnv` precedent). `bN`/`offN` are the Nat values,
    `bB`/`i` the stored words. -/
def mkEncEnv (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) : Env :=
  [("st", .arr32 st), ("i", .u64 i),
   ("off", .u64 (BitVec.ofNat 64 offN)), ("b", .u32 bB),
   ("key", .arr32 key), ("counter", .u32 counter),
   ("nonce", .arr32 nonce), ("msg", .arr32 msg),
   ("nwords", .u64 nwords)]

theorem mkEncEnv_st (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "st" = some (.arr32 st) := by
  simp [mkEncEnv, envLookup]

theorem mkEncEnv_i (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "i" = some (.u64 i) := by
  simp [mkEncEnv, envLookup, show ("i" : String) ≠ "st" by decide]

theorem mkEncEnv_off (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "off" = some (.u64 (BitVec.ofNat 64 offN)) := by
  simp [mkEncEnv, envLookup, show ("off" : String) ≠ "st" by decide,
    show ("off" : String) ≠ "i" by decide]

theorem mkEncEnv_b (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "b" = some (.u32 bB) := by
  simp [mkEncEnv, envLookup, show ("b" : String) ≠ "st" by decide,
    show ("b" : String) ≠ "i" by decide,
    show ("b" : String) ≠ "off" by decide]

theorem mkEncEnv_key (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "key" = some (.arr32 key) := by
  simp [mkEncEnv, envLookup, show ("key" : String) ≠ "st" by decide,
    show ("key" : String) ≠ "i" by decide,
    show ("key" : String) ≠ "off" by decide,
    show ("key" : String) ≠ "b" by decide]

theorem mkEncEnv_counter (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "counter" = some (.u32 counter) := by
  simp [mkEncEnv, envLookup, show ("counter" : String) ≠ "st" by decide,
    show ("counter" : String) ≠ "i" by decide,
    show ("counter" : String) ≠ "off" by decide,
    show ("counter" : String) ≠ "b" by decide,
    show ("counter" : String) ≠ "key" by decide]

theorem mkEncEnv_nonce (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "nonce" = some (.arr32 nonce) := by
  simp [mkEncEnv, envLookup, show ("nonce" : String) ≠ "st" by decide,
    show ("nonce" : String) ≠ "i" by decide,
    show ("nonce" : String) ≠ "off" by decide,
    show ("nonce" : String) ≠ "b" by decide,
    show ("nonce" : String) ≠ "key" by decide,
    show ("nonce" : String) ≠ "counter" by decide]

theorem mkEncEnv_msg (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "msg" = some (.arr32 msg) := by
  simp [mkEncEnv, envLookup, show ("msg" : String) ≠ "st" by decide,
    show ("msg" : String) ≠ "i" by decide,
    show ("msg" : String) ≠ "off" by decide,
    show ("msg" : String) ≠ "b" by decide,
    show ("msg" : String) ≠ "key" by decide,
    show ("msg" : String) ≠ "counter" by decide,
    show ("msg" : String) ≠ "nonce" by decide]

theorem mkEncEnv_nwords (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envLookup (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "nwords" = some (.u64 nwords) := by
  simp [mkEncEnv, envLookup, show ("nwords" : String) ≠ "st" by decide,
    show ("nwords" : String) ≠ "i" by decide,
    show ("nwords" : String) ≠ "off" by decide,
    show ("nwords" : String) ≠ "b" by decide,
    show ("nwords" : String) ≠ "key" by decide,
    show ("nwords" : String) ≠ "counter" by decide,
    show ("nwords" : String) ≠ "nonce" by decide,
    show ("nwords" : String) ≠ "msg" by decide]

theorem mkEncEnv_update_st (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st l' : List (BitVec 32)) :
    envUpdate (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "st" (.arr32 l') =
      some (mkEncEnv key counter bB nonce msg nwords bN offN i l') := by
  simp [mkEncEnv, envUpdate]

theorem mkEncEnv_update_i (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i i' : BitVec 64)
    (st : List (BitVec 32)) :
    envUpdate (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "i" (.u64 i') =
      some (mkEncEnv key counter bB nonce msg nwords bN offN i' st) := by
  simp [mkEncEnv, envUpdate, show ("i" : String) ≠ "st" by decide]

theorem mkEncEnv_update_off (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN offN' : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envUpdate (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "off" (.u64 (BitVec.ofNat 64 offN')) =
      some (mkEncEnv key counter bB nonce msg nwords bN offN' i st) := by
  simp [mkEncEnv, envUpdate, show ("off" : String) ≠ "st" by decide,
    show ("off" : String) ≠ "i" by decide]

theorem mkEncEnv_update_b (key : List (BitVec 32)) (counter : BitVec 32)
    (bB bB' : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envUpdate (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "b" (.u32 bB') =
      some (mkEncEnv key counter bB' nonce msg nwords bN offN i st) := by
  simp [mkEncEnv, envUpdate, show ("b" : String) ≠ "st" by decide,
    show ("b" : String) ≠ "i" by decide,
    show ("b" : String) ≠ "off" by decide]

theorem mkEncEnv_update_msg (key : List (BitVec 32)) (counter : BitVec 32)
    (bB : BitVec 32) (nonce msg msg' : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (i : BitVec 64)
    (st : List (BitVec 32)) :
    envUpdate (mkEncEnv key counter bB nonce msg nwords bN offN i st)
      "msg" (.arr32 msg') =
      some (mkEncEnv key counter bB nonce msg' nwords bN offN i st) := by
  simp [mkEncEnv, envUpdate, show ("msg" : String) ≠ "st" by decide,
    show ("msg" : String) ≠ "i" by decide,
    show ("msg" : String) ≠ "off" by decide,
    show ("msg" : String) ≠ "b" by decide,
    show ("msg" : String) ≠ "key" by decide,
    show ("msg" : String) ≠ "counter" by decide,
    show ("msg" : String) ≠ "nonce" by decide]


/-- Program-level `arrSet` (K6 analogue of `revVecSet`). -/
theorem encArrSet (prog : Prog) (F : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i : BitVec 64) (xv : BitVec 32)
    (l : List (BitVec 32)) (w : BitVec 32) (ρ' : Env)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.u32 xv))
    (harr : envLookup ρ x = some (.arr32 l))
    (hget : l[i.toNat]? = some w)
    (hu : envUpdate ρ x (.arr32 (l.set i.toNat xv)) = some ρ') :
    evalProgStmt prog F (.arrSet x ie ve) ρ = .ok (ρ', .fellThrough) := by
  simpa [evalProgStmt] using
    (evalStmtFuel_arrSet F x ie ve ρ i xv l w ρ' hi hv harr hget hu)

/-- The 16-store chain is exactly `encSetup`. -/
theorem setupChain_eq_encSetup (st key : List (BitVec 32))
    (counter bB : BitVec 32) (b : Nat) (hbN : bB.toNat = b)
    (nonce : List (BitVec 32))
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hst16 : st.length = 16) :
    ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]).set 15 nonce[2]) =
      encSetup key counter b nonce := by
  have hkj0 : 0 < key.length := by omega
  have hkj1 : 1 < key.length := by omega
  have hkj2 : 2 < key.length := by omega
  have hkj3 : 3 < key.length := by omega
  have hkj4 : 4 < key.length := by omega
  have hkj5 : 5 < key.length := by omega
  have hkj6 : 6 < key.length := by omega
  have hkj7 : 7 < key.length := by omega
  have hnj0 : 0 < nonce.length := by omega
  have hnj1 : 1 < nonce.length := by omega
  have hnj2 : 2 < nonce.length := by omega
  have hbB : BitVec.ofNat 32 b = bB := by rw [← hbN]; simp
  have hlen : (((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]).set 15 nonce[2])).length = 16 := by simp [List.length_set, hst16]
  have henc : (encSetup key counter b nonce).length = 16 :=
    encSetup_length key counter b nonce hk8 hn3
  apply List.ext_getElem?
  intro i
  by_cases hi16 : i < 16
  · by_cases h0 : i = 0
    · subst h0
      have hbnd0 : 0 < (encSetup key counter b nonce).length := by omega
      simp_all [encSetup]
    · by_cases h1 : i = 1
      · subst h1
        have hbnd1 : 1 < (encSetup key counter b nonce).length := by omega
        simp_all [encSetup]
      · by_cases h2 : i = 2
        · subst h2
          have hbnd2 : 2 < (encSetup key counter b nonce).length := by omega
          simp_all [encSetup]
        · by_cases h3 : i = 3
          · subst h3
            have hbnd3 : 3 < (encSetup key counter b nonce).length := by omega
            simp_all [encSetup]
          · by_cases h4 : i = 4
            · subst h4
              have hbnd4 : 4 < (encSetup key counter b nonce).length := by omega
              simp_all [encSetup]
            · by_cases h5 : i = 5
              · subst h5
                have hbnd5 : 5 < (encSetup key counter b nonce).length := by omega
                simp_all [encSetup]
              · by_cases h6 : i = 6
                · subst h6
                  have hbnd6 : 6 < (encSetup key counter b nonce).length := by omega
                  simp_all [encSetup]
                · by_cases h7 : i = 7
                  · subst h7
                    have hbnd7 : 7 < (encSetup key counter b nonce).length := by omega
                    simp_all [encSetup]
                  · by_cases h8 : i = 8
                    · subst h8
                      have hbnd8 : 8 < (encSetup key counter b nonce).length := by omega
                      simp_all [encSetup]
                    · by_cases h9 : i = 9
                      · subst h9
                        have hbnd9 : 9 < (encSetup key counter b nonce).length := by omega
                        simp_all [encSetup]
                      · by_cases h10 : i = 10
                        · subst h10
                          have hbnd10 : 10 < (encSetup key counter b nonce).length := by omega
                          simp_all [encSetup]
                        · by_cases h11 : i = 11
                          · subst h11
                            have hbnd11 : 11 < (encSetup key counter b nonce).length := by omega
                            simp_all [encSetup]
                          · by_cases h12 : i = 12
                            · subst h12
                              have hbnd12 : 12 < (encSetup key counter b nonce).length := by omega
                              simp_all [encSetup]
                            · by_cases h13 : i = 13
                              · subst h13
                                have hbnd13 : 13 < (encSetup key counter b nonce).length := by omega
                                simp_all [encSetup]
                              · by_cases h14 : i = 14
                                · subst h14
                                  have hbnd14 : 14 < (encSetup key counter b nonce).length := by omega
                                  simp_all [encSetup]
                                · by_cases h15 : i = 15
                                  · subst h15
                                    have hbnd15 : 15 < (encSetup key counter b nonce).length := by omega
                                    simp_all [encSetup]
                                  · have hfalse : False := by omega
                                    exact False.elim hfalse
  · have e1 : (((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]).set 15 nonce[2]))[i]? = none :=
      List.getElem?_eq_none (by omega)
    have e2 : (encSetup key counter b nonce)[i]? = none :=
      List.getElem?_eq_none (by omega)
    rw [e1, e2]

/-- Lookup skips a prefix of stale bindings (old `s` keystreams,
    the `ntail` let): the workhorse for call-in-loop threading, where
    `callRet` accumulates one `s` binding per iteration. -/
theorem chainLookup (pre : Env) (ρ : Env) (x : String) (v : Value)
    (hrest : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hx : x ≠ "s" ∧ x ≠ "ntail")
    (h : envLookup ρ x = some v) :
    envLookup (pre ++ ρ) x = some v := by
  induction pre with
  | nil => exact h
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    have hk : k ≠ x := by
      have hm : (k, w) ∈ (k, w) :: tl := List.mem_cons_self
      have h2 : ((k, w)).1 ≠ x := by
        rcases hrest (k, w) hm with h' | h'
        · rw [h']; exact Ne.symm hx.1
        · rw [h']; exact Ne.symm hx.2
      exact h2
    have hkx : x ≠ k := Ne.symm hk
    have ih' := ih (fun p hp => hrest p (List.mem_cons_of_mem _ hp))
    simp only [List.cons_append, envLookup, hkx]
    exact ih'

/-- Update traverses a stale-binding prefix in place. -/
theorem chainUpdate (pre : Env) (ρ : Env) (x : String) (v : Value)
    (ρ' : Env)
    (hrest : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hx : x ≠ "s" ∧ x ≠ "ntail")
    (hu : envUpdate ρ x v = some ρ') :
    envUpdate (pre ++ ρ) x v = some (pre ++ ρ') := by
  induction pre with
  | nil => exact hu
  | cons hd tl ih =>
    obtain ⟨k, w⟩ := hd
    have hk : k ≠ x := by
      have hm : (k, w) ∈ (k, w) :: tl := List.mem_cons_self
      have h2 : ((k, w)).1 ≠ x := by
        rcases hrest (k, w) hm with h' | h'
        · rw [h']; exact Ne.symm hx.1
        · rw [h']; exact Ne.symm hx.2
      exact h2
    have hkx : x ≠ k := Ne.symm hk
    have ih' := ih (fun p hp => hrest p (List.mem_cons_of_mem _ hp))
    simp only [List.cons_append, envUpdate_miss _ _ _ _ _ hkx, ih']

/-- The 16 setup stores run straight-line, leaving `st` holding
-- exactly `encSetup` (canonical env in, canonical env out). Each
-- store threads through `encArrSet`; the closing rewrite is the
-- set-chain/`encSetup` bridge below. -/
theorem setupFrag_correct (prog : Prog) (F : Nat)
    (key : List (BitVec 32)) (counter : BitVec 32) (bB : BitVec 32)
    (b : Nat) (hbN : bB.toNat = b)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (bN offN : Nat) (iB : BitVec 64) (st : List (BitVec 32))
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hst16 : st.length = 16) :
    ∃ ρ', evalProgStmt prog F setupFrag
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (ρ', .fellThrough) ∧
      ρ' = pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB
        (encSetup key counter b nonce) := by
  have hkj0 : 0 < key.length := by omega
  have hkj1 : 1 < key.length := by omega
  have hkj2 : 2 < key.length := by omega
  have hkj3 : 3 < key.length := by omega
  have hkj4 : 4 < key.length := by omega
  have hkj5 : 5 < key.length := by omega
  have hkj6 : 6 < key.length := by omega
  have hkj7 : 7 < key.length := by omega
  have hnj0 : 0 < nonce.length := by omega
  have hnj1 : 1 < nonce.length := by omega
  have hnj2 : 2 < nonce.length := by omega
  have hknat0 : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by omega)
  have hi0 : evalExpr (u64lit 0) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) = .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv0 : evalExpr (u32lit 0x61707865) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) = .ok (.u32 (BitVec.ofNat 32 0x61707865)) := by
      simp only [u32lit, evalExpr, litVal]
  have ha0 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB st)
  have hlen0 : (st).length = 16 := hst16
  have hlt0 : 0 < (st).length := by omega
  have hg0 : (st)[0]? = some (st)[0] := List.getElem?_eq_getElem hlt0
  have hu0 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (st) ((st).set (BitVec.ofNat 64 0).toNat (BitVec.ofNat 32 0x61707865)))
  rw [hknat0] at hu0
  have hs0 := encArrSet prog F "st" (u64lit 0) (u32lit 0x61707865) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) (BitVec.ofNat 64 0) (BitVec.ofNat 32 0x61707865) (st) (((st))[0]) _ hi0 hv0 ha0 hg0 hu0
  have hknat1 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by omega)
  have hi1 : evalExpr (u64lit 1) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (st.set 0 (BitVec.ofNat 32 0x61707865))) = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv1 : evalExpr (u32lit 0x3320646e) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (st.set 0 (BitVec.ofNat 32 0x61707865))) = .ok (.u32 (BitVec.ofNat 32 0x3320646e)) := by
      simp only [u32lit, evalExpr, litVal]
  have ha1 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (st.set 0 (BitVec.ofNat 32 0x61707865)))
  have hlen1 : ((st.set 0 (BitVec.ofNat 32 0x61707865))).length = 16 := by simp [List.length_set, hlen0]
  have hlt1 : 1 < ((st.set 0 (BitVec.ofNat 32 0x61707865))).length := by omega
  have hg1 : ((st.set 0 (BitVec.ofNat 32 0x61707865)))[1]? = some ((st.set 0 (BitVec.ofNat 32 0x61707865)))[1] := List.getElem?_eq_getElem hlt1
  have hu1 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((st.set 0 (BitVec.ofNat 32 0x61707865))) (((st.set 0 (BitVec.ofNat 32 0x61707865))).set (BitVec.ofNat 64 1).toNat (BitVec.ofNat 32 0x3320646e)))
  rw [hknat1] at hu1
  have hs1 := encArrSet prog F "st" (u64lit 1) (u32lit 0x3320646e) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (st.set 0 (BitVec.ofNat 32 0x61707865))) (BitVec.ofNat 64 1) (BitVec.ofNat 32 0x3320646e) ((st.set 0 (BitVec.ofNat 32 0x61707865))) ((((st.set 0 (BitVec.ofNat 32 0x61707865))))[1]) _ hi1 hv1 ha1 hg1 hu1
  have hknat2 : (BitVec.ofNat 64 2).toNat = 2 := ofNat64_toNat 2 (by omega)
  have hi2 : evalExpr (u64lit 2) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))) = .ok (.u64 (BitVec.ofNat 64 2)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv2 : evalExpr (u32lit 0x79622d32) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))) = .ok (.u32 (BitVec.ofNat 32 0x79622d32)) := by
      simp only [u32lit, evalExpr, litVal]
  have ha2 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB ((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)))
  have hlen2 : (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))).length = 16 := by simp [List.length_set, hlen1]
  have hlt2 : 2 < (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))).length := by omega
  have hg2 : (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)))[2]? = some (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)))[2] := List.getElem?_eq_getElem hlt2
  have hu2 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))) ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))).set (BitVec.ofNat 64 2).toNat (BitVec.ofNat 32 0x79622d32)))
  rw [hknat2] at hu2
  have hs2 := encArrSet prog F "st" (u64lit 2) (u32lit 0x79622d32) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))) (BitVec.ofNat 64 2) (BitVec.ofNat 32 0x79622d32) (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))) (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e))))[2]) _ hi2 hv2 ha2 hg2 hu2
  have hknat3 : (BitVec.ofNat 64 3).toNat = 3 := ofNat64_toNat 3 (by omega)
  have hi3 : evalExpr (u64lit 3) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))) = .ok (.u64 (BitVec.ofNat 64 3)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv3 : evalExpr (u32lit 0x6b206574) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))) = .ok (.u32 (BitVec.ofNat 32 0x6b206574)) := by
      simp only [u32lit, evalExpr, litVal]
  have ha3 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)))
  have hlen3 : ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))).length = 16 := by simp [List.length_set, hlen2]
  have hlt3 : 3 < ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))).length := by omega
  have hg3 : ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)))[3]? = some ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)))[3] := List.getElem?_eq_getElem hlt3
  have hu3 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))) (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))).set (BitVec.ofNat 64 3).toNat (BitVec.ofNat 32 0x6b206574)))
  rw [hknat3] at hu3
  have hs3 := encArrSet prog F "st" (u64lit 3) (u32lit 0x6b206574) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))) (BitVec.ofNat 64 3) (BitVec.ofNat 32 0x6b206574) ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))) ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32))))[3]) _ hi3 hv3 ha3 hg3 hu3
  have hknat4 : (BitVec.ofNat 64 4).toNat = 4 := ofNat64_toNat 4 (by omega)
  have hi4 : evalExpr (u64lit 4) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))) = .ok (.u64 (BitVec.ofNat 64 4)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv4 : evalExpr (keyAt 0) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))) = .ok (.u32 key[0]) := by
      have hkj64 : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by omega)
      have hget : key[0]? = some key[0] := List.getElem?_eq_getElem hkj0
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha4 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)))
  have hlen4 : (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))).length = 16 := by simp [List.length_set, hlen3]
  have hlt4 : 4 < (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))).length := by omega
  have hg4 : (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)))[4]? = some (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)))[4] := List.getElem?_eq_getElem hlt4
  have hu4 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))) ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))).set (BitVec.ofNat 64 4).toNat key[0]))
  rw [hknat4] at hu4
  have hs4 := encArrSet prog F "st" (u64lit 4) (keyAt 0) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))) (BitVec.ofNat 64 4) key[0] (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))) (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574))))[4]) _ hi4 hv4 ha4 hg4 hu4
  have hknat5 : (BitVec.ofNat 64 5).toNat = 5 := ofNat64_toNat 5 (by omega)
  have hi5 : evalExpr (u64lit 5) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])) = .ok (.u64 (BitVec.ofNat 64 5)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv5 : evalExpr (keyAt 1) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])) = .ok (.u32 key[1]) := by
      have hkj64 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by omega)
      have hget : key[1]? = some key[1] := List.getElem?_eq_getElem hkj1
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha5 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]))
  have hlen5 : ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])).length = 16 := by simp [List.length_set, hlen4]
  have hlt5 : 5 < ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])).length := by omega
  have hg5 : ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]))[5]? = some ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]))[5] := List.getElem?_eq_getElem hlt5
  have hu5 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])) (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])).set (BitVec.ofNat 64 5).toNat key[1]))
  rw [hknat5] at hu5
  have hs5 := encArrSet prog F "st" (u64lit 5) (keyAt 1) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])) (BitVec.ofNat 64 5) key[1] ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])) ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0])))[5]) _ hi5 hv5 ha5 hg5 hu5
  have hknat6 : (BitVec.ofNat 64 6).toNat = 6 := ofNat64_toNat 6 (by omega)
  have hi6 : evalExpr (u64lit 6) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])) = .ok (.u64 (BitVec.ofNat 64 6)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv6 : evalExpr (keyAt 2) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])) = .ok (.u32 key[2]) := by
      have hkj64 : (BitVec.ofNat 64 2).toNat = 2 := ofNat64_toNat 2 (by omega)
      have hget : key[2]? = some key[2] := List.getElem?_eq_getElem hkj2
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha6 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]))
  have hlen6 : (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])).length = 16 := by simp [List.length_set, hlen5]
  have hlt6 : 6 < (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])).length := by omega
  have hg6 : (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]))[6]? = some (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]))[6] := List.getElem?_eq_getElem hlt6
  have hu6 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])) ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])).set (BitVec.ofNat 64 6).toNat key[2]))
  rw [hknat6] at hu6
  have hs6 := encArrSet prog F "st" (u64lit 6) (keyAt 2) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])) (BitVec.ofNat 64 6) key[2] (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])) (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1])))[6]) _ hi6 hv6 ha6 hg6 hu6
  have hknat7 : (BitVec.ofNat 64 7).toNat = 7 := ofNat64_toNat 7 (by omega)
  have hi7 : evalExpr (u64lit 7) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])) = .ok (.u64 (BitVec.ofNat 64 7)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv7 : evalExpr (keyAt 3) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])) = .ok (.u32 key[3]) := by
      have hkj64 : (BitVec.ofNat 64 3).toNat = 3 := ofNat64_toNat 3 (by omega)
      have hget : key[3]? = some key[3] := List.getElem?_eq_getElem hkj3
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha7 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]))
  have hlen7 : ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])).length = 16 := by simp [List.length_set, hlen6]
  have hlt7 : 7 < ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])).length := by omega
  have hg7 : ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]))[7]? = some ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]))[7] := List.getElem?_eq_getElem hlt7
  have hu7 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])) (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])).set (BitVec.ofNat 64 7).toNat key[3]))
  rw [hknat7] at hu7
  have hs7 := encArrSet prog F "st" (u64lit 7) (keyAt 3) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])) (BitVec.ofNat 64 7) key[3] ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])) ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2])))[7]) _ hi7 hv7 ha7 hg7 hu7
  have hknat8 : (BitVec.ofNat 64 8).toNat = 8 := ofNat64_toNat 8 (by omega)
  have hi8 : evalExpr (u64lit 8) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])) = .ok (.u64 (BitVec.ofNat 64 8)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv8 : evalExpr (keyAt 4) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])) = .ok (.u32 key[4]) := by
      have hkj64 : (BitVec.ofNat 64 4).toNat = 4 := ofNat64_toNat 4 (by omega)
      have hget : key[4]? = some key[4] := List.getElem?_eq_getElem hkj4
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha8 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]))
  have hlen8 : (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])).length = 16 := by simp [List.length_set, hlen7]
  have hlt8 : 8 < (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])).length := by omega
  have hg8 : (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]))[8]? = some (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]))[8] := List.getElem?_eq_getElem hlt8
  have hu8 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])) ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])).set (BitVec.ofNat 64 8).toNat key[4]))
  rw [hknat8] at hu8
  have hs8 := encArrSet prog F "st" (u64lit 8) (keyAt 4) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])) (BitVec.ofNat 64 8) key[4] (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])) (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3])))[8]) _ hi8 hv8 ha8 hg8 hu8
  have hknat9 : (BitVec.ofNat 64 9).toNat = 9 := ofNat64_toNat 9 (by omega)
  have hi9 : evalExpr (u64lit 9) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])) = .ok (.u64 (BitVec.ofNat 64 9)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv9 : evalExpr (keyAt 5) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])) = .ok (.u32 key[5]) := by
      have hkj64 : (BitVec.ofNat 64 5).toNat = 5 := ofNat64_toNat 5 (by omega)
      have hget : key[5]? = some key[5] := List.getElem?_eq_getElem hkj5
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha9 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]))
  have hlen9 : ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])).length = 16 := by simp [List.length_set, hlen8]
  have hlt9 : 9 < ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])).length := by omega
  have hg9 : ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]))[9]? = some ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]))[9] := List.getElem?_eq_getElem hlt9
  have hu9 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])) (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])).set (BitVec.ofNat 64 9).toNat key[5]))
  rw [hknat9] at hu9
  have hs9 := encArrSet prog F "st" (u64lit 9) (keyAt 5) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])) (BitVec.ofNat 64 9) key[5] ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])) ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4])))[9]) _ hi9 hv9 ha9 hg9 hu9
  have hknat10 : (BitVec.ofNat 64 10).toNat = 10 := ofNat64_toNat 10 (by omega)
  have hi10 : evalExpr (u64lit 10) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])) = .ok (.u64 (BitVec.ofNat 64 10)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv10 : evalExpr (keyAt 6) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])) = .ok (.u32 key[6]) := by
      have hkj64 : (BitVec.ofNat 64 6).toNat = 6 := ofNat64_toNat 6 (by omega)
      have hget : key[6]? = some key[6] := List.getElem?_eq_getElem hkj6
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha10 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]))
  have hlen10 : (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])).length = 16 := by simp [List.length_set, hlen9]
  have hlt10 : 10 < (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])).length := by omega
  have hg10 : (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]))[10]? = some (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]))[10] := List.getElem?_eq_getElem hlt10
  have hu10 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])) ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])).set (BitVec.ofNat 64 10).toNat key[6]))
  rw [hknat10] at hu10
  have hs10 := encArrSet prog F "st" (u64lit 10) (keyAt 6) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])) (BitVec.ofNat 64 10) key[6] (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])) (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5])))[10]) _ hi10 hv10 ha10 hg10 hu10
  have hknat11 : (BitVec.ofNat 64 11).toNat = 11 := ofNat64_toNat 11 (by omega)
  have hi11 : evalExpr (u64lit 11) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])) = .ok (.u64 (BitVec.ofNat 64 11)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv11 : evalExpr (keyAt 7) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])) = .ok (.u32 key[7]) := by
      have hkj64 : (BitVec.ofNat 64 7).toNat = 7 := ofNat64_toNat 7 (by omega)
      have hget : key[7]? = some key[7] := List.getElem?_eq_getElem hkj7
      have hkey := chainLookup pre _ "key" _ hpre (by decide) (mkEncEnv_key key counter bB nonce msg nwords bN offN iB (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]))
      simp only [evalExpr, keyAt, u64lit, litVal, hkey, hkj64, hget]
  have ha11 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]))
  have hlen11 : ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])).length = 16 := by simp [List.length_set, hlen10]
  have hlt11 : 11 < ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])).length := by omega
  have hg11 : ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]))[11]? = some ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]))[11] := List.getElem?_eq_getElem hlt11
  have hu11 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])) (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])).set (BitVec.ofNat 64 11).toNat key[7]))
  rw [hknat11] at hu11
  have hs11 := encArrSet prog F "st" (u64lit 11) (keyAt 7) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])) (BitVec.ofNat 64 11) key[7] ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])) ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6])))[11]) _ hi11 hv11 ha11 hg11 hu11
  have hknat12 : (BitVec.ofNat 64 12).toNat = 12 := ofNat64_toNat 12 (by omega)
  have hi12 : evalExpr (u64lit 12) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])) = .ok (.u64 (BitVec.ofNat 64 12)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv12 : evalExpr (.uadd (.var "counter") (.var "b")) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])) = .ok (.u32 (counter + bB)) := by
      have hcounter := chainLookup pre _ "counter" _ hpre (by decide) (mkEncEnv_counter key counter bB nonce msg nwords bN offN iB ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]))
      have hb := chainLookup pre _ "b" _ hpre (by decide) (mkEncEnv_b key counter bB nonce msg nwords bN offN iB ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]))
      simp only [evalExpr, hcounter, hb]
  have ha12 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]))
  have hlen12 : (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])).length = 16 := by simp [List.length_set, hlen11]
  have hlt12 : 12 < (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])).length := by omega
  have hg12 : (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]))[12]? = some (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]))[12] := List.getElem?_eq_getElem hlt12
  have hu12 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])) ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])).set (BitVec.ofNat 64 12).toNat (counter + bB)))
  rw [hknat12] at hu12
  have hs12 := encArrSet prog F "st" (u64lit 12) (.uadd (.var "counter") (.var "b")) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])) (BitVec.ofNat 64 12) (counter + bB) (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])) (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7])))[12]) _ hi12 hv12 ha12 hg12 hu12
  have hknat13 : (BitVec.ofNat 64 13).toNat = 13 := ofNat64_toNat 13 (by omega)
  have hi13 : evalExpr (u64lit 13) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))) = .ok (.u64 (BitVec.ofNat 64 13)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv13 : evalExpr (nonceAt 0) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))) = .ok (.u32 nonce[0]) := by
      have hkj64 : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by omega)
      have hget : nonce[0]? = some nonce[0] := List.getElem?_eq_getElem hnj0
      have hnonce := chainLookup pre _ "nonce" _ hpre (by decide) (mkEncEnv_nonce key counter bB nonce msg nwords bN offN iB (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)))
      simp only [evalExpr, nonceAt, u64lit, litVal, hnonce, hkj64, hget]
  have ha13 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)))
  have hlen13 : ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))).length = 16 := by simp [List.length_set, hlen12]
  have hlt13 : 13 < ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))).length := by omega
  have hg13 : ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)))[13]? = some ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)))[13] := List.getElem?_eq_getElem hlt13
  have hu13 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))) (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))).set (BitVec.ofNat 64 13).toNat nonce[0]))
  rw [hknat13] at hu13
  have hs13 := encArrSet prog F "st" (u64lit 13) (nonceAt 0) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))) (BitVec.ofNat 64 13) nonce[0] ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))) ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB))))[13]) _ hi13 hv13 ha13 hg13 hu13
  have hknat14 : (BitVec.ofNat 64 14).toNat = 14 := ofNat64_toNat 14 (by omega)
  have hi14 : evalExpr (u64lit 14) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])) = .ok (.u64 (BitVec.ofNat 64 14)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv14 : evalExpr (nonceAt 1) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])) = .ok (.u32 nonce[1]) := by
      have hkj64 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by omega)
      have hget : nonce[1]? = some nonce[1] := List.getElem?_eq_getElem hnj1
      have hnonce := chainLookup pre _ "nonce" _ hpre (by decide) (mkEncEnv_nonce key counter bB nonce msg nwords bN offN iB ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]))
      simp only [evalExpr, nonceAt, u64lit, litVal, hnonce, hkj64, hget]
  have ha14 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]))
  have hlen14 : (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])).length = 16 := by simp [List.length_set, hlen13]
  have hlt14 : 14 < (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])).length := by omega
  have hg14 : (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]))[14]? = some (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]))[14] := List.getElem?_eq_getElem hlt14
  have hu14 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])) ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])).set (BitVec.ofNat 64 14).toNat nonce[1]))
  rw [hknat14] at hu14
  have hs14 := encArrSet prog F "st" (u64lit 14) (nonceAt 1) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])) (BitVec.ofNat 64 14) nonce[1] (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])) (((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0])))[14]) _ hi14 hv14 ha14 hg14 hu14
  have hknat15 : (BitVec.ofNat 64 15).toNat = 15 := ofNat64_toNat 15 (by omega)
  have hi15 : evalExpr (u64lit 15) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])) = .ok (.u64 (BitVec.ofNat 64 15)) := by
    simp only [u64lit, evalExpr, litVal]
  have hv15 : evalExpr (nonceAt 2) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])) = .ok (.u32 nonce[2]) := by
      have hkj64 : (BitVec.ofNat 64 2).toNat = 2 := ofNat64_toNat 2 (by omega)
      have hget : nonce[2]? = some nonce[2] := List.getElem?_eq_getElem hnj2
      have hnonce := chainLookup pre _ "nonce" _ hpre (by decide) (mkEncEnv_nonce key counter bB nonce msg nwords bN offN iB (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]))
      simp only [evalExpr, nonceAt, u64lit, litVal, hnonce, hkj64, hget]
  have ha15 := chainLookup pre _ "st" _ hpre (by decide) (mkEncEnv_st key counter bB nonce msg nwords bN offN iB (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]))
  have hlen15 : ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])).length = 16 := by simp [List.length_set, hlen14]
  have hlt15 : 15 < ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])).length := by omega
  have hg15 : ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]))[15]? = some ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]))[15] := List.getElem?_eq_getElem hlt15
  have hu15 := chainUpdate pre _ "st" _ _ hpre (by decide) (mkEncEnv_update_st key counter bB nonce msg nwords bN offN iB ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])) (((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])).set (BitVec.ofNat 64 15).toNat nonce[2]))
  rw [hknat15] at hu15
  have hs15 := encArrSet prog F "st" (u64lit 15) (nonceAt 2) (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB (((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])) (BitVec.ofNat 64 15) nonce[2] ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])) ((((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1])))[15]) _ hi15 hv15 ha15 hg15 hu15
  have hsetup : evalProgStmt prog F setupFrag
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB ((((((((((((((((st.set 0 (BitVec.ofNat 32 0x61707865)).set 1 (BitVec.ofNat 32 0x3320646e)).set 2 (BitVec.ofNat 32 0x79622d32)).set 3 (BitVec.ofNat 32 0x6b206574)).set 4 key[0]).set 5 key[1]).set 6 key[2]).set 7 key[3]).set 8 key[4]).set 9 key[5]).set 10 key[6]).set 11 key[7]).set 12 (counter + bB)).set 13 nonce[0]).set 14 nonce[1]).set 15 nonce[2]), .fellThrough) := by
    simp only [setupFrag, stSet_eq]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs0]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs1]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs2]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs3]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs4]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs5]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs6]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs7]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs8]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs9]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs10]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs11]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs12]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs13]
    rw [evalProgStmt_seq_fallthrough prog F _ _ _ _ hs14]
    exact hs15
  rw [setupChain_eq_encSetup st key counter bB b hbN nonce hk8 hn3 hst16] at hsetup
  exact ⟨_, hsetup, rfl⟩

/-! ## K6b: xor-loop agreement -/

/-- General-index `idxu` hit (the xor body indexes by `off + i`,
    not a literal). -/
theorem evalExpr_idxu_ok (arr : String) (ie : CExpr) (ρ : Env)
    (l : List (BitVec 32)) (i : BitVec 64) (x : BitVec 32)
    (harr : envLookup ρ arr = some (.arr32 l))
    (hidx : evalExpr ie ρ = .ok (.u64 i))
    (hget : l[i.toNat]? = some x) :
    evalExpr (.idxu arr ie) ρ = .ok (.u32 x) := by
  simp [evalExpr, harr, hidx, hget]

/-- `bxor` on two `u32` words. -/
theorem evalExpr_bxor_u32 (a b : CExpr) (ρ : Env) (x y : BitVec 32)
    (ha : evalExpr a ρ = .ok (.u32 x))
    (hb : evalExpr b ρ = .ok (.u32 y)) :
    evalExpr (.bxor a b) ρ = .ok (.u32 (x ^^^ y)) := by
  simp [evalExpr, ha, hb]

/-- `assign` at program level (call-free, any fuel). -/
theorem evalExpr_uadd_u32 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 32)
    (h₁ : evalExpr e₁ ρ = .ok (.u32 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u32 y)) :
    evalExpr (.uadd e₁ e₂) ρ = .ok (.u32 (x + y)) := by
  simp [evalExpr, h₁, h₂]

theorem evalProgStmt_assign_ok (prog : Prog) (F : Nat) (x : String)
    (e : CExpr) (ρ : Env) (v : Value) (ρ' : Env)
    (h : evalExpr e ρ = .ok v)
    (hu : envUpdate ρ x v = some ρ') :
    evalProgStmt prog F (.assign x e) ρ = .ok (ρ', .fellThrough) := by
  have hfu := evalStmtFuel_assign F x e ρ v ρ' h hu
  cases F with
  | zero => simpa [evalProgStmt] using hfu
  | succ F => simpa [evalProgStmt] using hfu

/-- Wrapping 64-bit addition is exact when the sum fits. -/
theorem u64add_toNat_exact (x y : BitVec 64)
    (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hy : y.toNat < 2 ^ 64 := y.isLt
  omega

/-- Wrapping 32-bit addition is exact when the sum fits. -/
theorem u32add_toNat_exact (x y : BitVec 32)
    (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add]
  have hx : x.toNat < 2 ^ 32 := x.isLt
  have hy : y.toNat < 2 ^ 32 := y.isLt
  omega

/-- Xor words `[i, i+n)` of `s` into `msg` at `off+i` on: the xor
    loop's natural model (the same counter indexes both arrays, so the
    `encXor` shift trick does not apply; the `i = 0` bridge below
    recovers `encXor`). -/
def encXorFrom (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) (i n : Nat) : List (BitVec 32) :=
  match n with
  | 0 => msg
  | n+1 =>
    ((encXorFrom msg off s i n).set (off + i + n)
      (((encXorFrom msg off s i n)[off + i + n]?.getD 0) ^^^
        (s[i + n]?.getD 0)))

/-- Unfolding the last xor step (definitional). -/
theorem encXorFrom_succ (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) (i n : Nat) :
    encXorFrom msg off s i (n + 1) =
      ((encXorFrom msg off s i n).set (off + i + n)
        (((encXorFrom msg off s i n)[off + i + n]?.getD 0) ^^^
          (s[i + n]?.getD 0))) := rfl

/-- Xor keeps the message length. -/
theorem encXorFrom_length (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) (i n : Nat) :
    (encXorFrom msg off s i n).length = msg.length := by
  induction n generalizing msg with
  | zero => rfl
  | succ k ih => simp [encXorFrom, ih, List.length_set]

/-- At `i = 0` the loop model is exactly `encXor`. -/
theorem encXorFrom_eq_encXor (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) (n : Nat) :
    encXorFrom msg off s 0 n = encXor msg off s n := by
  induction n generalizing msg with
  | zero => rfl
  | succ k ih => simp [encXorFrom, encXor, ih]

/-- One loop iteration peels the front index off the loop model. -/
theorem encXorFrom_step (msg : List (BitVec 32)) (off : Nat)
    (s : List (BitVec 32)) (i k : Nat) (w kk : BitVec 32)
    (hmsg : msg[off + i]? = some w)
    (hs : s[i]? = some kk) :
    encXorFrom msg off s i (k + 1) =
      encXorFrom (msg.set (off + i) (w ^^^ kk)) off s (i + 1) k := by
  induction k generalizing msg with
  | zero =>
    have e1 : off + i + 0 = off + i := by omega
    have e2 : i + 0 = i := by omega
    simp [encXorFrom, e1, e2, hmsg, hs]
  | succ k ih =>
    rw [encXorFrom_succ]
    rw [ih msg hmsg]
    rw [encXorFrom_succ]
    have e1 : off + i + (k + 1) = off + (i + 1) + k := by omega
    have e2 : i + (k + 1) = (i + 1) + k := by omega
    rw [e1, e2]

/-- One xor-body iteration: `msg[off+i] ^= s[i]; i++`. -/
theorem xorBodyFrag_correct (prog : Prog) (F : Nat)
    (s : List (BitVec 32)) (key : List (BitVec 32))
    (counter bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (iB : BitVec 64)
    (i : Nat) (hi : iB.toNat = i)
    (st : List (BitVec 32)) (w k : BitVec 32)
    (hmsg : msg[offN + i]? = some w)
    (hs : s[i]? = some k)
    (hadd : offN + i < 2 ^ 64)
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hsV : ∀ (msg' : List (BitVec 32)) (i' : BitVec 64),
      envLookup (pre ++ mkEncEnv key counter bB nonce msg' nwords bN offN i' st)
        "s" = some (.arr32 s)) :
    evalProgStmt prog F xorBodyFrag
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN (iB + BitVec.ofNat 64 1) st, .fellThrough) := by
  have hoffV : envLookup
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) "off" =
      some (.u64 (BitVec.ofNat 64 offN)) :=
    chainLookup pre _ "off" _ hpre (by decide)
      (mkEncEnv_off key counter bB nonce msg nwords bN offN iB st)
  have hiV : envLookup
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) "i" =
      some (.u64 iB) :=
    chainLookup pre _ "i" _ hpre (by decide)
      (mkEncEnv_i key counter bB nonce msg nwords bN offN iB st)
  have hovar : evalExpr (.var "off")
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 offN)) :=
    evalExpr_var_hit _ _ _ hoffV
  have hivar : evalExpr (.var "i")
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hiV
  have hmsgV : envLookup
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) "msg" =
      some (.arr32 msg) :=
    chainLookup pre _ "msg" _ hpre (by decide)
      (mkEncEnv_msg key counter bB nonce msg nwords bN offN iB st)
  have hsVuse := hsV msg iB
  have hoffN : (BitVec.ofNat 64 offN).toNat = offN := by
    have h : offN < 2 ^ 64 := by omega
    exact ofNat64_toNat offN h
  have haddN : (BitVec.ofNat 64 offN + iB).toNat = offN + i := by
    rw [u64add_toNat_exact _ _ (by rw [hoffN, hi]; exact hadd), hoffN, hi]
  have hidx : evalExpr (.uadd (.var "off") (.var "i"))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 offN + iB)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hovar hivar
  have hget : msg[(BitVec.ofNat 64 offN + iB).toNat]? = some w := by
    rw [haddN]; exact hmsg
  have hmv : evalExpr
      (.idxu "msg" (.uadd (.var "off") (.var "i")))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u32 w) :=
    evalExpr_idxu_ok _ _ _ _ _ _ hmsgV hidx hget
  have hsv : evalExpr (.idxu "s" (.var "i"))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u32 k) :=
    evalExpr_idxu_ok _ _ _ _ _ _ hsVuse hivar (by rw [hi]; exact hs)
  have hxv : evalExpr
      (.bxor (.idxu "msg" (.uadd (.var "off") (.var "i")))
        (.idxu "s" (.var "i")))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u32 (w ^^^ k)) :=
    evalExpr_bxor_u32 _ _ _ _ _ hmv hsv
  have hset : msg.set (BitVec.ofNat 64 offN + iB).toNat (w ^^^ k) =
      msg.set (offN + i) (w ^^^ k) := by rw [haddN]
  have harr : evalProgStmt prog F
      (.arrSet "msg" (.uadd (.var "off") (.var "i"))
        (.bxor (.idxu "msg" (.uadd (.var "off") (.var "i")))
          (.idxu "s" (.var "i"))))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN iB st, .fellThrough) := by
    have hu : envUpdate
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) "msg"
        (.arr32 (msg.set (BitVec.ofNat 64 offN + iB).toNat (w ^^^ k))) =
        some (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
          nwords bN offN iB st) := by
      rw [hset]
      exact chainUpdate pre _ "msg" _ _ hpre (by decide)
        (mkEncEnv_update_msg key counter bB nonce msg
          (msg.set (offN + i) (w ^^^ k)) nwords bN offN iB st)
    exact encArrSet prog F "msg" _ _
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st)
      (BitVec.ofNat 64 offN + iB) (w ^^^ k) msg w _ hidx hxv hmsgV hget hu
  have hlit1 : evalExpr (u64lit 1)
      (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hiV' : envLookup
      (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN iB st) "i" =
      some (.u64 iB) :=
    chainLookup pre _ "i" _ hpre (by decide)
      (mkEncEnv_i key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN iB st)
  have hivar' : evalExpr (.var "i")
      (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN iB st) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hiV'
  have hii : evalExpr (.uadd (.var "i") (u64lit 1))
      (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN iB st) =
      .ok (.u64 (iB + BitVec.ofNat 64 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hivar' hlit1
  have hasg : evalProgStmt prog F (.assign "i" (.uadd (.var "i") (u64lit 1)))
      (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN iB st) =
      .ok (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
        nwords bN offN (iB + BitVec.ofNat 64 1) st, .fellThrough) :=
    evalProgStmt_assign_ok prog F "i" _ _ _ _
      hii (chainUpdate pre _ "i" _ _ hpre (by decide)
        (mkEncEnv_update_i key counter bB nonce
          (msg.set (offN + i) (w ^^^ k)) nwords bN offN iB
          (iB + BitVec.ofNat 64 1) st))
  have hbody : xorBodyFrag =
      (.seq (.arrSet "msg" (.uadd (.var "off") (.var "i"))
        (.bxor (.idxu "msg" (.uadd (.var "off") (.var "i")))
          (.idxu "s" (.var "i"))))
        (.assign "i" (.uadd (.var "i") (u64lit 1)))) := rfl
  rw [hbody, evalProgStmt_seq_fallthrough _ _ _ _ _ _ harr]
  exact hasg


/-- Loop-exit: a false guard leaves the env unchanged (either fuel),
    in loop-model conclusion form. -/
theorem xorLoopFrag_exit (prog : Prog) (F : Nat)
    (s : List (BitVec 32)) (key : List (BitVec 32))
    (counter bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (iB : BitVec 64)
    (i N : Nat) (hi : iB.toNat = i) (hie : i = N)
    (st : List (BitVec 32))
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (bnd : CExpr) (loop : CStmt)
    (hloop : loop = .while_ (.ult (.var "i") bnd) xorBodyFrag)
    (hbnd : evalExpr bnd
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 N)))
    (hN64 : N < 2 ^ 64) :
    evalProgStmt prog F loop
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (pre ++ mkEncEnv key counter bB nonce
        (encXorFrom msg offN s i (N - i)) nwords bN offN
        (iB + BitVec.ofNat 64 (N - i)) st, .fellThrough) := by
  rw [hie] at hi ⊢
  have hiV : envLookup
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) "i" =
      some (.u64 iB) :=
    chainLookup pre _ "i" _ hpre (by decide)
      (mkEncEnv_i key counter bB nonce msg nwords bN offN iB st)
  have hN : (BitVec.ofNat 64 N).toNat = N := ofNat64_toNat N hN64
  have hfalse : iB.ult (BitVec.ofNat 64 N) = false := by
    rw [BitVec.ult_eq_decide, hi, hN]
    exact decide_eq_false (by omega)
  have hguardF : evalExpr (.ult (.var "i") bnd)
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 (.var "i") bnd
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st)
      iB (BitVec.ofNat 64 N) (evalExpr_var_hit _ _ _ hiV) hbnd
    rwa [hfalse] at h
  rw [hloop, evalProgStmt_while_false prog F _ _ _ hguardF]
  have eN : N - N = 0 := by omega
  have em0 : encXorFrom msg offN s N (N - N) = msg := by simp [eN, encXorFrom]
  have ew0 : iB + BitVec.ofNat 64 (N - N) = iB := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, eN, ofNat64_toNat 0 (by decide),
      Nat.add_zero, Nat.mod_eq_of_lt iB.isLt]
  rw [em0, ew0]

/-- The xor loop (full or tail) computes the loop model: fuel
    induction unrolling one body iteration at a time (M8 precedent);
    the bound expression is a parameter discharged per use. -/
theorem xorLoopFrag_correct (prog : Prog) (F : Nat)
    (s : List (BitVec 32)) (key : List (BitVec 32))
    (counter bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat) (iB : BitVec 64)
    (i N : Nat) (hi : iB.toNat = i)
    (st : List (BitVec 32))
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hsV : ∀ (msg' : List (BitVec 32)) (i' : BitVec 64),
      envLookup (pre ++ mkEncEnv key counter bB nonce msg' nwords bN offN i' st)
        "s" = some (.arr32 s))
    (bnd : CExpr) (loop : CStmt)
    (hloop : loop = .while_ (.ult (.var "i") bnd) xorBodyFrag)
    (hbnd : ∀ (msg' : List (BitVec 32)) (i' : BitVec 64),
      evalExpr bnd
        (pre ++ mkEncEnv key counter bB nonce msg' nwords bN offN i' st) =
        .ok (.u64 (BitVec.ofNat 64 N)))
    (hN64 : N < 2 ^ 64)
    (hiN : i ≤ N) (hF : N - i ≤ F)
    (hslen : s.length = 16) (hN16 : N ≤ 16)
    (hmsglen : offN + N ≤ msg.length)
    (hfit : offN + N < 2 ^ 64) :
    evalProgStmt prog F loop
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (pre ++ mkEncEnv key counter bB nonce
        (encXorFrom msg offN s i (N - i)) nwords bN offN
        (iB + BitVec.ofNat 64 (N - i)) st, .fellThrough) := by
  induction F generalizing i iB msg with
  | zero =>
    have hie : i = N := by omega
    exact xorLoopFrag_exit prog 0 s key counter bB nonce msg nwords bN offN
      iB i N hi hie st pre hpre bnd loop hloop (hbnd msg iB) hN64
  | succ F ih =>
    by_cases hie : i = N
    · exact xorLoopFrag_exit prog (F + 1) s key counter bB nonce msg nwords
        bN offN iB i N hi hie st pre hpre bnd loop hloop (hbnd msg iB) hN64
    · have hilt : i < N := by omega
      have hiV : envLookup
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) "i" =
          some (.u64 iB) :=
        chainLookup pre _ "i" _ hpre (by decide)
          (mkEncEnv_i key counter bB nonce msg nwords bN offN iB st)
      have hivar := evalExpr_var_hit _ _ _ hiV
      have hN : (BitVec.ofNat 64 N).toNat = N := ofNat64_toNat N hN64
      have htrue : iB.ult (BitVec.ofNat 64 N) = true := by
        rw [BitVec.ult_eq_decide, hi, hN]
        exact decide_eq_true (by omega)
      have hguardT : evalExpr (.ult (.var "i") bnd)
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 (.var "i") bnd
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st)
          iB (BitVec.ofNat 64 N) hivar (hbnd msg iB)
        rwa [htrue] at h
      obtain ⟨w, hgetm⟩ : ∃ w, msg[offN + i]? = some w :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨k, hgets⟩ : ∃ k, s[i]? = some k :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hadd : offN + i < 2 ^ 64 := by omega
      have hbody := xorBodyFrag_correct prog F s key counter bB nonce msg
        nwords bN offN iB i hi st w k hgetm hgets hadd pre hpre hsV
      have hwhile : evalProgStmt prog (F + 1) loop
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
          evalProgStmt prog F loop
            (pre ++ mkEncEnv key counter bB nonce (msg.set (offN + i) (w ^^^ k))
              nwords bN offN (iB + BitVec.ofNat 64 1) st) := by
        simp only [hloop,
          evalProgStmt_while_true prog F _ _ _ hguardT, hbody]
      rw [hwhile]
      have hi1 : (BitVec.ofNat 64 1).toNat = 1 :=
        ofNat64_toNat 1 (by decide)
      have hi' : (iB + BitVec.ofNat 64 1).toNat = i + 1 := by
        have hb : iB.toNat + (BitVec.ofNat 64 1).toNat < 2 ^ 64 := by
          rw [hi, hi1]
          calc i + 1 ≤ N := by omega
            _ ≤ offN + N := by omega
            _ < 2 ^ 64 := hfit
        rw [u64add_toNat_exact _ _ hb, hi, hi1]
      have hloop' := ih (i := i + 1) (iB := iB + BitVec.ofNat 64 1)
        (msg := msg.set (offN + i) (w ^^^ k)) (hi := hi')
        (hiN := by omega) (hF := by omega)
        (hmsglen := by rw [List.length_set]; exact hmsglen)
      have eN : N - i = (N - (i + 1)) + 1 := by omega
      have emsg : encXorFrom (msg.set (offN + i) (w ^^^ k)) offN s (i + 1)
          (N - (i + 1)) = encXorFrom msg offN s i (N - i) := by
        rw [eN]
        exact (encXorFrom_step msg offN s i (N - (i + 1)) w k hgetm hgets).symm
      have g : 1 + (N - (i + 1)) = N - i := by omega
      have eword : (iB + BitVec.ofNat 64 1) +
          BitVec.ofNat 64 (N - (i + 1)) =
          iB + BitVec.ofNat 64 (N - i) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, g]
      rw [emsg, eword] at hloop'
      exact hloop'

/-- Full-block xor loop from `i = 0`: computes `encXor msg off s 16`. -/
theorem xorFullFrag_correct (prog : Prog) (F : Nat)
    (s : List (BitVec 32)) (key : List (BitVec 32))
    (counter bB : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : BitVec 64) (bN offN : Nat)
    (st : List (BitVec 32))
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hsV : ∀ (msg' : List (BitVec 32)) (i' : BitVec 64),
      envLookup (pre ++ mkEncEnv key counter bB nonce msg' nwords bN offN i' st)
        "s" = some (.arr32 s))
    (hslen : s.length = 16)
    (hmsglen : offN + 16 ≤ msg.length)
    (hfit : offN + 16 < 2 ^ 64) (hF : 16 ≤ F) :
    evalProgStmt prog F xorFullFrag
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) st) =
      .ok (pre ++ mkEncEnv key counter bB nonce (encXor msg offN s 16) nwords
        bN offN (BitVec.ofNat 64 16) st, .fellThrough) := by
  have h := xorLoopFrag_correct prog F s key counter bB nonce msg nwords bN offN
    (BitVec.ofNat 64 0) 0 16 (ofNat64_toNat 0 (by decide)) st
    pre hpre hsV (u64lit 16) xorFullFrag
    rfl (fun msg' i' => by simp only [u64lit, evalExpr_lit, litVal])
    (by decide) (Nat.zero_le 16) (by simpa using hF) hslen (by omega) hmsglen hfit
  rw [Nat.sub_zero, encXorFrom_eq_encXor] at h
  have hw : BitVec.ofNat 64 0 + BitVec.ofNat 64 16 = BitVec.ofNat 64 16 := by
    simp [← BitVec.ofNat_add]
  rw [hw] at h
  exact h

/-- The admitted block call runs the K4 leaf at the same fuel
    (`callRet` discipline). -/
theorem blockCallFrag_correct (prog : Prog) (F : Nat)
    (ρ : Env) (st : List (BitVec 32))
    (hst : envLookup ρ "st" = some (.arr32 st))
    (h16 : 16 ≤ st.length)
    (hfind : findFunc prog "chacha20_block" = some chachaBlockFunc)
    (hF16 : 16 ≤ F) :
    evalProgStmt prog F blockCallFrag ρ =
      .ok (envExtend ρ "s" (.arr32 (addBackList st (chachaRounds 10 st) 16)),
        .fellThrough) := by
  have hargs : lookupArgs ρ ["st"] = some [.arr32 st] :=
    lookupArgs_cons_hit ρ "st" (.arr32 st) [] [] hst (lookupArgs_nil ρ)
  have hcall : evalFuncFuel F chachaBlockFunc [.arr32 st] =
      .ok (.arr32 (addBackList st (chachaRounds 10 st) 16)) := by
    rw [evalFuncFuel_chachaBlock F st h16 hF16]
    simp [chachaBlockFwd, h16]
  have hdef : blockCallFrag = .callRet "s" "chacha20_block" ["st"] := rfl
  rw [hdef]
  exact evalProgStmt_callRet_ok prog F "s" "chacha20_block" ["st"] ρ
    [.arr32 st] chachaBlockFunc
    (.arr32 (addBackList st (chachaRounds 10 st) 16)) hargs hfind hcall

/-- One full iteration: reset `i`, setup, block call, full xor, bump
    `b` and `off` (chain-prefix env in, extended chain out). -/
theorem fullIterFrag_correct (prog : Prog) (F : Nat)
    (key : List (BitVec 32)) (counter bB : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (bN offN : Nat) (iB : BitVec 64) (st : List (BitVec 32))
    (b : Nat) (hbN : bB.toNat = b)
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hst16 : st.length = 16)
    (hfind : findFunc prog "chacha20_block" = some chachaBlockFunc)
    (hmsglen : offN + 16 ≤ msg.length)
    (hfit : offN + 16 < 2 ^ 64)
    (hF16 : 16 ≤ F) :
    evalProgStmt prog F fullIterFrag
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter (bB + BitVec.ofNat 32 1) nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN (offN + 16) (BitVec.ofNat 64 16)
        (encSetup key counter b nonce), .fellThrough) := by
  have hi0eval : evalExpr (u64lit 0)
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hassi0 : evalProgStmt prog F (.assign "i" (u64lit 0))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) st, .fellThrough) :=
    evalProgStmt_assign_ok prog F "i" (u64lit 0)
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) _ _
      hi0eval (chainUpdate pre _ "i" _ _ hpre (by decide)
        (mkEncEnv_update_i key counter bB nonce msg nwords bN offN iB
          (BitVec.ofNat 64 0) st))
  have hsetup := setupFrag_correct prog F key counter bB b hbN nonce msg
    nwords bN offN (BitVec.ofNat 64 0) st pre hpre hk8 hn3 hst16
  have hst : envLookup
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce)) "st" =
      some (.arr32 (encSetup key counter b nonce)) :=
    chainLookup pre _ "st" _ hpre (by decide)
      (mkEncEnv_st key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce))
  have h16 : 16 ≤ (encSetup key counter b nonce).length := by
    have hl : (encSetup key counter b nonce).length = 16 :=
      encSetup_length key counter b nonce hk8 hn3
    omega
  have hcall := blockCallFrag_correct prog F
    (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN
      (BitVec.ofNat 64 0) (encSetup key counter b nonce))
    (encSetup key counter b nonce) hst h16 hfind hF16
  have hcallS : evalProgStmt prog F blockCallFrag
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce)) =
      .ok ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce), .fellThrough) :=
    hcall
  have hpre2 : ∀ p ∈ ("s", .arr32
      (addBackList (encSetup key counter b nonce)
        (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre,
      p.1 = "s" ∨ p.1 = "ntail" := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · left; rfl
    · exact hpre p hp
  have hsV2 : ∀ (msg' : List (BitVec 32)) (i' : BitVec 64),
      envLookup ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter bB nonce msg' nwords bN offN i'
        (encSetup key counter b nonce)) "s" =
        some (.arr32
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16)) := by
    intro msg' i'
    simp [List.cons_append, envLookup]
  have hslen : (addBackList (encSetup key counter b nonce)
      (chachaRounds 10 (encSetup key counter b nonce)) 16).length = 16 := by
    rw [addBackList_length, encSetup_length key counter b nonce hk8 hn3]
  have hxor := xorFullFrag_correct prog F
    (addBackList (encSetup key counter b nonce)
      (chachaRounds 10 (encSetup key counter b nonce)) 16)
    key counter bB nonce msg nwords bN offN
    (encSetup key counter b nonce)
    ((("s", .arr32
      (addBackList (encSetup key counter b nonce)
        (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre))
    hpre2 hsV2 hslen hmsglen hfit hF16
  have hbvar : evalExpr (.var "b")
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter bB nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok (.u32 bB) :=
    evalExpr_var_hit _ _ _
      (chainLookup _ _ "b" _ hpre2 (by decide)
        (mkEncEnv_b key counter bB nonce
          (encXor msg offN
            (addBackList (encSetup key counter b nonce)
              (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
          nwords bN offN (BitVec.ofNat 64 16) (encSetup key counter b nonce)))
  have h1b : evalExpr (u32lit 1)
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter bB nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok (.u32 (BitVec.ofNat 32 1)) := by
    simp only [u32lit, evalExpr_lit, litVal]
  have hbeval : evalExpr (.uadd (.var "b") (u32lit 1))
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter bB nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok (.u32 (bB + BitVec.ofNat 32 1)) :=
    evalExpr_uadd_u32 _ _ _ _ _ hbvar h1b
  have hassignb : evalProgStmt prog F
      (.assign "b" (.uadd (.var "b") (u32lit 1)))
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter bB nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter (bB + BitVec.ofNat 32 1) nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce), .fellThrough) :=
    evalProgStmt_assign_ok prog F "b" (.uadd (.var "b") (u32lit 1)) _ _ _
      hbeval (chainUpdate _ _ "b" _ _ hpre2 (by decide)
        (mkEncEnv_update_b key counter bB (bB + BitVec.ofNat 32 1) nonce
          (encXor msg offN
            (addBackList (encSetup key counter b nonce)
              (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
          nwords bN offN (BitVec.ofNat 64 16) (encSetup key counter b nonce)))
  have hoffvar : evalExpr (.var "off")
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter (bB + BitVec.ofNat 32 1) nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok (.u64 (BitVec.ofNat 64 offN)) :=
    evalExpr_var_hit _ _ _
      (chainLookup _ _ "off" _ hpre2 (by decide)
        (mkEncEnv_off key counter (bB + BitVec.ofNat 32 1) nonce
          (encXor msg offN
            (addBackList (encSetup key counter b nonce)
              (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
          nwords bN offN (BitVec.ofNat 64 16) (encSetup key counter b nonce)))
  have h16off : evalExpr (u64lit 16)
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter (bB + BitVec.ofNat 32 1) nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok (.u64 (BitVec.ofNat 64 16)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hoffeval : evalExpr (.uadd (.var "off") (u64lit 16))
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter (bB + BitVec.ofNat 32 1) nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok (.u64 (BitVec.ofNat 64 offN + BitVec.ofNat 64 16)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hoffvar h16off
  have hnorm : BitVec.ofNat 64 offN + BitVec.ofNat 64 16 =
      BitVec.ofNat 64 (offN + 16) :=
    (BitVec.ofNat_add _ _).symm
  have huoff := chainUpdate _ _ "off" _ _ hpre2 (by decide)
    (mkEncEnv_update_off key counter (bB + BitVec.ofNat 32 1) nonce
      (encXor msg offN
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
      nwords bN offN (offN + 16) (BitVec.ofNat 64 16)
      (encSetup key counter b nonce))
  rw [← hnorm] at huoff
  have hassignoff : evalProgStmt prog F
      (.assign "off" (.uadd (.var "off") (u64lit 16)))
      ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter (bB + BitVec.ofNat 32 1) nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN offN (BitVec.ofNat 64 16)
        (encSetup key counter b nonce)) =
      .ok ((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre) ++
        mkEncEnv key counter (bB + BitVec.ofNat 32 1) nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
        nwords bN (offN + 16) (BitVec.ofNat 64 16)
        (encSetup key counter b nonce), .fellThrough) :=
    evalProgStmt_assign_ok prog F "off" (.uadd (.var "off") (u64lit 16)) _ _ _
      hoffeval huoff
  have hiter : fullIterFrag =
      (.seq (.assign "i" (u64lit 0))
      (.seq setupFrag
      (.seq blockCallFrag
      (.seq xorFullFrag
      (.seq (.assign "b" (.uadd (.var "b") (u32lit 1)))
        (.assign "off" (.uadd (.var "off") (u64lit 16)))))))) := rfl
  obtain ⟨ρsetup, hsetupE, rfl⟩ := hsetup
  rw [hiter,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hassi0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hsetupE,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hcallS,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hxor,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hassignb]
  exact hassignoff

/-- `let_` at program level (call-free, any fuel). -/
theorem evalProgStmt_let_ok (prog : Prog) (F : Nat) (x : String)
    (ty : CType) (e : CExpr) (ρ : Env) (v : Value)
    (h : evalExpr e ρ = .ok v) :
    evalProgStmt prog F (.let_ x ty e) ρ =
      .ok (envExtend ρ x v, .fellThrough) := by
  have hfu := evalStmtFuel_let_ F x ty e ρ v h
  cases F with
  | zero => simpa [evalProgStmt] using hfu
  | succ F => simpa [evalProgStmt] using hfu

/-- `une` on two `u64` words. -/
theorem evalExpr_une_u64 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 64)
    (h₁ : evalExpr e₁ ρ = .ok (.u64 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u64 y)) :
    evalExpr (.une e₁ e₂) ρ = .ok (.b (x != y)) := by
  simp [evalExpr, h₁, h₂]

/-- The `ntail` let evaluates the wrap-free difference (needs `off ≤ nwords`). -/
theorem tailNtail_ok (prog : Prog) (F : Nat)
    (key : List (BitVec 32)) (counter bB : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (bN offN : Nat) (iB : BitVec 64) (st : List (BitVec 32))
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hle : offN ≤ nwords.toNat) :
    evalProgStmt prog F (.let_ "ntail" (.u 64) (.usub (.var "nwords") (.var "off")))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st), .fellThrough) ∧
    (nwords - BitVec.ofNat 64 offN).toNat = nwords.toNat - offN := by
  have hoff64 : offN < 2 ^ 64 := by have h := nwords.isLt; omega
  have hoffNat : (BitVec.ofNat 64 offN).toNat = offN := ofNat64_toNat offN hoff64
  have hleB : BitVec.ofNat 64 offN ≤ nwords := by
    rw [BitVec.le_def, hoffNat]; exact hle
  have hsub : (nwords - BitVec.ofNat 64 offN).toNat = nwords.toNat - offN := by
    rw [BitVec.toNat_sub_of_le hleB, hoffNat]
  have hnV := chainLookup pre _ "nwords" _ hpre (by decide)
    (mkEncEnv_nwords key counter bB nonce msg nwords bN offN iB st)
  have hoV := chainLookup pre _ "off" _ hpre (by decide)
    (mkEncEnv_off key counter bB nonce msg nwords bN offN iB st)
  have he : evalExpr (.usub (.var "nwords") (.var "off"))
      (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (nwords - BitVec.ofNat 64 offN)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ (evalExpr_var_hit _ _ _ hnV)
      (evalExpr_var_hit _ _ _ hoV)
  have hlet := evalProgStmt_let_ok prog F "ntail" (.u 64) _ _ _ he
  refine ⟨?_, hsub⟩
  simpa [envExtend, List.cons_append] using hlet

/-- Tail `if` with empty tail: guard false, env keeps `ntail`. -/
theorem tailIf_empty (prog : Prog) (F : Nat)
    (key : List (BitVec 32)) (counter bB : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (bN offN : Nat) (iB : BitVec 64) (st : List (BitVec 32))
    (pre : Env)
    (hsub : (nwords - BitVec.ofNat 64 offN).toNat = nwords.toNat - offN)
    (hnt0 : nwords.toNat - offN = 0) :
    evalProgStmt prog F
      (.if_ (.une (.var "ntail") (u64lit 0)) tailFrag .skip)
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st), .fellThrough) := by
  have hntEq : nwords - BitVec.ofNat 64 offN = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [hsub, hnt0, ofNat64_toNat 0 (by decide)]
  have hlk : envLookup
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) "ntail" =
      some (.u64 (nwords - BitVec.ofNat 64 offN)) := by
    simp [List.cons_append, envLookup]
  have h0 : evalExpr (u64lit 0)
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hbb : (nwords - BitVec.ofNat 64 offN != BitVec.ofNat 64 0) = false := by
    rw [hntEq]
    decide
  have hg : evalExpr (.une (.var "ntail") (u64lit 0))
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.b false) := by
    have h := evalExpr_une_u64 (.var "ntail") (u64lit 0) _ _ _
      (evalExpr_var_hit _ _ _ hlk) h0
    rwa [hbb] at h
  rw [evalProgStmt_if_false _ _ _ _ _ _ hg]
  cases F <;> simp [evalProgStmt, evalStmtFuel, evalStmtZero, evalStmtWith]

/-- Tail `if` with `ntN > 0` words left: guard true, tail block
    computes the partial xor. -/
theorem tailIf_nonempty (prog : Prog) (F : Nat)
    (key : List (BitVec 32)) (counter bB : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (bN offN : Nat) (iB : BitVec 64) (st : List (BitVec 32))
    (b : Nat) (hbN : bB.toNat = b)
    (ntN : Nat) (hntN : nwords.toNat - offN = ntN)
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hst16 : st.length = 16)
    (hfind : findFunc prog "chacha20_block" = some chachaBlockFunc)
    (hle : offN ≤ nwords.toNat) (hnt16 : ntN ≤ 16)
    (hmsg : msg.length = nwords.toNat)
    (hsub : (nwords - BitVec.ofNat 64 offN).toNat = nwords.toNat - offN)
    (hntNe : ntN ≠ 0)
    (hF16 : 16 ≤ F) (hFnt : ntN ≤ F) :
    evalProgStmt prog F
      (.if_ (.une (.var "ntail") (u64lit 0)) tailFrag .skip)
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) ::
        ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre)) ++
        mkEncEnv key counter bB nonce
        (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) ntN)
        nwords bN offN (BitVec.ofNat 64 ntN)
        (encSetup key counter b nonce), .fellThrough) := by
  have hN64 : ntN < 2 ^ 64 := by omega
  have hntNat : (BitVec.ofNat 64 ntN).toNat = ntN := ofNat64_toNat ntN hN64
  have hsubN : (nwords - BitVec.ofNat 64 offN).toNat = ntN := by
    rw [hsub, hntN]
  have hntEq : nwords - BitVec.ofNat 64 offN = BitVec.ofNat 64 ntN :=
    BitVec.eq_of_toNat_eq (by rw [hsubN, hntNat])
  have hpreT : ∀ p ∈ ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre,
      p.1 = "s" ∨ p.1 = "ntail" := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · right; rfl
    · exact hpre p hp
  have hlk : envLookup
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) "ntail" =
      some (.u64 (nwords - BitVec.ofNat 64 offN)) := by
    simp [List.cons_append, envLookup]
  have h0 : evalExpr (u64lit 0)
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hne : nwords - BitVec.ofNat 64 offN ≠ BitVec.ofNat 64 0 := by
    intro hcon
    apply hntNe
    have hconT := congrArg BitVec.toNat hcon
    rw [hsubN, ofNat64_toNat 0 (by decide)] at hconT
    exact hconT
  have hbb : (nwords - BitVec.ofNat 64 offN != BitVec.ofNat 64 0) = true :=
    (bne_iff_ne).mpr hne
  have hg : evalExpr (.une (.var "ntail") (u64lit 0))
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.b true) := by
    have h := evalExpr_une_u64 (.var "ntail") (u64lit 0) _ _ _
      (evalExpr_var_hit _ _ _ hlk) h0
    rwa [hbb] at h
  rw [evalProgStmt_if_true _ _ _ _ _ _ hg]
  have hi0eval : evalExpr (u64lit 0)
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hassi0 : evalProgStmt prog F (.assign "i" (u64lit 0))
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
      .ok ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) st, .fellThrough) :=
    evalProgStmt_assign_ok prog F "i" (u64lit 0) _ _ _
      hi0eval (chainUpdate _ _ "i" _ _ hpreT (by decide)
        (mkEncEnv_update_i key counter bB nonce msg nwords bN offN iB
          (BitVec.ofNat 64 0) st))
  have hsetup := setupFrag_correct prog F key counter bB b hbN nonce msg
    nwords bN offN (BitVec.ofNat 64 0) st
    (("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) hpreT hk8 hn3 hst16
  obtain ⟨ρsetup, hsetupE, rfl⟩ := hsetup
  have hstL : envLookup
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce)) "st" =
      some (.arr32 (encSetup key counter b nonce)) :=
    chainLookup _ _ "st" _ hpreT (by decide)
      (mkEncEnv_st key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce))
  have h16 : 16 ≤ (encSetup key counter b nonce).length := by
    have hl : (encSetup key counter b nonce).length = 16 :=
      encSetup_length key counter b nonce hk8 hn3
    omega
  have hcall := blockCallFrag_correct prog F
    ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
      mkEncEnv key counter bB nonce msg nwords bN offN
      (BitVec.ofNat 64 0) (encSetup key counter b nonce))
    (encSetup key counter b nonce) hstL h16 hfind hF16
  have hcallS : evalProgStmt prog F blockCallFrag
      ((("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre) ++
        mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce)) =
      .ok (((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) ::
        ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre)) ++
        mkEncEnv key counter bB nonce msg nwords bN offN
        (BitVec.ofNat 64 0) (encSetup key counter b nonce), .fellThrough) :=
    hcall
  have hpreS : ∀ p ∈ ("s", .arr32
      (addBackList (encSetup key counter b nonce)
        (chachaRounds 10 (encSetup key counter b nonce)) 16)) ::
      ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre,
      p.1 = "s" ∨ p.1 = "ntail" := by
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · left; rfl
    · right; rfl
    · exact hpre p hp
  have hsVTail : ∀ (msg' : List (BitVec 32)) (i' : BitVec 64),
      envLookup (((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) ::
        ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre)) ++
        mkEncEnv key counter bB nonce msg' nwords bN offN i'
        (encSetup key counter b nonce)) "s" =
        some (.arr32
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16)) := by
    intro msg' i'
    simp [List.cons_append, envLookup]
  have hbndTail : ∀ (msg' : List (BitVec 32)) (i' : BitVec 64),
      evalExpr (.var "ntail")
        (((("s", .arr32
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16)) ::
          ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre)) ++
          mkEncEnv key counter bB nonce msg' nwords bN offN i'
          (encSetup key counter b nonce)) =
        .ok (.u64 (BitVec.ofNat 64 ntN)) := by
    intro msg' i'
    have hlkT : envLookup (((("s", .arr32
        (addBackList (encSetup key counter b nonce)
          (chachaRounds 10 (encSetup key counter b nonce)) 16)) ::
        ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre)) ++
        mkEncEnv key counter bB nonce msg' nwords bN offN i'
        (encSetup key counter b nonce)) "ntail" =
        some (.u64 (nwords - BitVec.ofNat 64 offN)) := by
      simp [List.cons_append, envLookup]
    calc evalExpr (.var "ntail") _ = .ok (.u64 (nwords - BitVec.ofNat 64 offN)) :=
          evalExpr_var_hit _ _ _ hlkT
      _ = .ok (.u64 (BitVec.ofNat 64 ntN)) := by rw [hntEq]
  have hslen : (addBackList (encSetup key counter b nonce)
      (chachaRounds 10 (encSetup key counter b nonce)) 16).length = 16 := by
    rw [addBackList_length, encSetup_length key counter b nonce hk8 hn3]
  have hmsglen : offN + ntN ≤ msg.length := by
    have h := nwords.isLt; omega
  have hfit : offN + ntN < 2 ^ 64 := by
    have h := nwords.isLt; omega
  have hxor := xorLoopFrag_correct prog F
    (addBackList (encSetup key counter b nonce)
      (chachaRounds 10 (encSetup key counter b nonce)) 16)
    key counter bB nonce msg nwords bN offN
    (BitVec.ofNat 64 0) 0 ntN (ofNat64_toNat 0 (by decide))
    (encSetup key counter b nonce)
    ((("s", .arr32
      (addBackList (encSetup key counter b nonce)
        (chachaRounds 10 (encSetup key counter b nonce)) 16)) ::
      ("ntail", .u64 (nwords - BitVec.ofNat 64 offN)) :: pre))
    hpreS hsVTail (.var "ntail") xorTailFrag
    rfl hbndTail hN64 (Nat.zero_le ntN) (by omega) hslen hnt16 hmsglen hfit
  rw [Nat.sub_zero, encXorFrom_eq_encXor] at hxor
  have hw : BitVec.ofNat 64 0 + BitVec.ofNat 64 ntN = BitVec.ofNat 64 ntN := by
    simp [← BitVec.ofNat_add]
  rw [hw] at hxor
  have htail : tailFrag =
      (.seq (.assign "i" (u64lit 0))
      (.seq setupFrag
      (.seq blockCallFrag xorTailFrag))) := rfl
  rw [htail,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hassi0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hsetupE,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hcallS]
  exact hxor

/-- Outer loop: full iterations until `off + 16 > nwords`; the fuel-free
    list model is invariant across the loop (chain-prefix env). -/
theorem outerWhile_post (prog : Prog) (F : Nat)
    (key : List (BitVec 32)) (counter bB : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (bN offN : Nat) (iB : BitVec 64) (st : List (BitVec 32))
    (b : Nat) (hbN : bB.toNat = b) (hoff : offN = 16 * b)
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hst16 : st.length = 16)
    (hfind : findFunc prog "chacha20_block" = some chachaBlockFunc)
    (hle : offN ≤ nwords.toNat)
    (hsize : nwords.toNat + 16 < 2 ^ 64)
    (hmsg : msg.length = nwords.toNat)
    (h32 : b + (nwords.toNat - offN) / 16 < 2 ^ 32)
    (hF : (nwords.toNat - offN) / 16 + 16 ≤ F) :
    ∃ (preW : Env) (bBW : BitVec 32) (bFW offFW : Nat) (iBW : BitVec 64)
      (stW : List (BitVec 32)) (msgMid : List (BitVec 32)),
      (∀ p ∈ preW, p.1 = "s" ∨ p.1 = "ntail") ∧
      bBW.toNat = bFW ∧ offFW = 16 * bFW ∧
      offFW ≤ nwords.toNat ∧ nwords.toNat < offFW + 16 ∧
      stW.length = 16 ∧ msgMid.length = nwords.toNat ∧
      evalProgStmt prog F outerWhileFrag
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (preW ++ mkEncEnv key counter bBW nonce msgMid nwords bN offFW iBW stW,
          .fellThrough) ∧
      chacha20EncryptList key counter nonce msg nwords.toNat offN b =
        chacha20EncryptList key counter nonce msgMid nwords.toNat offFW bFW := by
  induction F generalizing b bB offN msg pre iB st with
  | zero => exact False.elim (by omega)
  | succ F ih =>
    have hoff64 : offN + 16 < 2 ^ 64 := by omega
    have hnVoff : evalExpr (.var "off")
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (.u64 (BitVec.ofNat 64 offN)) :=
      evalExpr_var_hit _ _ _
        (chainLookup pre _ "off" _ hpre (by decide)
          (mkEncEnv_off key counter bB nonce msg nwords bN offN iB st))
    have h16v : evalExpr (u64lit 16)
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (.u64 (BitVec.ofNat 64 16)) := by
      simp only [u64lit, evalExpr_lit, litVal]
    have huoff : evalExpr (.uadd (.var "off") (u64lit 16))
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (.u64 (BitVec.ofNat 64 offN + BitVec.ofNat 64 16)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hnVoff h16v
    have hnVn : evalExpr (.var "nwords")
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (.u64 nwords) :=
      evalExpr_var_hit _ _ _
        (chainLookup pre _ "nwords" _ hpre (by decide)
          (mkEncEnv_nwords key counter bB nonce msg nwords bN offN iB st))
    have h1v : evalExpr (u64lit 1)
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by
      simp only [u64lit, evalExpr_lit, litVal]
    have hun : evalExpr (.uadd (.var "nwords") (u64lit 1))
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (.u64 (nwords + BitVec.ofNat 64 1)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hnVn h1v
    have hoffNorm : BitVec.ofNat 64 offN + BitVec.ofNat 64 16 =
        BitVec.ofNat 64 (offN + 16) := (BitVec.ofNat_add _ _).symm
    have hoffT : (BitVec.ofNat 64 offN + BitVec.ofNat 64 16).toNat =
        offN + 16 := by
      rw [hoffNorm, ofNat64_toNat _ hoff64]
    have hnT : (nwords + BitVec.ofNat 64 1).toNat = nwords.toNat + 1 := by
      have h1 : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    by_cases hle16 : offN + 16 ≤ nwords.toNat
    · have htrue : (BitVec.ofNat 64 offN + BitVec.ofNat 64 16).ult
          (nwords + BitVec.ofNat 64 1) = true := by
        rw [BitVec.ult_eq_decide, hoffT, hnT]
        exact decide_eq_true (by omega)
      have hguardT : evalExpr
          (.ult (.uadd (.var "off") (u64lit 16))
            (.uadd (.var "nwords") (u64lit 1)))
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huoff hun
        rwa [htrue] at h
      have hF16 : 16 ≤ F := by omega
      have hmsglen : offN + 16 ≤ msg.length := by omega
      have hfit : offN + 16 < 2 ^ 64 := by omega
      have hiter := fullIterFrag_correct prog F key counter bB nonce msg
        nwords bN offN iB st b hbN pre hpre hk8 hn3 hst16 hfind
        hmsglen hfit hF16
      have hblt : b + 1 < 2 ^ 32 := by omega
      have hbB : bB = BitVec.ofNat 32 b :=
        BitVec.eq_of_toNat_eq (by rw [hbN, ofNat32_toNat b (by omega)])
      have hbBof : bB + BitVec.ofNat 32 1 = BitVec.ofNat 32 (b + 1) := by
        rw [hbB, ofNat32_add_one]
      rw [hbBof] at hiter
      have hpre1 : ∀ p ∈ ("s", .arr32
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre,
          p.1 = "s" ∨ p.1 = "ntail" := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · left; rfl
        · exact hpre p hp
      have hst1 : (encSetup key counter b nonce).length = 16 :=
        encSetup_length key counter b nonce hk8 hn3
      have hbN' : (BitVec.ofNat 32 (b + 1)).toNat = b + 1 :=
        ofNat32_toNat (b + 1) hblt
      have hoff' : offN + 16 = 16 * (b + 1) := by omega
      have hle' : offN + 16 ≤ nwords.toNat := hle16
      have hmsg' : (encXor msg offN
          (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16) 16).length =
          nwords.toNat := by
        rw [encXor_length, hmsg]
      have h32' : b + 1 + (nwords.toNat - (offN + 16)) / 16 < 2 ^ 32 := by omega
      have hF' : (nwords.toNat - (offN + 16)) / 16 + 16 ≤ F := by omega
      obtain ⟨preW, bBW, bFW, offFW, iBW, stW, msgMid,
          hpreW, hbNW, hoffW, hleW, hexitW, hstW, hmsgW, hWhile, hList⟩ :=
        ih (b := b + 1) (bB := BitVec.ofNat 32 (b + 1)) (offN := offN + 16)
          (msg := encXor msg offN
            (addBackList (encSetup key counter b nonce)
              (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
          (pre := ("s", .arr32
            (addBackList (encSetup key counter b nonce)
              (chachaRounds 10 (encSetup key counter b nonce)) 16)) :: pre)
          (iB := BitVec.ofNat 64 16)
          (st := encSetup key counter b nonce)
          (hbN := hbN') (hoff := hoff') (hpre := hpre1) (hst16 := hst1)
          (hle := hle') (hmsg := hmsg') (h32 := h32') (hF := hF')
      have hblockFwd : chachaBlockFwd (encSetup key counter b nonce) =
          .ok (.arr32 (addBackList (encSetup key counter b nonce)
            (chachaRounds 10 (encSetup key counter b nonce)) 16)) := by
        have h16 : 16 ≤ (encSetup key counter b nonce).length := by
          rw [hst1]; omega
        simp [chachaBlockFwd, h16]
      have hunfold : chacha20EncryptList key counter nonce msg nwords.toNat offN b =
          chacha20EncryptList key counter nonce
            (encXor msg offN
              (addBackList (encSetup key counter b nonce)
                (chachaRounds 10 (encSetup key counter b nonce)) 16) 16)
            nwords.toNat (offN + 16) (b + 1) := by
        rw [chacha20EncryptList.eq_def key counter nonce msg nwords.toNat offN b,
          ite_eq_left ⟨hk8, hn3, by omega⟩,
          ite_eq_left (by omega : offN + 16 < nwords.toNat + 1), hblockFwd]
      have hWhileFull : evalProgStmt prog (F + 1) outerWhileFrag
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
          .ok (preW ++ mkEncEnv key counter bBW nonce msgMid nwords bN offFW iBW stW,
            .fellThrough) := by
        simp only [outerWhileFrag,
          evalProgStmt_while_true prog F _ _ _ hguardT, hiter]
        exact hWhile
      refine ⟨preW, bBW, bFW, offFW, iBW, stW, msgMid,
        hpreW, hbNW, hoffW, hleW, hexitW, hstW, hmsgW, hWhileFull, ?_⟩
      rw [hunfold]; exact hList
    · have hfalse : (BitVec.ofNat 64 offN + BitVec.ofNat 64 16).ult
          (nwords + BitVec.ofNat 64 1) = false := by
        rw [BitVec.ult_eq_decide, hoffT, hnT]
        exact decide_eq_false (by omega)
      have hguardF : evalExpr
          (.ult (.uadd (.var "off") (u64lit 16))
            (.uadd (.var "nwords") (u64lit 1)))
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huoff hun
        rwa [hfalse] at h
      have hWhileExit : evalProgStmt prog (F + 1) outerWhileFrag
          (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
          .ok (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st,
            .fellThrough) := by
        simp only [outerWhileFrag,
          evalProgStmt_while_false prog (F + 1) _ _ _ hguardF]
      refine ⟨pre, bB, b, offN, iB, st, msg,
        hpre, hbN, hoff, hle, by omega, hst16, hmsg, hWhileExit, rfl⟩

/-- Outer loop plus tail: the emitted suffix computes the fuel-free
    list model (chain-prefix env). -/
theorem outerTail_correct (prog : Prog) (F : Nat)
    (key : List (BitVec 32)) (counter bB : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (bN offN : Nat) (iB : BitVec 64) (st : List (BitVec 32))
    (b : Nat) (hbN : bB.toNat = b) (hoff : offN = 16 * b)
    (pre : Env) (hpre : ∀ p ∈ pre, p.1 = "s" ∨ p.1 = "ntail")
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hst16 : st.length = 16)
    (hfind : findFunc prog "chacha20_block" = some chachaBlockFunc)
    (hle : offN ≤ nwords.toNat)
    (hsize : nwords.toNat + 16 < 2 ^ 64)
    (hmsg : msg.length = nwords.toNat)
    (h32 : b + (nwords.toNat - offN) / 16 < 2 ^ 32)
    (hF : (nwords.toNat - offN) / 16 + 16 ≤ F) :
    ∃ (preT : Env) (bT : BitVec 32) (offT : Nat) (iT : BitVec 64)
      (stT : List (BitVec 32)) (msgFin : List (BitVec 32)),
      (∀ p ∈ preT, p.1 = "s" ∨ p.1 = "ntail") ∧
      msgFin.length = nwords.toNat ∧
      evalProgStmt prog F
        (.seq outerWhileFrag
          (.seq (.let_ "ntail" (.u 64) (.usub (.var "nwords") (.var "off")))
            (.seq (.if_ (.une (.var "ntail") (u64lit 0)) tailFrag .skip)
              (.return_ (.var "msg")))))
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (preT ++ mkEncEnv key counter bT nonce msgFin nwords bN offT iT stT,
          .returned (.arr32 msgFin)) ∧
      chacha20EncryptList key counter nonce msg nwords.toNat offN b =
        .ok msgFin := by
  obtain ⟨preW, bBW, bFW, offFW, iBW, stW, msgMid,
      hpreW, hbNW, hoffW, hleW, hexitW, hstW, hmsgW, hWhile, hListMid⟩ :=
    outerWhile_post prog F key counter bB nonce msg nwords bN offN iB st
      b hbN hoff pre hpre hk8 hn3 hst16 hfind hle hsize hmsg h32 hF
  by_cases hnt0 : nwords.toNat - offFW = 0
  · obtain ⟨hLet, hsubW⟩ := tailNtail_ok prog F key counter bBW nonce msgMid
      nwords bN offFW iBW stW preW hpreW hleW
    have hpreT : ∀ p ∈ ("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW,
        p.1 = "s" ∨ p.1 = "ntail" := by
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · right; rfl
      · exact hpreW p hp
    have hIf := tailIf_empty prog F key counter bBW nonce msgMid nwords
      bN offFW iBW stW preW hsubW hnt0
    have hRetV : evalExpr (.var "msg")
        ((("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW) ++
          mkEncEnv key counter bBW nonce msgMid nwords bN offFW iBW stW) =
        .ok (.arr32 msgMid) :=
      evalExpr_var_hit _ _ _
        (chainLookup _ _ "msg" _ hpreT (by decide)
          (mkEncEnv_msg key counter bBW nonce msgMid nwords bN offFW iBW stW))
    have hRet := evalProgStmt_return prog F (.var "msg") _ _ hRetV
    have hListW : chacha20EncryptList key counter nonce msgMid nwords.toNat
        offFW bFW = .ok msgMid := by
      rw [chacha20EncryptList.eq_def key counter nonce msgMid nwords.toNat
        offFW bFW,
        ite_eq_left ⟨hk8, hn3, by omega⟩,
        ite_eq_right (by omega : ¬ offFW + 16 < nwords.toNat + 1)]
      show (if nwords.toNat - offFW = 0 then _ else _) = Except.ok msgMid
      rw [ite_eq_left hnt0]
    have hEval : evalProgStmt prog F
        (.seq outerWhileFrag
          (.seq (.let_ "ntail" (.u 64) (.usub (.var "nwords") (.var "off")))
            (.seq (.if_ (.une (.var "ntail") (u64lit 0)) tailFrag .skip)
              (.return_ (.var "msg")))))
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (((("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW) ++
          mkEncEnv key counter bBW nonce msgMid nwords bN offFW iBW stW),
          .returned (.arr32 msgMid)) := by
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hWhile,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hLet,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hIf]
      exact hRet
    refine ⟨(("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW),
      bBW, offFW, iBW, stW, msgMid, hpreT, hmsgW, hEval, ?_⟩
    rw [hListMid]; exact hListW
  · have hF16 : 16 ≤ F := by omega
    have hFnt : nwords.toNat - offFW ≤ F := by omega
    have hnt16 : nwords.toNat - offFW ≤ 16 := by omega
    obtain ⟨hLet, hsubW⟩ := tailNtail_ok prog F key counter bBW nonce msgMid
      nwords bN offFW iBW stW preW hpreW hleW
    have hIf := tailIf_nonempty prog F key counter bBW nonce msgMid nwords
      bN offFW iBW stW bFW hbNW (nwords.toNat - offFW) rfl
      preW hpreW hk8 hn3 hstW hfind hleW hnt16 hmsgW hsubW hnt0 hF16 hFnt
    have hpreT : ∀ p ∈ ("s", .arr32
        (addBackList (encSetup key counter bFW nonce)
          (chachaRounds 10 (encSetup key counter bFW nonce)) 16)) ::
        ("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW,
        p.1 = "s" ∨ p.1 = "ntail" := by
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · left; rfl
      · right; rfl
      · exact hpreW p hp
    have hRetV : evalExpr (.var "msg")
        (((("s", .arr32
          (addBackList (encSetup key counter bFW nonce)
            (chachaRounds 10 (encSetup key counter bFW nonce)) 16)) ::
          ("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW)) ++
          mkEncEnv key counter bBW nonce
          (encXor msgMid offFW
            (addBackList (encSetup key counter bFW nonce)
              (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
            (nwords.toNat - offFW))
          nwords bN offFW (BitVec.ofNat 64 (nwords.toNat - offFW))
          (encSetup key counter bFW nonce)) =
        .ok (.arr32 (encXor msgMid offFW
          (addBackList (encSetup key counter bFW nonce)
            (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
          (nwords.toNat - offFW))) :=
      evalExpr_var_hit _ _ _
        (chainLookup _ _ "msg" _ hpreT (by decide)
          (mkEncEnv_msg key counter bBW nonce
            (encXor msgMid offFW
              (addBackList (encSetup key counter bFW nonce)
                (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
              (nwords.toNat - offFW))
            nwords bN offFW (BitVec.ofNat 64 (nwords.toNat - offFW))
            (encSetup key counter bFW nonce)))
    have hRet := evalProgStmt_return prog F (.var "msg") _ _ hRetV
    have hblockFwdW : chachaBlockFwd (encSetup key counter bFW nonce) =
        .ok (.arr32 (addBackList (encSetup key counter bFW nonce)
          (chachaRounds 10 (encSetup key counter bFW nonce)) 16)) := by
      have h16 : 16 ≤ (encSetup key counter bFW nonce).length := by
        rw [encSetup_length key counter bFW nonce hk8 hn3]; omega
      simp [chachaBlockFwd, h16]
    have hListW : chacha20EncryptList key counter nonce msgMid nwords.toNat
        offFW bFW =
        .ok (encXor msgMid offFW
          (addBackList (encSetup key counter bFW nonce)
            (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
          (nwords.toNat - offFW)) := by
      rw [chacha20EncryptList.eq_def key counter nonce msgMid nwords.toNat
        offFW bFW,
        ite_eq_left ⟨hk8, hn3, by omega⟩,
        ite_eq_right (by omega : ¬ offFW + 16 < nwords.toNat + 1)]
      show (if nwords.toNat - offFW = 0 then _ else _) =
        Except.ok (encXor msgMid offFW
          (addBackList (encSetup key counter bFW nonce)
            (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
          (nwords.toNat - offFW))
      rw [ite_eq_right hnt0, hblockFwdW]
    have hEval : evalProgStmt prog F
        (.seq outerWhileFrag
          (.seq (.let_ "ntail" (.u 64) (.usub (.var "nwords") (.var "off")))
            (.seq (.if_ (.une (.var "ntail") (u64lit 0)) tailFrag .skip)
              (.return_ (.var "msg")))))
        (pre ++ mkEncEnv key counter bB nonce msg nwords bN offN iB st) =
        .ok (((("s", .arr32
          (addBackList (encSetup key counter bFW nonce)
            (chachaRounds 10 (encSetup key counter bFW nonce)) 16)) ::
          ("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW)) ++
          mkEncEnv key counter bBW nonce
          (encXor msgMid offFW
            (addBackList (encSetup key counter bFW nonce)
              (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
            (nwords.toNat - offFW))
          nwords bN offFW (BitVec.ofNat 64 (nwords.toNat - offFW))
          (encSetup key counter bFW nonce),
          .returned (.arr32 (encXor msgMid offFW
            (addBackList (encSetup key counter bFW nonce)
              (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
            (nwords.toNat - offFW)))) := by
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hWhile,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hLet,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hIf]
      exact hRet
    have hmsgFin : (encXor msgMid offFW
        (addBackList (encSetup key counter bFW nonce)
          (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
        (nwords.toNat - offFW)).length = nwords.toNat := by
      rw [encXor_length]; exact hmsgW
    refine ⟨((("s", .arr32
      (addBackList (encSetup key counter bFW nonce)
        (chachaRounds 10 (encSetup key counter bFW nonce)) 16)) ::
      ("ntail", .u64 (nwords - BitVec.ofNat 64 offFW)) :: preW)),
      bBW, offFW, (BitVec.ofNat 64 (nwords.toNat - offFW)),
      (encSetup key counter bFW nonce),
      (encXor msgMid offFW
        (addBackList (encSetup key counter bFW nonce)
          (chachaRounds 10 (encSetup key counter bFW nonce)) 16)
        (nwords.toNat - offFW)),
      hpreT, hmsgFin, hEval, ?_⟩
    rw [hListMid]; exact hListW

/-- Whole-function agreement: the emitted entry computes the fuel-free
    list model (default fuel suffices for `nwords ≤ 4096`). -/
theorem evalProgFunc_chacha20Encrypt (F : Nat)
    (key : List (BitVec 32)) (counter : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hmsg : msg.length = nwords.toNat)
    (hbound : nwords.toNat ≤ 4096)
    (hF : (nwords.toNat - 0) / 16 + 16 ≤ F) :
    ∃ msgFin : List (BitVec 32),
      evalProgFunc chacha20EncryptProg F chacha20EncryptFunc
        [.arr32 key, .u32 counter, .arr32 nonce, .arr32 msg, .u64 nwords] =
        .ok (.arr32 msgFin) ∧
      chacha20EncryptList key counter nonce msg nwords.toNat 0 0 =
        .ok msgFin := by
  have hfind : findFunc chacha20EncryptProg "chacha20_block" =
      some chachaBlockFunc := rfl
  have hbind : bindArgs chacha20EncryptFunc.args
      [.arr32 key, .u32 counter, .arr32 nonce, .arr32 msg, .u64 nwords] =
      some [("key", .arr32 key), ("counter", .u32 counter),
        ("nonce", .arr32 nonce), ("msg", .arr32 msg),
        ("nwords", .u64 nwords)] := rfl
  have hbody : chacha20EncryptFunc.body =
      (.seq (.let_ "b" (.u 32) (u32lit 0))
      (.seq (.let_ "off" (.u 64) (u64lit 0))
      (.seq (.let_ "i" (.u 64) (u64lit 0))
      (.seq (.let_ "st" (.array (.u 32) 16)
                (.lit (.arr32 (List.replicate 16 0))))
      (.seq outerWhileFrag
      (.seq (.let_ "ntail" (.u 64)
                (.usub (.var "nwords") (.var "off")))
      (.seq (.if_ (.une (.var "ntail") (u64lit 0)) tailFrag .skip)
            (.return_ (.var "msg"))))))))) := rfl
  have e0b : evalExpr (u32lit 0)
      [("key", .arr32 key), ("counter", .u32 counter),
        ("nonce", .arr32 nonce), ("msg", .arr32 msg),
        ("nwords", .u64 nwords)] =
      .ok (.u32 (BitVec.ofNat 32 0)) := by
    simp only [u32lit, evalExpr_lit, litVal]
  have hletb : evalProgStmt chacha20EncryptProg F
      (.let_ "b" (.u 32) (u32lit 0))
      [("key", .arr32 key), ("counter", .u32 counter),
        ("nonce", .arr32 nonce), ("msg", .arr32 msg),
        ("nwords", .u64 nwords)] =
      .ok (envExtend [("key", .arr32 key), ("counter", .u32 counter),
        ("nonce", .arr32 nonce), ("msg", .arr32 msg),
        ("nwords", .u64 nwords)] "b" (.u32 (BitVec.ofNat 32 0)),
        .fellThrough) :=
    evalProgStmt_let_ok chacha20EncryptProg F "b" (.u 32) _ _ _ e0b
  have e0off : evalExpr (u64lit 0)
      (envExtend [("key", .arr32 key), ("counter", .u32 counter),
        ("nonce", .arr32 nonce), ("msg", .arr32 msg),
        ("nwords", .u64 nwords)] "b" (.u32 (BitVec.ofNat 32 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hletoff : evalProgStmt chacha20EncryptProg F
      (.let_ "off" (.u 64) (u64lit 0))
      (envExtend [("key", .arr32 key), ("counter", .u32 counter),
        ("nonce", .arr32 nonce), ("msg", .arr32 msg),
        ("nwords", .u64 nwords)] "b" (.u32 (BitVec.ofNat 32 0))) =
      .ok (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0)), .fellThrough) :=
    evalProgStmt_let_ok chacha20EncryptProg F "off" (.u 64) _ _ _ e0off
  have e0i : evalExpr (u64lit 0)
      (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp only [u64lit, evalExpr_lit, litVal]
  have hleti : evalProgStmt chacha20EncryptProg F
      (.let_ "i" (.u 64) (u64lit 0))
      (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0))) =
      .ok (envExtend (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0)))
        "i" (.u64 (BitVec.ofNat 64 0)), .fellThrough) :=
    evalProgStmt_let_ok chacha20EncryptProg F "i" (.u 64) _ _ _ e0i
  have e0st : evalExpr (.lit (.arr32 (List.replicate 16 0)))
      (envExtend (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0)))
        "i" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.arr32 (List.replicate 16 0)) := by
    simp only [evalExpr_lit, litVal]
  have hletst : evalProgStmt chacha20EncryptProg F
      (.let_ "st" (.array (.u 32) 16) (.lit (.arr32 (List.replicate 16 0))))
      (envExtend (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0)))
        "i" (.u64 (BitVec.ofNat 64 0))) =
      .ok (envExtend (envExtend (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0)))
        "i" (.u64 (BitVec.ofNat 64 0)))
        "st" (.arr32 (List.replicate 16 0)), .fellThrough) :=
    evalProgStmt_let_ok chacha20EncryptProg F "st" (.array (.u 32) 16)
      _ _ _ e0st
  have hbN : (BitVec.ofNat 32 0).toNat = 0 := ofNat32_toNat 0 (by decide)
  have hst16 : (List.replicate 16 0).length = 16 := List.length_replicate
  have hOuter := outerTail_correct chacha20EncryptProg F key counter
    (BitVec.ofNat 32 0) nonce msg nwords 0 0 (BitVec.ofNat 64 0)
    (List.replicate 16 0) 0 hbN rfl [] (by simp) hk8 hn3 hst16 hfind
    (Nat.zero_le _) (by omega) hmsg (by omega) hF
  obtain ⟨preT, bT, offT, iT, stT, msgFin, hpreT, hlen, hOuterE, hListE⟩ := hOuter
  have hEq : ([] ++ mkEncEnv key counter (BitVec.ofNat 32 0) nonce msg
      nwords 0 0 (BitVec.ofNat 64 0) (List.replicate 16 0)) =
      (envExtend (envExtend (envExtend (envExtend [("key", .arr32 key),
        ("counter", .u32 counter), ("nonce", .arr32 nonce),
        ("msg", .arr32 msg), ("nwords", .u64 nwords)]
        "b" (.u32 (BitVec.ofNat 32 0)))
        "off" (.u64 (BitVec.ofNat 64 0)))
        "i" (.u64 (BitVec.ofNat 64 0)))
        "st" (.arr32 (List.replicate 16 0))) := rfl
  rw [hEq] at hOuterE
  have hstmt : evalProgStmt chacha20EncryptProg F chacha20EncryptFunc.body
      [("key", .arr32 key), ("counter", .u32 counter),
        ("nonce", .arr32 nonce), ("msg", .arr32 msg),
        ("nwords", .u64 nwords)] =
      .ok (preT ++ mkEncEnv key counter bT nonce msgFin nwords 0 offT iT stT,
        .returned (.arr32 msgFin)) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletb,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletoff,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hleti,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletst]
    exact hOuterE
  refine ⟨msgFin, ?_, hListE⟩
  simp only [evalProgFunc, hbind, hstmt]

/-- Fuel-threaded loop model equals the fuel-free list model at
    sufficient fuel (one fuel per full block plus one for the tail). -/
theorem encLoopFwd_eq_list (F : Nat)
    (key : List (BitVec 32)) (counter : BitVec 32) (b : Nat)
    (nonce msg : List (BitVec 32)) (off nwords : Nat)
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hmsg : nwords ≤ msg.length)
    (hF : (nwords - off) / 16 + 1 ≤ F) :
    chacha20EncryptFwd.encLoopFwd key counter b nonce msg off nwords F =
      chacha20EncryptList key counter nonce msg nwords off b := by
  induction F generalizing b off msg with
  | zero => exact False.elim (by omega)
  | succ F ih =>
    have e1 : chacha20EncryptFwd.encLoopFwd key counter b nonce msg off
        nwords (F + 1) =
        (if off + 16 < nwords + 1 then
          match chachaBlockFwd (encSetup key counter b nonce) with
          | .error e => .error e
          | .ok (.arr32 s) =>
            chacha20EncryptFwd.encLoopFwd key counter (b + 1) nonce
              (encXor msg off s 16) (off + 16) nwords F
          | .ok _ => .error .AssertFail
        else
          let ntail := nwords - off
          if ntail = 0 then .ok msg
          else
            match chachaBlockFwd (encSetup key counter b nonce) with
            | .error e => .error e
            | .ok (.arr32 s) => .ok (encXor msg off s ntail)
            | .ok _ => .error .AssertFail) := rfl
    have hC0 : 8 ≤ key.length ∧ 3 ≤ nonce.length ∧ nwords ≤ msg.length :=
      ⟨hk8, hn3, hmsg⟩
    rw [e1, chacha20EncryptList.eq_def key counter nonce msg nwords off b,
      ite_eq_left hC0]
    by_cases hguard : off + 16 < nwords + 1
    · rw [ite_eq_left hguard, ite_eq_left hguard]
      match hblock : chachaBlockFwd (encSetup key counter b nonce) with
      | .error e => rfl
      | .ok w =>
        match w with
        | .arr32 s =>
          have hmsg' : nwords ≤ (encXor msg off s 16).length := by
            rw [encXor_length]; exact hmsg
          exact ih (b := b + 1) (off := off + 16)
            (msg := encXor msg off s 16) (hmsg := hmsg') (hF := by omega)
        | .i32 _ => rfl
        | .u32 _ => rfl
        | .i64 _ => rfl
        | .u64 _ => rfl
        | .b _ => rfl
        | .unit => rfl
        | .vecVal _ => rfl
        | .vecVal64 _ => rfl
        | .boxVal _ => rfl
        | .structVal _ _ => rfl
        | .optVal _ => rfl
        | .spanVal _ => rfl
        | .viewVal _ => rfl
        | .stdVecVal _ => rfl
        | .stdVecOwned _ _ _ => rfl
    · rw [ite_eq_right hguard, ite_eq_right hguard]

/-- Top-level forward equals the list model modulo the `arr32` wrap. -/
theorem chacha20EncryptFwd_eq_list (F : Nat)
    (key : List (BitVec 32)) (counter : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hmsg : nwords.toNat ≤ msg.length)
    (hF : (nwords.toNat - 0) / 16 + 2 ≤ F) :
    chacha20EncryptFwd key counter nonce msg nwords F =
      match chacha20EncryptList key counter nonce msg nwords.toNat 0 0 with
      | .error e => .error e
      | .ok m => .ok (.arr32 m) := by
  cases F with
  | zero => exact False.elim (by omega)
  | succ F =>
    have e0 : chacha20EncryptFwd key counter nonce msg nwords (F + 1) =
        (if 8 ≤ key.length ∧ 3 ≤ nonce.length ∧ nwords.toNat ≤ msg.length then
          match chacha20EncryptFwd.encLoopFwd key counter 0 nonce msg 0
              nwords.toNat F with
          | .error e => .error e
          | .ok m => .ok (.arr32 m)
        else .error .OOB) := rfl
    rw [e0]
    by_cases hC : 8 ≤ key.length ∧ 3 ≤ nonce.length ∧ nwords.toNat ≤ msg.length
    · rw [ite_eq_left hC]
      have hLoop := encLoopFwd_eq_list F key counter 0 nonce msg 0
        nwords.toNat hk8 hn3 hmsg (by omega)
      rw [hLoop]
    · rw [ite_eq_right hC,
        chacha20EncryptList.eq_def key counter nonce msg nwords.toNat 0 0,
        ite_eq_right hC]

/-- `emit_correct` for `chacha20_encrypt` at the default fuel. -/
theorem emit_correct_chacha20Encrypt
    (key : List (BitVec 32)) (counter : BitVec 32)
    (nonce msg : List (BitVec 32)) (nwords : BitVec 64)
    (hk8 : 8 ≤ key.length) (hn3 : 3 ≤ nonce.length)
    (hmsg : msg.length = nwords.toNat)
    (hbound : nwords.toNat ≤ 4096) :
    evalProgFunc chacha20EncryptProg EVAL_FUEL chacha20EncryptFunc
      [.arr32 key, .u32 counter, .arr32 nonce, .arr32 msg, .u64 nwords] =
      match chacha20EncryptList key counter nonce msg nwords.toNat 0 0 with
      | .error e => .error e
      | .ok m => .ok (.arr32 m) := by
  obtain ⟨msgFin, heval, hlist⟩ :=
    evalProgFunc_chacha20Encrypt EVAL_FUEL key counter nonce msg nwords
      hk8 hn3 hmsg hbound (by cir_fuel)
  rw [heval, hlist]

/-- Decidable equality on list-model results (K6b KAT: enables
    `native_decide` on the closed §2.4.2 goal; mirrors the
    `DecidableEq (Result Value)` instance in `Circe.Eval.Core`). -/
instance : DecidableEq (Result (List (BitVec 32))) := fun a b => by
  cases a with
  | ok x =>
    cases b with
    | ok y =>
      match decEq x y with
      | isTrue h => exact isTrue (by rw [h])
      | isFalse h => exact isFalse (fun h' => by cases h'; exact h rfl)
    | error _ => exact isFalse (fun h => by cases h)
  | error e =>
    cases b with
    | ok _ => exact isFalse (fun h => by cases h)
    | error f =>
      match decEq e f with
      | isTrue h => exact isTrue (by rw [h])
      | isFalse h => exact isFalse (fun h' => by cases h'; exact h rfl)

/-- RFC 8439 §2.4.2 key/nonce/counter. -/
def katKey : List (BitVec 32) :=
  [0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
   0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c]

/-- RFC 8439 §2.4.2 nonce. -/
def katNonce : List (BitVec 32) := [0x00000000, 0x4a000000, 0x00000000]

/-- RFC 8439 §2.4.2 counter. -/
def katCounter : BitVec 32 := 1

/-- RFC 8439 §2.4.2 "Sunscreen" plaintext, 28-word prefix (one full
    block plus 12 tail words). -/
def katMsg : List (BitVec 32) :=
  [0x6964614c, 0x61207365, 0x4720646e, 0x6c746e65, 0x6e656d65, 0x20666f20,
   0x20656874, 0x73616c63, 0x666f2073, 0x39392720, 0x6649203a, 0x63204920,
   0x646c756f, 0x66666f20, 0x79207265, 0x6f20756f, 0x20796c6e, 0x20656e6f,
   0x20706974, 0x20726f66, 0x20656874, 0x75747566, 0x202c6572, 0x736e7573,
   0x65657263, 0x6f77206e, 0x20646c75, 0x69206562]

/-- Expected ciphertext for the 28-word prefix (RFC bytes, LE words). -/
def katOut : List (BitVec 32) :=
  [0x9a352e6e, 0x80f96825, 0x2807ba41, 0x81690ddd, 0xec7a7ee9, 0xc260431d,
   0xccaf270a, 0x0bae9ffd, 0xc5651bf9, 0xab334752, 0xab3d598f, 0x57b362cd,
   0x24d63916, 0xab5251e6, 0x350c538f, 0xd861089f, 0xbf0dca07, 0x616a0d50,
   0x088ea356, 0x5eb6228a, 0x4d51bc52, 0x06f8cc16, 0x1ae98c81, 0x363779b7,
   0xbf0bf95a, 0xe65ba374, 0xed8e0bb4, 0x425e78f2]

/-- RFC 8439 §2.4.2 KAT at the list model (one full block plus a
    12-word tail; `native_decide`: closed evaluation, kernel-checked). -/
theorem kat_chacha20_list :
    chacha20EncryptList katKey katCounter katNonce katMsg 28 0 0 =
      .ok katOut := by
  native_decide

/-- RFC 8439 §2.4.2 KAT end to end: the emitted entry computes the
    expected ciphertext. -/
theorem kat_chacha20_eval :
    evalProgFunc chacha20EncryptProg EVAL_FUEL chacha20EncryptFunc
      [.arr32 katKey, .u32 katCounter, .arr32 katNonce, .arr32 katMsg,
        .u64 (BitVec.ofNat 64 28)] =
      .ok (.arr32 katOut) := by
  have h8 : 8 ≤ katKey.length := by decide
  have h3 : 3 ≤ katNonce.length := by decide
  have hlen : katMsg.length = (BitVec.ofNat 64 28).toNat := by decide
  obtain ⟨msgFin, heval, hlist⟩ :=
    evalProgFunc_chacha20Encrypt EVAL_FUEL katKey katCounter katNonce
      katMsg (BitVec.ofNat 64 28) h8 h3 hlen (by decide) (by decide)
  have hkat : chacha20EncryptList katKey katCounter katNonce katMsg
      (BitVec.ofNat 64 28).toNat 0 0 = .ok katOut := by
    rw [ofNat64_toNat 28 (by decide)]
    exact kat_chacha20_list
  rw [hlist] at hkat
  cases hkat
  exact heval
