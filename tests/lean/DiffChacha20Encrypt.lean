-- Differential test for the K6 ChaCha20 stream cipher: verified Lean
-- `chacha20_encrypt` (evaluation + forward) vs the native C binary, plus
-- the corpus pipeline leg (real `.cir` validates under an explicit
-- `noalias` verdict and emits byte-identical text to the golden) and
-- the RFC 8439 §2.4.2 KAT leg (28-word prefix: one full + one 12-word
-- tail block).
--
-- Run: `lake env lean --run tests/lean/DiffChacha20Encrypt.lean <encryptbin> [trials]`
-- Every trial asserts evaluated `evalProgFunc` agrees with the value
-- forward (runtime composition check); in-range trials additionally
-- agree with native on the message words. Short key/nonce/message and
-- over-long `nwords` are `OOB` in Lean (UB in C), so those cases assert
-- Lean-Lean agreement only.
-- Mismatch = P0.
import Circe.Emit
import Circe.Validator
import Circe.Crypto.Stream

namespace DiffChacha20Encrypt

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := bin, args := args }
  if out.exitCode != 0 then
    throw (IO.userError s!"chacha20_encrypt native failed: {out.stderr}")
  pure out.stdout.trimAscii.toString

/-- Stream pipeline acceptance: real `.cir` validates under the
    explicit `noalias` verdict and emits byte-identical text to the
    golden (gate VERIFY-OK). -/
def checkEncryptPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/chacha20_encrypt.cir"
  let want ← IO.FS.readFile "tests/golden/Chacha20Encrypt.lean"
  match runPipeline text ⟨"chacha20_encrypt", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"encrypt pipeline unexpectedly rejected: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for chacha20_encrypt")
    IO.println s!"PASS pipeline chacha20_encrypt"
    pure 1

/-- RFC 8439 §2.4.2 key/nonce/counter. -/
def katKey : List (BitVec 32) :=
  [0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
   0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c]

def katNonce : List (BitVec 32) := [0x00000000, 0x4a000000, 0x00000000]

def katCounter : BitVec 32 := 1

/-- RFC 8439 §2.4.2 "Sunscreen" plaintext, 28-word prefix (112 of the
    114 bytes: one full block + 12 tail words). -/
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

def checkEncrypt (encBin : String) (key : List (BitVec 32))
    (counter : BitVec 32) (nonce msg : List (BitVec 32))
    (nwords : Nat) : IO Nat := do
  let F := 64 * (nwords + 2) + 64
  let fwd := chacha20EncryptFwd key counter nonce msg
    (BitVec.ofNat 64 nwords) F
  let ev := evalProgFunc chacha20EncryptProg F chacha20EncryptFunc
    [.arr32 key, .u32 counter, .arr32 nonce, .arr32 msg,
     .u64 (BitVec.ofNat 64 nwords)]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.arr32 r) =>
      let args := ((key.map toString).toArray
        ++ #[toString counter.toNat]
        ++ (nonce.map toString).toArray
        ++ #[toString nwords]
        ++ (msg.map toString).toArray)
      let native ← runNative encBin args
      let ws := if native == "" then [] else native.splitOn " "
      let want := r.map (fun w => toString w.toNat)
      if ws.length != want.length then
        throw (IO.userError s!"encrypt native arity unparsable: {native}")
      for p in ws.zip want do
        if p.1 != p.2 then
          throw (IO.userError s!"encrypt mismatch: lean={p.2} native={p.1}")
      pure 1
    | _ => throw (IO.userError s!"encrypt eval shape unexpected")
  else
    throw (IO.userError s!"encrypt eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let encBin := args.getD 0 "/tmp/opencode/circe_chacha20_encrypt_native"
  let trials := (args.getD 1 "200").toNat?.getD 200
  let mut passed := 0
  let p ← checkEncryptPipeline
  passed := passed + p
  -- Directed KAT leg: the forward computes the RFC §2.4.2 prefix vector.
  let kat := chacha20EncryptFwd katKey katCounter katNonce katMsg
    (BitVec.ofNat 64 28) 4096
  if (repr kat).pretty != (repr (.ok (.arr32 katOut) : Result Value)).pretty then
    throw (IO.userError s!"encrypt KAT mismatch (forward disagrees with RFC 8439 §2.4.2)")
  IO.println s!"PASS encrypt KAT (§2.4.2 28-word prefix)"
  passed := passed + 1
  let c ← checkEncrypt encBin katKey katCounter katNonce katMsg 28
  passed := passed + c
  -- Directed edges: empty (no-op), single word (pure tail), exactly one
  -- block (no tail), short key/nonce/message and over-long nwords (OOB).
  let c0 ← checkEncrypt encBin katKey katCounter katNonce [] 0
  passed := passed + c0
  let c1 ← checkEncrypt encBin katKey katCounter katNonce [0x6964614c] 1
  passed := passed + c1
  let c16 ← checkEncrypt encBin katKey katCounter katNonce
    (katMsg.take 16) 16
  passed := passed + c16
  let cs1 ← checkEncrypt encBin (katKey.take 7) katCounter katNonce katMsg 28
  passed := passed + cs1
  let cs2 ← checkEncrypt encBin katKey katCounter (katNonce.take 2) katMsg 28
  passed := passed + cs2
  let cs3 ← checkEncrypt encBin katKey katCounter katNonce (katMsg.take 27) 28
  passed := passed + cs3
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let nw := s % 41
    let mut ws : List (BitVec 32) := []
    for _ in List.range nw do
      s := lcgNext s
      ws := ws ++ [BitVec.ofNat 32 (s % 2 ^ 32)]
    s := lcgNext s
    let ctr := BitVec.ofNat 32 (s % 2 ^ 32)
    let c ← checkEncrypt encBin katKey ctr katNonce ws nw
    passed := passed + c
  IO.println s!"DIFFCHACHA20ENCRYPT-OK passed={passed} (edges + {trials} random trials)"

end DiffChacha20Encrypt
