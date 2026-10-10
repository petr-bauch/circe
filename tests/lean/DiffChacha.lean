-- Differential test for the K4 ChaCha20 block kernel: verified Lean
-- `chacha20_block` (evaluation + forward) vs the native C binary, plus
-- the corpus pipeline leg (real `.cir` validates under an explicit
-- `noalias` verdict and emits byte-identical text to the golden) and
-- the RFC 8439 §2.3.2 KAT leg.
--
-- Run: `lake env lean --run tests/lean/DiffChacha.lean <chachabin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with the value
-- forward (runtime composition check); in-range trials additionally
-- agree with native on the 16-word state (longer states compare the
-- 16-word prefix — the tail passes through on both sides). Short
-- states are UB in C, so `OOB` cases assert Lean-Lean agreement only.
-- Mismatch = P0.
import Circe.Emit
import Circe.Validator
import Circe.Crypto.Block

namespace DiffChacha

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Block-kernel pipeline acceptance: real `.cir` validates under the
    explicit `noalias` verdict (attrs are claims, the verdict confirms)
    and emits byte-identical text to the golden (gate VERIFY-OK). -/
def checkChachaPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/chacha_block.cir"
  let want ← IO.FS.readFile "tests/golden/ChachaBlock.lean"
  match runPipeline text ⟨"chacha20_block", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"chacha pipeline unexpectedly rejected: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for chacha20_block")
    IO.println s!"PASS pipeline chacha20_block"
    pure 1

/-- RFC 8439 §2.3.2 block input. -/
def chachaKatIn : List (BitVec 32) :=
  [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
   0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
   0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c,
   0x00000001, 0x09000000, 0x4a000000, 0x00000000]

/-- Expected block output (keystream words, cross-checked against the
    RFC keystream bytes `10 f1 e7 e4 ...`). -/
def chachaKatOut : List (BitVec 32) :=
  [0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3,
   0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3,
   0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9,
   0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2]

def checkChacha (chachaBin : String) (s : List (BitVec 32)) : IO Nat := do
  let fwd := chachaBlockFwd s
  let ev := evalFunc chachaBlockFunc [.arr32 s]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.arr32 r) =>
      -- Native takes exactly the 16-word state; longer Lean states
      -- compare the 16-word prefix (the tail passes through).
      let args := ((s.take 16).map (toString ·.toNat)).toArray
      let native ← runNative chachaBin args
      let ws := if native == "" then [] else native.splitOn " "
      let want := r.take 16
      if ws.length != want.length then
        throw (IO.userError s!"chacha native arity unparsable: {native}")
      for p in ws.zip want do
        match p.1.toNat? with
        | none => throw (IO.userError s!"chacha native unparsable: {native}")
        | some m =>
          if m != p.2.toNat then
            throw (IO.userError s!"chacha mismatch: lean={p.2.toNat} native={m}")
      pure 1
    | _ => throw (IO.userError s!"chacha eval shape unexpected")
  else
    throw (IO.userError s!"chacha eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let chachaBin := args.getD 0 "/tmp/opencode/circe_chacha_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  let p ← checkChachaPipeline
  passed := passed + p
  -- Directed KAT leg: the forward computes the RFC §2.3.2 vector.
  let kat := chachaBlockFwd chachaKatIn
  if (repr kat).pretty != (repr (.ok (.arr32 chachaKatOut) : Result Value)).pretty then
    throw (IO.userError s!"chacha KAT mismatch (forward disagrees with RFC 8439 §2.3.2)")
  IO.println s!"PASS chacha KAT (§2.3.2)"
  passed := passed + 1
  let c ← checkChacha chachaBin chachaKatIn
  passed := passed + c
  -- Directed edges: all-zero, short (`OOB`), long (tail through).
  let c0 ← checkChacha chachaBin (List.replicate 16 0)
  passed := passed + c0
  let cs ← checkChacha chachaBin (chachaKatIn.take 15)
  passed := passed + cs
  let cl ← checkChacha chachaBin (chachaKatIn ++ [0xdeadbeef])
  passed := passed + cl
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    let mut ws : List (BitVec 32) := []
    for _ in List.range 18 do
      s := lcgNext s
      ws := BitVec.ofNat 32 (s % 2 ^ 32) :: ws
    s := lcgNext s
    let victim := s % 4
    let state := if victim == 3 then ws.take 15 else ws.take 16
    let c ← checkChacha chachaBin state
    passed := passed + c
    s := lcgNext s
  IO.println s!"DIFFCHACHA-OK passed={passed} (pipeline + KAT + edges + {trials} random trials)"

end DiffChacha
