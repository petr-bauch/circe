-- Differential test for the K5c SHA-256 compress kernel: verified Lean
-- `sha256_compress` (evaluation + forward) vs the native C binary, plus
-- the corpus pipeline leg (real `.cir` validates under an explicit
-- `noalias` verdict and emits byte-identical text to the golden) and
-- the FIPS 180-4 §8.1.1 "abc" KAT leg.
--
-- Run: `lake env lean --run tests/lean/DiffSha.lean <shabin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with the value
-- forward (runtime composition check); in-range trials additionally
-- agree with native on the 24-word state (longer states compare the
-- 24-word prefix — the tail passes through on both sides). Short
-- states are UB in C, so `OOB` cases assert Lean-Lean agreement only.
-- Mismatch = P0.
import Circe.Emit
import Circe.Validator
import Circe.Crypto.Sha
import Circe.Crypto.ShaBlock

namespace DiffSha

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Compress-kernel pipeline acceptance: real `.cir` validates under the
    explicit `noalias` verdict (attrs are claims, the verdict confirms)
    and emits byte-identical text to the golden (gate VERIFY-OK). -/
def checkShaPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/sha256_compress.cir"
  let want ← IO.FS.readFile "tests/golden/Sha256Compress.lean"
  match runPipeline text ⟨"sha256_compress", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"sha pipeline unexpectedly rejected: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for sha256_compress")
    IO.println s!"PASS pipeline sha256_compress"
    pure 1

/-- FIPS 180-4 §8.1.1 "abc" block input (IV + padded "abc" block). -/
def shaKatIn : List (BitVec 32) :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
   0x61626380, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000018]

/-- Expected compress output (the "abc" digest + the block back,
    cross-checked against `sha256Compress_kat`). -/
def shaKatOut : List (BitVec 32) :=
  [0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
   0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad,
   0x61626380, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000000,
   0x00000000, 0x00000000, 0x00000000, 0x00000018]

def checkSha (shaBin : String) (s : List (BitVec 32)) : IO Nat := do
  let fwd := sha256FuncFwd s
  let ev := evalFunc sha256Func [.arr32 s]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.arr32 r) =>
      -- Native takes exactly the 24-word state; longer Lean states
      -- compare the 24-word prefix (the tail passes through).
      let args := ((s.take 24).map (toString ·.toNat)).toArray
      let native ← runNative shaBin args
      let ws := if native == "" then [] else native.splitOn " "
      let want := r.take 24
      if ws.length != want.length then
        throw (IO.userError s!"sha native arity unparsable: {native}")
      for p in ws.zip want do
        match p.1.toNat? with
        | none => throw (IO.userError s!"sha native unparsable: {native}")
        | some m =>
          if m != p.2.toNat then
            throw (IO.userError s!"sha mismatch: lean={p.2.toNat} native={m}")
      pure 1
    | _ => throw (IO.userError s!"sha eval shape unexpected")
  else
    throw (IO.userError s!"sha eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let shaBin := args.getD 0 "/tmp/opencode/circe_sha_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  let p ← checkShaPipeline
  passed := passed + p
  -- Directed KAT leg: the forward computes the FIPS "abc" vector.
  let kat := sha256FuncFwd shaKatIn
  if (repr kat).pretty != (repr (.ok (.arr32 shaKatOut) : Result Value)).pretty then
    throw (IO.userError s!"sha KAT mismatch (forward disagrees with FIPS 180-4 §8.1.1)")
  IO.println s!"PASS sha KAT (§8.1.1 abc)"
  passed := passed + 1
  let c ← checkSha shaBin shaKatIn
  passed := passed + c
  -- Directed edges: all-zero, short (`OOB`), long (tail through).
  let c0 ← checkSha shaBin (List.replicate 24 0)
  passed := passed + c0
  let cs ← checkSha shaBin (shaKatIn.take 23)
  passed := passed + cs
  let cl ← checkSha shaBin (shaKatIn ++ [0xdeadbeef])
  passed := passed + cl
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    let mut ws : List (BitVec 32) := []
    for _ in List.range 26 do
      s := lcgNext s
      ws := BitVec.ofNat 32 (s % 2 ^ 32) :: ws
    s := lcgNext s
    let victim := s % 4
    let state := if victim == 3 then ws.take 23 else ws.take 24
    let c ← checkSha shaBin state
    passed := passed + c
    s := lcgNext s
  IO.println s!"DIFFSHA-OK passed={passed} (pipeline + KAT + edges + {trials} random trials)"

end DiffSha
