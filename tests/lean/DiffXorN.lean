-- Differential test for the K2 buffer-xor kernel: verified Lean
-- `xor_n` (evaluation + forward) vs the native C binary, plus the
-- corpus pipeline leg (real `.cir` validates under an explicit
-- `noalias` verdict and emits byte-identical text to the golden).
--
-- Run: `lake env lean --run tests/lean/DiffXorN.lean <xornbin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with the value
-- forward (runtime composition check); in-range trials additionally
-- agree with native. Over-long `n` is UB in C, so `OOB` cases assert
-- Lean-Lean agreement only (the writer would run past the buffers).
-- Mismatch = P0.
import Circe.Emit
import Circe.Validator

namespace DiffXorN

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Buffer-kernel pipeline acceptance: real `.cir` validates under the
    explicit `noalias` verdict (attrs are claims, the verdict confirms)
    and emits byte-identical text to the golden (gate VERIFY-OK). -/
def checkXorNPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/xor_n.cir"
  let want ← IO.FS.readFile "tests/golden/XorN.lean"
  match runPipeline text ⟨"xor_n", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"xor_n pipeline unexpectedly rejected: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for xor_n")
    IO.println s!"PASS pipeline xor_n"
    pure 1

/-- Directed cases: `(out-init, a, b, n)`. -/
def xorNEdges : List (List (BitVec 32) × List (BitVec 32) ×
    List (BitVec 32) × BitVec 64) :=
  [([0, 0], [1, 2], [3, 4], 2),
   ([9, 9], [1, 2], [3, 4], 2),
   ([7, 7], [1, 1], [2, 2], 0),
   ([9, 9], [1, 2], [3, 4], 1),
   ([], [], [], 0),
   ([0, 0], [1, 2], [3, 4], 3),
   ([0, 0], [1], [3, 4], 2),
   ([0], [1, 2], [3, 4], 2),
   ([0, 0], [1, 2], [3], 2)]

/-- Huge-`n` spec legs (no fuel needed — the pure forward only):
    past-`u32` and past-`u64`-half lengths are `OOB` on tiny buffers. -/
def xorNHugeNs : List (BitVec 64) :=
  [BitVec.ofNat 64 0x100000000, BitVec.ofNat 64 0x1000000000,
   BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF]

def checkXorNHuge (n : BitVec 64) : IO Nat := do
  let got := xorNFwd [1, 2] [3, 4] [5, 6] n
  if (repr got).pretty == (repr (.error .OOB : Result Value)).pretty then
    pure 1
  else
    throw (IO.userError s!"xor_n huge-n not OOB: n={n.toNat}")

def checkXorN (xorBin : String) (o a b : List (BitVec 32))
    (n : BitVec 64) : IO Nat := do
  let fwd := xorNFwd o a b n
  let ev := evalFunc xorNFunc [.arr32 o, .arr32 a, .arr32 b, .u64 n]
  if (repr fwd).pretty == (repr ev).pretty then
    match fwd with
    | .error _ => pure 1
    | .ok (.arr32 r) =>
      -- Native reads exactly the `n`-prefix (partial-prefix edges
      -- carry longer buffers, like the C caller would).
      let args := #[toString n.toNat] ++
        (((a.take n.toNat).map (toString ·.toNat)) ++
          ((b.take n.toNat).map (toString ·.toNat))).toArray
      let native ← runNative xorBin args
      let ws := if native == "" then [] else native.splitOn " "
      -- Native emits the `n`-prefix; `r` is the full out-buffer.
      let want := r.take n.toNat
      if ws.length != want.length then
        throw (IO.userError s!"xor_n native arity unparsable: {native}")
      for p in ws.zip want do
        match p.1.toNat? with
        | none => throw (IO.userError s!"xor_n native unparsable: {native}")
        | some m =>
          if m != p.2.toNat then
            throw (IO.userError s!"xor_n mismatch: lean={p.2.toNat} native={m}")
      pure 1
    | _ => throw (IO.userError s!"xor_n eval shape unexpected")
  else
    throw (IO.userError s!"xor_n eval/fwd mismatch (emit_correct violated at runtime)")

def main (args : List String) : IO Unit := do
  let xorBin := args.getD 0 "/tmp/opencode/circe_xor_n_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  let p ← checkXorNPipeline
  passed := passed + p
  for e in xorNEdges do
    let c ← checkXorN xorBin e.1 e.2.1 e.2.2.1 e.2.2.2
    passed := passed + c
  for n in xorNHugeNs do
    let c ← checkXorNHuge n
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for t in List.range trials do
    s := lcgNext s
    -- Small lengths stay in fuel; every fourth trial shortens one
    -- buffer (Lean-Lean `OOB` path), the rest compare vs native.
    let n := BitVec.ofNat 64 ([0, 1, 2, 3, 5, 8].getD (s % 6) 0)
    let half : Bool := t % 2 == 0
    let mut ws : List (BitVec 32) := []
    for _ in List.range (3 * n.toNat) do
      s := lcgNext s
      ws := BitVec.ofNat 32 (s % 2 ^ 32) :: ws
    let a := ws.take n.toNat
    let b := (ws.drop n.toNat).take n.toNat
    let o := List.replicate n.toNat (if half then BitVec.ofNat 32 0 else BitVec.ofNat 32 0xDEAD)
    s := lcgNext s
    let victim := s % 4
    if victim == 3 || n.toNat == 0 then
      let c ← checkXorN xorBin o a b n
      passed := passed + c
    else
      -- Shorten one buffer below `n`: the first short op errors.
      let short : List (BitVec 32) :=
        List.replicate (n.toNat - 1) (BitVec.ofNat 32 0)
      let c ← if victim == 0 then checkXorN xorBin short a b n
        else if victim == 1 then checkXorN xorBin o short b n
        else checkXorN xorBin o a short n
      passed := passed + c
    s := lcgNext s
  IO.println s!"DIFFXORN-OK passed={passed} (edges + huge-n + {trials} random trials)"

end DiffXorN
