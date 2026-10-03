-- Differential test for N2c: verified Lean `sumFwd` (the identical body
-- the recovered `sum_norestrict` shares with `sum_array`) vs the native
-- no-`restrict` binary. Recovery changes only the gate, never the
-- semantics — so this fuzzer asserts the same equation on the same edges:
-- wrapping sums on in-range lengths, `OOB` off-range (native not
-- consulted there: OOB read is UB in C).
--
-- Run: `lake env lean --run tests/lean/DiffNorestrict.lean <norestrict_bin> [trials]`
import Circe.Emit

/-- 64-bit LCG step. -/
def lcgNextNr (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Draw a `BitVec 32` uniformly from the stream. -/
def drawU32Nr (s : Nat) : BitVec 32 × Nat :=
  let s' := lcgNextNr s
  (BitVec.ofNat 32 (s' % 2 ^ 32), s')

/-- Run a native binary with args, returning trimmed stdout. -/
def runNativeNr (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Fixed edge cases (list, length): in-range sums plus OOB lengths. -/
def norestrictEdges : List (List Nat × Nat) :=
  [([], 0), ([0], 1), ([1, 2, 3], 3), ([5], 0),
   ([4294967295, 4294967295], 2), ([1, 2], 5), ([], 1), ([7, 8, 9], 2)]

def checkNorestrict (nrBin : String) (l : List (BitVec 32)) (n : BitVec 32) :
    IO Nat := do
  if n.toNat ≤ l.length then
    match sumFwd l n, evalFunc sumFunc [.arr32 l, .u32 n] with
    | .ok (.u32 r), .ok (.u32 r2) =>
      if r != r2 then
        throw (IO.userError s!"norestrict eval/fwd mismatch (emit_correct violated at runtime)")
      let native ← runNativeNr nrBin
        (#[toString n.toNat] ++ ((l.map fun x => toString x.toNat).toArray))
      match native.toNat? with
      | none => throw (IO.userError s!"norestrict native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"norestrict mismatch: n={n.toNat} lean={r.toNat} native={m}")
        pure 1
    | .ok _, _ =>
      throw (IO.userError s!"norestrict eval shape unexpected")
    | .error e, _ =>
      throw (IO.userError s!"norestrict wrongly strict on in-range input: {(repr e).pretty}")
  else
    match sumFwd l n with
    | .error .OOB => pure 1
    | .ok v =>
      throw (IO.userError s!"norestrict wrongly lenient: n={n.toNat} len={l.length} gave {(repr v).pretty}")
    | .error e =>
      throw (IO.userError s!"norestrict wrong error kind: {(repr e).pretty}")

def main (args : List String) : IO Unit := do
  let nrBin := args.getD 0 "/tmp/opencode/circe_sum_norestrict_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (xs, k) in norestrictEdges do
    let l := xs.map (BitVec.ofNat 32)
    let c ← checkNorestrict nrBin l (BitVec.ofNat 32 k)
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    let k := s % 9
    let nn := lcgNextNr s % 10
    let mut l : List (BitVec 32) := []
    let mut t := s
    for _ in List.range k do
      let (w, t') := drawU32Nr t
      t := t'
      l := l ++ [w]
    s := t
    let c ← checkNorestrict nrBin l (BitVec.ofNat 32 nn)
    passed := passed + c
  IO.println s!"DIFFNORESTRICT-OK passed={passed} (edges + {trials} random trials)"
