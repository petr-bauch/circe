-- Differential test for the two-reader admission (`sum_two`): verified
-- Lean `sumTwoFunc` (evaluation + forward) vs the native C binary, plus
-- the corpus pipeline leg (real `.cir` validates under an explicit
-- `noalias` verdict and emits byte-identical text to the golden).
--
-- Run: `lake env lean --run tests/lean/DiffSumTwo.lean <sumbin> [trials]`
-- Every trial asserts evaluated `evalFunc` agrees with the value
-- forward (runtime composition check); in-range trials additionally
-- agree with native. Over-long `n` (past either array) is UB in C, so
-- `OOB` cases assert Lean-Lean agreement only. Aliased readers
-- (`a == b`, same words twice) run through both legs: reads never
-- write, so aliasing is value-sound (N2a). Mismatch = P0.
import Circe.Emit
import Circe.Validator

namespace DiffSumTwo

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- U32 draw. -/
def drawU32 (s : Nat) : BitVec 32 × Nat :=
  (BitVec.ofNat 32 (s % 2 ^ 32), lcgNext s)

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Two-reader pipeline acceptance: real `.cir` validates under the
    explicit `noalias` verdict (attrs are claims, the verdict confirms)
    and emits byte-identical text to the golden (gate VERIFY-OK). -/
def checkSumTwoPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/sum_two.cir"
  let want ← IO.FS.readFile "tests/golden/SumTwo.lean"
  match runPipeline text ⟨"sum_two", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"sum_two pipeline unexpectedly rejected: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for sum_two")
    IO.println s!"PASS pipeline sum_two"
    pure 1

/-- Directed cases: `(a-words, b-words, n)`. -/
def sumTwoEdges : List (List Nat × List Nat × Nat) :=
  [([1, 2, 3], [4, 5, 6], 3),
   ([1, 2], [1, 2], 2),
   ([], [], 0),
   ([7], [8], 0),
   ([0xFFFFFFFF], [1], 1),
   ([1], [1, 2], 2),
   ([1, 2], [1], 2),
   ([1, 2], [3, 4], 5),
   ([9, 9, 9], [9, 9, 9], 3)]

/-- One trial: eval-vs-forward always; native agreement in-range,
    `OOB`-must-hold past either array. -/
def checkSumTwo (bin : String) (l₁ l₂ : List (BitVec 32))
    (n : BitVec 32) : IO Nat := do
  let got := evalFunc sumTwoFunc [.arr32 l₁, .arr32 l₂, .u32 n]
  if n.toNat ≤ l₁.length ∧ n.toNat ≤ l₂.length then
    match got, sumTwoFwd l₁ l₂ n with
    | .ok (.u32 r), .ok (.u32 w) =>
      if r != w then
        throw (IO.userError s!"sum_two eval/fwd mismatch (emit_correct violated at runtime)")
      -- The driver reads `b` immediately after `n` words of `a`, so
      -- send exactly the `n`-prefix of each (over-long tails stay on
      -- the Lean-Lean leg only).
      let a' := l₁.take n.toNat
      let b' := l₂.take n.toNat
      let native ← runNative bin
        (#[toString n.toNat] ++
          ((a'.map fun x => toString x.toNat).toArray) ++
          ((b'.map fun x => toString x.toNat).toArray))
      match native.toNat? with
      | none => throw (IO.userError s!"sum_two native unparsable: {native}")
      | some m =>
        if m != w.toNat then
          throw (IO.userError s!"sum_two mismatch: n={n.toNat} lean={w.toNat} native={m}")
        pure 1
    | .ok _, _ =>
      throw (IO.userError s!"sum_two eval shape unexpected")
    | .error e, _ =>
      throw (IO.userError s!"sum_two wrongly strict on in-range input: {(repr e).pretty}")
  else
    match got, sumTwoFwd l₁ l₂ n with
    | .error .OOB, .error .OOB => pure 1
    | .ok v, _ =>
      throw (IO.userError s!"sum_two wrongly lenient: n={n.toNat} lens=({l₁.length},{l₂.length}) gave {(repr v).pretty}")
    | _, .ok v =>
      throw (IO.userError s!"sum_two forward wrongly lenient: gave {(repr v).pretty}")
    | .error e, _ =>
      throw (IO.userError s!"sum_two wrong error kind: {(repr e).pretty}")

def main (args : List String) : IO Unit := do
  let sumBin := args.getD 0 "/tmp/opencode/circe_sum_two_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  let c ← checkSumTwoPipeline
  passed := passed + c
  for (xs, ys, k) in sumTwoEdges do
    let l₁ := xs.map (BitVec.ofNat 32)
    let l₂ := ys.map (BitVec.ofNat 32)
    let c ← checkSumTwo sumBin l₁ l₂ (BitVec.ofNat 32 k)
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    let k₁ := s % 9
    let k₂ := lcgNext s % 9
    let nn := lcgNext (lcgNext s) % 11
    let mut l₁ : List (BitVec 32) := []
    let mut l₂ : List (BitVec 32) := []
    let mut t := lcgNext (lcgNext (lcgNext s))
    for _ in List.range k₁ do
      let (w, t') := drawU32 t
      t := t'
      l₁ := l₁ ++ [w]
    for _ in List.range k₂ do
      let (w, t') := drawU32 t
      t := t'
      l₂ := l₂ ++ [w]
    s := t
    let c ← checkSumTwo sumBin l₁ l₂ (BitVec.ofNat 32 nn)
    passed := passed + c
  -- Aliased readers through the native leg: identical words twice.
  let c ← checkSumTwo sumBin [9, 9, 9] [9, 9, 9] 3
  passed := passed + c
  IO.println s!"DIFFSUMTWO-OK passed={passed} (pipeline + edges + {trials} random trials + alias leg)"

end DiffSumTwo
