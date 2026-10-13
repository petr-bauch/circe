-- Differential test for the first writer admission (F1): verified
-- Lean forward (plus `evalFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffReborrow.main [bin trials]`).
-- Every trial asserts evaluation agrees with the sequential
-- checked-add pair (runtime composition check) and, when the pair is
-- `.ok` (both adds in range), the entry agrees with native (the
-- driver calls the real `alias_reborrow` on the input word and prints
-- the post-call word, so tampering the C++ under test is caught).
-- Overflow cases assert Lean-Lean agreement only — signed overflow
-- is UB, so native has nothing to compare (the `nsw` error legs).
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.Reborrow

namespace DiffReborrow

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed words: zero, small increments, `-1`, `INT32_MIN`,
    second-add overflow, first-add overflow. -/
def reborrowEdges : List (BitVec 32) :=
  [0, 1, 10, 0xFFFFFFFF, 0x80000000, 0x7FFFFFFE, 0x7FFFFFFF]

def checkReborrow (reborrowBin : String) (x : BitVec 32) : IO Nat := do
  -- Entry: call-free evaluation agrees with the checked-add pair
  -- (runtime composition check).
  let fwd := reborrowFwd x
  let ev := evalFunc reborrowFunc [.i32 x]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "reborrow eval/fwd mismatch")
  -- Native only when the checked-add pair is `.ok`; otherwise
  -- Lean-Lean agreement only.
  match fwd with
  | .ok (.i32 s) =>
    let native ← runNative reborrowBin #[toString x.toInt]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"reborrow mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"reborrow native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let reborrowBin := args.getD 0 "/tmp/opencode/circe_reborrow_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for x in reborrowEdges do
    let q ← checkReborrow reborrowBin x
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for i in List.range trials do
    s := lcgNext s
    -- Small words stay in range (native agrees); every 8th trial is
    -- full-width (overflows exercise the Lean-Lean path).
    let xi : Int :=
      if i % 8 == 7 then ((s : Int) % 2 ^ 32) - 2 ^ 31
      else (((s % 101 : Nat) : Int) - 50)
    let q ← checkReborrow reborrowBin (BitVec.ofInt 32 xi)
    passed := passed + q
  IO.println s!"DIFFREBORROW-OK passed={passed} (edges + {trials} random trials)"

end DiffReborrow
