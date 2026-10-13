-- Differential test for the branch-writer admission (G2b): verified
-- Lean forward (plus `evalFunc` composition) vs the native C binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffCondPair.main [bin trials]`).
-- Every trial asserts evaluation agrees with the independent
-- branch-then-add pair (runtime composition check) and, when both
-- evaluated adds are in range, the entry agrees with native (the
-- driver calls the real `cond_pair` on two disjoint cells and
-- prints the updated pair, so tampering the C under test is
-- caught). Overflow cases assert Lean-Lean agreement only — signed
-- overflow is UB, so native has nothing to compare (the `nsw`
-- error legs, plus the `c = false` masking leg where native never
-- computes the first add). Aliased callers are caller-UB under
-- the `noalias` verdict: documented, never fuzzed. Mismatch = P0.
import Circe.Emit
import Circe.Emit.CondPair

namespace DiffCondPair

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Directed triples: both legs, `-1` on either side, `INT32_MIN`,
    first-add overflow taken and masked, second-add overflow on
    both legs. -/
def condPairEdges : List (BitVec 32 × BitVec 32 × Bool) :=
  [(0, 0, true), (10, 20, true), (10, 20, false),
   (0xFFFFFFFF, 0, true), (0, 0xFFFFFFFF, false),
   (0x80000000, 0x80000000, true), (0x7FFFFFFF, 0, true),
   (0x7FFFFFFF, 0, false), (0, 0x7FFFFFFF, true),
   (0, 0x7FFFFFFF, false)]

def checkCondPair (condPairBin : String) (p q : BitVec 32)
    (c : Bool) : IO Nat := do
  -- Entry: call-free evaluation agrees with the branch-then-add pair
  -- (runtime composition check).
  let fwd := condPairFwd p q c
  let ev := evalFunc condPairFunc [.i32 p, .i32 q, .b c]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "cond_pair eval/fwd mismatch")
  -- Native only when the evaluated adds are `.ok`; otherwise
  -- Lean-Lean agreement only.
  match fwd with
  | .ok (.structVal "IPair" [("a", a), ("b", b)]) =>
    let native ← runNative condPairBin
      #[toString p.toInt, toString q.toInt, if c then "1" else "0"]
    match native.splitOn " " with
    | [sp, sq] =>
      match sp.toInt?, sq.toInt? with
      | some m, some n =>
        if m != a.toInt || n != b.toInt then
          throw (IO.userError s!"cond_pair mismatch: lean=({a.toInt}, {b.toInt}) native=({m}, {n})")
        pure 1
      | _, _ =>
        throw (IO.userError s!"cond_pair native unparsable: {native}")
    | _ =>
      throw (IO.userError s!"cond_pair native unparsable: {native}")
  | _ => pure 1

def main (args : List String) : IO Unit := do
  let condPairBin := args.getD 0 "/tmp/opencode/circe_cond_pair_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (p, q, c) in condPairEdges do
    let r ← checkCondPair condPairBin p q c
    passed := passed + r
  let mut s := 0x9E3779B97F4A7C15
  for i in List.range trials do
    s := lcgNext s
    -- Small words stay in range (native agrees); every 8th trial is
    -- full-width (overflows exercise the Lean-Lean path); `c`
    -- alternates (masking legs included).
    let xi : Int :=
      if i % 8 == 7 then ((s : Int) % 2 ^ 32) - 2 ^ 31
      else (((s % 101 : Nat) : Int) - 50)
    s := lcgNext s
    let yi : Int :=
      if i % 8 == 3 then ((s : Int) % 2 ^ 32) - 2 ^ 31
      else (((s % 101 : Nat) : Int) - 50)
    let c := i % 2 == 0
    let r ← checkCondPair condPairBin (BitVec.ofInt 32 xi)
      (BitVec.ofInt 32 yi) c
    passed := passed + r
  IO.println s!"DIFFCONDPAIR-OK passed={passed} (edges + {trials} random trials)"

end DiffCondPair
