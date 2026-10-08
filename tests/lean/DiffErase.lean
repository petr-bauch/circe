-- Differential test for the N7d `std::vector<int32_t>`
-- single-element `erase` fragment: verified Lean forwards (plus
-- `evalProgFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffErase.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and the closed entry agrees with
-- native (`reserve(10)` + three pushes + `erase(begin() + 1)` +
-- two reads + add = `4`). Native has no entry point for the bare
-- shiftDown/eraseCore leaves, so those fuzz Lean-Lean
-- (proof-covered and runtime cross-checked against the value
-- forwards); the shiftDown additionally pins the ascending walk
-- (position `pos` holds the old `pos + 1` word, and erasing the
-- last element moves zero words). Mismatch = P0.
import Circe.Emit

namespace DiffErase

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Live buffer holding `1 .. len + 1` (the shift reads below `len`;
    the extra word keeps every fuzz buffer well-formed). -/
def mkBuf (len : Nat) : Vec32 :=
  ⟨(List.range (len + 1)).map (fun k => BitVec.ofNat 32 (k + 1)), false⟩

/-- Ascending shift over `[pos + 1, len)` down to `pos`: program
    evaluation agrees with the forward, the length is unchanged, and
    position `pos` holds the old `pos + 1` word (erasing the last
    element moves zero words, so the buffer is unchanged). -/
def checkShiftDown (len cap pos : Nat) : IO Nat := do
  let b := mkBuf len
  let fwd := stdVecShiftDownFwd b len cap
    (BitVec.ofNat 64 (pos + 1)) (BitVec.ofNat 64 len)
    (BitVec.ofNat 64 pos)
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecShiftDownFunc
    [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 (pos + 1)),
     .u64 (BitVec.ofNat 64 len), .u64 (BitVec.ofNat 64 pos)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_shift_down eval/fwd mismatch at ({len}, {cap}, {pos})")
  match ev with
  | .ok (.stdVecOwned b' l _) =>
    match b'.val[pos]?, b.val[pos + 1]?, b.val[pos]? with
    | some moved, some next, some cur =>
      let want := if pos + 1 == len then cur else next
      if l != len || moved != want then
        throw (IO.userError s!"vec_shift_down result miss at ({len}, {cap}, {pos})")
      else pure 1
    | _, _, _ => throw (IO.userError s!"vec_shift_down index miss at ({len}, {cap}, {pos})")
  | _ => throw (IO.userError s!"vec_shift_down eval not ok at ({len}, {cap}, {pos})")

/-- `_M_erase` with `pos < len`: program evaluation agrees with the
    forward, the result has length `len - 1`, and position `pos`
    holds the old `pos + 1` word (erasing the last element keeps the
    buffer and just drops the length). -/
def checkEraseCore (len cap pos : Nat) : IO Nat := do
  let b := mkBuf len
  let fwd := stdVecEraseCoreFwd b len cap (BitVec.ofNat 64 pos)
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecEraseCoreFunc
    [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 pos)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_erase_core eval/fwd mismatch at ({len}, {cap}, {pos})")
  match ev with
  | .ok (.stdVecOwned b' l _) =>
    match b'.val[pos]?, b.val[pos + 1]?, b.val[pos]? with
    | some moved, some next, some cur =>
      let want := if pos + 1 == len then cur else next
      if l != len - 1 || moved != want then
        throw (IO.userError s!"vec_erase_core result miss at ({len}, {cap}, {pos})")
      else pure 1
    | _, _, _ => throw (IO.userError s!"vec_erase_core index miss at ({len}, {cap}, {pos})")
  | _ => throw (IO.userError s!"vec_erase_core eval not ok at ({len}, {cap}, {pos})")

/-- `erase` forwarder: program evaluation agrees with the forward
    (same position matrix as the core). -/
def checkErase (len cap pos : Nat) : IO Nat := do
  let b := mkBuf len
  let fwd := stdVecEraseFwd b len cap (BitVec.ofNat 64 pos)
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecEraseFunc
    [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 pos)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_erase eval/fwd mismatch at ({len}, {cap}, {pos})")
  pure 1

def checkEntry (eraseBin : String) : IO Nat := do
  -- Entry: program evaluation agrees with the value forward
  -- (runtime composition check over the closed script).
  let fwd := vecEraseSumEntryFwd
  let ev := evalProgFunc vecGrowProg EVAL_FUEL vecEraseSumEntryFunc []
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_erase_sum eval/fwd mismatch")
  -- Native agrees (the closed script returns `4`).
  match fwd with
  | .ok (.i32 s) =>
    let native ← runNative eraseBin #[]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"vec_erase_sum mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_erase_sum native unparsable: {native}")
  | _ => throw (IO.userError "vec_erase_sum forward not `.ok (.i32 _)`")

/-- Directed edges: shiftDown boundaries (`pos = 0`, middle,
    `pos = len - 1` single word / zero-move), eraseCore/erase
    position matrix (first + middle + last). -/
def shiftEdges : List (Nat × Nat × Nat) :=
  [(1, 4, 0), (2, 4, 0), (2, 4, 1), (3, 6, 0), (3, 6, 1), (3, 6, 2)]

def coreEdges : List (Nat × Nat × Nat) :=
  [(1, 1, 0), (2, 4, 0), (2, 4, 1), (3, 6, 0), (3, 6, 1), (3, 6, 2)]

def main (args : List String) : IO Unit := do
  let eraseBin := args.getD 0 "/tmp/opencode/circe_vec_erase_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  let e ← checkEntry eraseBin
  passed := passed + e
  for (len, cap, pos) in shiftEdges do
    let q ← checkShiftDown len cap pos
    passed := passed + q
  for (len, cap, pos) in coreEdges do
    let q ← checkEraseCore len cap pos
    passed := passed + q
  for (len, cap, pos) in coreEdges do
    let q ← checkErase len cap pos
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let len := 1 + s % 4
    s := lcgNext s
    let extra := s % 4
    s := lcgNext s
    let pos := s % len
    let cap := len + extra
    let q ← checkShiftDown len cap pos
    passed := passed + q
    let c ← checkEraseCore len cap pos
    passed := passed + c
    let i ← checkErase len cap pos
    passed := passed + i
  IO.println s!"DIFFERASE-OK passed={passed} (entry + {shiftEdges.length} shiftDown + {coreEdges.length} core + {coreEdges.length} erase edges + {trials} random trials × 3)"

end DiffErase
