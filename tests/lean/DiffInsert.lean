-- Differential test for the N7c `std::vector<int32_t>`
-- single-element `insert` fragment: verified Lean forwards (plus
-- `evalProgFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffInsert.main [bin trials]`).
-- Every trial asserts evaluated forms agree with the value forwards
-- (runtime composition check) and the closed entry agrees with
-- native (`reserve(10)` + two pushes + `insert(begin() + 1, 2)` +
-- three reads + add = `6`). Native has no entry point for the bare
-- shift/aux/rval leaves, so those fuzz Lean-Lean (proof-covered and
-- runtime cross-checked against the value forwards); the shift
-- additionally pins the spare-slot fill (the top word moved first,
-- i.e. the descending blit moved `last - first` words). Mismatch = P0.
import Circe.Emit

namespace DiffInsert

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Live buffer holding `1 .. len` with a zeroed spare slot at `len`
    (the shift destination / aux finish slot). -/
def mkShiftBuf (len : Nat) : Vec32 :=
  ⟨(List.range len).map (fun k => BitVec.ofNat 32 (k + 1)) ++
    [BitVec.ofNat 32 0], false⟩

/-- Backward shift over `[pos, len)` into the spare slot: program
    evaluation agrees with the forward, and the spare slot at `len`
    holds the old top word (the descending walk moved every word). -/
def checkShift (len cap pos : Nat) : IO Nat := do
  let b := mkShiftBuf len
  let fwd := stdVecShiftBackFwd b (len + 1) cap
    (BitVec.ofNat 64 pos) (BitVec.ofNat 64 len)
    (BitVec.ofNat 64 (len + 1))
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecShiftBackFunc
    [.stdVecOwned b (len + 1) cap, .u64 (BitVec.ofNat 64 pos),
     .u64 (BitVec.ofNat 64 len), .u64 (BitVec.ofNat 64 (len + 1))]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_shift_back eval/fwd mismatch at ({len}, {cap}, {pos})")
  match ev with
  | .ok (.stdVecOwned b' _ _) =>
    -- `pos = len` moves zero words (spare slot stays zeroed);
    -- otherwise the spare slot holds the old top word.
    match b'.val[len]?, b.val[len - 1]? with
    | some moved, some top =>
      let want := if pos == len then BitVec.ofNat 32 0 else top
      if moved != want then
        throw (IO.userError s!"vec_shift_back spare-slot miss at ({len}, {cap}, {pos})")
      else pure 1
    | _, _ => throw (IO.userError s!"vec_shift_back index miss at ({len}, {cap}, {pos})")
  | _ => throw (IO.userError s!"vec_shift_back eval not ok at ({len}, {cap}, {pos})")

/-- Live buffer holding `1 .. len + 1` (aux reads the last word and
    needs `len + 1 ≤ buflen`). -/
def mkBuf (len : Nat) : Vec32 :=
  ⟨(List.range (len + 1)).map (fun k => BitVec.ofNat 32 (k + 1)), false⟩

/-- `_M_insert_aux` with room (`len < cap`): program evaluation
    agrees with the forward, the result has length `len + 1`, and
    position `pos` holds the inserted word. -/
def checkAux (len cap pos x : Nat) : IO Nat := do
  let b := mkBuf len
  let fwd := stdVecInsertAuxFwd b len cap
    (BitVec.ofNat 64 pos) (BitVec.ofNat 32 x)
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecInsertAuxFunc
    [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 pos),
     .i32 (BitVec.ofNat 32 x)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_insert_aux eval/fwd mismatch at ({len}, {cap}, {pos}, {x})")
  match ev with
  | .ok (.stdVecOwned b' l _) =>
    match b'.val[pos]? with
    | some w =>
      if l != len + 1 || w != BitVec.ofNat 32 x then
        throw (IO.userError s!"vec_insert_aux result miss at ({len}, {cap}, {pos}, {x})")
      else pure 1
    | none => throw (IO.userError s!"vec_insert_aux index miss at ({len}, {cap}, {pos}, {x})")
  | _ => throw (IO.userError s!"vec_insert_aux eval not ok at ({len}, {cap}, {pos}, {x})")

/-- `_M_insert_rval` router: room (`len < cap`, including the
    `pos == len` construct-at-end boundary) and full (`len == cap`,
    reallocation at `pos`) — program evaluation agrees with the
    forward on both arms. -/
def checkRval (len cap pos x : Nat) : IO Nat := do
  let b := mkBuf len
  let fwd := stdVecInsertRvalFwd b len cap
    (BitVec.ofNat 64 pos) (BitVec.ofNat 32 x)
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecInsertRvalFunc
    [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 pos),
     .i32 (BitVec.ofNat 32 x)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_insert_rval eval/fwd mismatch at ({len}, {cap}, {pos}, {x})")
  pure 1

/-- `insert` forwarder: program evaluation agrees with the forward
    (same router matrix as rval). -/
def checkInsert (len cap pos x : Nat) : IO Nat := do
  let b := mkBuf len
  let fwd := stdVecInsertFwd b len cap
    (BitVec.ofNat 64 pos) (BitVec.ofNat 32 x)
  let ev := evalProgFunc vecGrowProg EVAL_FUEL stdVecInsertFunc
    [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 pos),
     .i32 (BitVec.ofNat 32 x)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"vec_insert eval/fwd mismatch at ({len}, {cap}, {pos}, {x})")
  pure 1

def checkEntry (insertBin : String) : IO Nat := do
  -- Entry: program evaluation agrees with the value forward
  -- (runtime composition check over the closed script).
  let fwd := vecInsertSumEntryFwd
  let ev := evalProgFunc vecGrowProg EVAL_FUEL vecInsertSumEntryFunc []
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_insert_sum eval/fwd mismatch")
  -- Native agrees (the closed script returns `6`).
  match fwd with
  | .ok (.i32 s) =>
    let native ← runNative insertBin #[]
    match native.toInt? with
    | some m =>
      if m != s.toInt then
        throw (IO.userError s!"vec_insert_sum mismatch: lean={s.toInt} native={m}")
      pure 1
    | none =>
      throw (IO.userError s!"vec_insert_sum native unparsable: {native}")
  | _ => throw (IO.userError "vec_insert_sum forward not `.ok (.i32 _)`")

/-- Directed edges: shift boundaries (`pos = 0`, `pos = len - 1`,
    single word), aux boundaries (`pos = 0`, middle, `pos = len`),
    rval/insert router matrix (room + end-construct + full). -/
def shiftEdges : List (Nat × Nat × Nat) :=
  [(1, 4, 0), (1, 4, 1), (2, 4, 0), (2, 4, 1), (2, 4, 2), (3, 6, 1)]

def auxEdges : List (Nat × Nat × Nat × Nat) :=
  [(1, 4, 0, 9), (1, 4, 1, 9), (2, 4, 0, 7), (2, 4, 1, 7),
   (2, 4, 2, 7), (3, 6, 1, 5)]

def rvalEdges : List (Nat × Nat × Nat × Nat) :=
  [(1, 4, 0, 9), (1, 4, 1, 9), (2, 4, 2, 7), (2, 2, 0, 7),
   (2, 2, 1, 7), (2, 2, 2, 7), (1, 1, 0, 9), (1, 1, 1, 9)]

def main (args : List String) : IO Unit := do
  let insertBin := args.getD 0 "/tmp/opencode/circe_vec_insert_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  let e ← checkEntry insertBin
  passed := passed + e
  for (len, cap, pos) in shiftEdges do
    let q ← checkShift len cap pos
    passed := passed + q
  for (len, cap, pos, x) in auxEdges do
    let q ← checkAux len cap pos x
    passed := passed + q
  for (len, cap, pos, x) in rvalEdges do
    let q ← checkRval len cap pos x
    passed := passed + q
  for (len, cap, pos, x) in rvalEdges do
    let q ← checkInsert len cap pos x
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let len := 1 + s % 4
    s := lcgNext s
    let extra := s % 4
    s := lcgNext s
    let pos := s % (len + 1)
    s := lcgNext s
    let x := 1 + s % 9
    let cap := len + extra
    let q ← checkShift len cap pos
    passed := passed + q
    let r ← checkAux len (len + 1 + extra) pos x
    passed := passed + r
    let v ← checkRval len cap pos x
    passed := passed + v
    let i ← checkInsert len cap pos x
    passed := passed + i
  IO.println s!"DIFFINSERT-OK passed={passed} (entry + {shiftEdges.length} shift + {auxEdges.length} aux + {rvalEdges.length} rval + {rvalEdges.length} insert edges + {trials} random trials × 4)"

end DiffInsert
