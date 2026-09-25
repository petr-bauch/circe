-- Differential test for the Phase 4 additions: verified Lean `choose`
-- (forward + backward) and `sum` vs native C binaries.
--
-- Run: `lake env lean --run tests/lean/DiffPhase4.lean <choose_bin> <sum_bin> [trials]`
-- `choose` selection never fails (all inputs compared against native);
-- write-back through the returned pointer is compared against `chooseBack`
-- (lens behavior vs native, no UB: plain stores). `sum` compares wrapping
-- sums on in-range lengths (unsigned: no UB); over-long lengths assert Lean
-- `OOB` (native not consulted: OOB read is UB in C). Every in-range `sum`
-- trial additionally asserts evaluated `evalFunc` agrees with `sumFwd`
-- (runtime loop check).
import Circe.Emit

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Draw an `Int` in `[int32Min, int32Max]` from the stream. -/
def drawI32 (s : Nat) : Int × Nat :=
  let s' := lcgNext s
  (Int.ofNat (s' % 2 ^ 32) + int32Min, s')

/-- Draw a `BitVec 32` uniformly from the stream. -/
def drawU32 (s : Nat) : BitVec 32 × Nat :=
  let s' := lcgNext s
  (BitVec.ofNat 32 (s' % 2 ^ 32), s')

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- Split stdout on spaces/newlines. -/
def splitWords (s : String) : List String :=
  let (_, acc) :=
    (s.toList ++ [' ']).foldl (fun (cur, acc) c =>
      if c == ' ' || c == '\n' || c == '\t' then ([], acc ++ [cur])
      else (cur ++ [c], acc)) ([], [])
  acc.map String.ofList |>.filter (fun t => t != "")

/-- Fixed edge cases for `choose` (b, x, y). -/
def chooseEdges : List (Bool × Int × Int) :=
  [(true, 0, 0), (false, 0, 0), (true, 1, 2), (false, 1, 2),
   (true, 2147483647, -2147483648), (false, 2147483647, -2147483648),
   (true, -5, -5), (false, 42, -42)]

def checkChooseFwd (chooseBin : String) (b : Bool) (x y : BitVec 32) :
    IO Nat := do
  match chooseFwd b x y with
  | .ok (.i32 r) =>
    let bs := if b then "1" else "0"
    let native ← runNative chooseBin
      #["sel", bs, toString x.toInt, toString y.toInt]
    match native.toInt? with
    | none => throw (IO.userError s!"choose native unparsable: {native}")
    | some n =>
      if n != r.toInt then
        throw (IO.userError s!"choose mismatch: b={bs} x={x.toInt} y={y.toInt} lean={r.toInt} native={n}")
      pure 1
  | .ok v =>
    throw (IO.userError s!"choose unexpected value shape: {(repr v).pretty}")
  | .error e =>
    throw (IO.userError s!"choose unexpected error: {(repr e).pretty}")

def checkChooseBack (chooseBin : String) (b : Bool) (x y r : BitVec 32) :
    IO Nat := do
  match chooseBack b x y r with
  | .ok (.i32 x', .i32 y') =>
    let bs := if b then "1" else "0"
    let native ← runNative chooseBin
      #["wb", bs, toString x.toInt, toString y.toInt, toString r.toInt]
    match splitWords native with
    | [sx, sy] =>
      match sx.toInt?, sy.toInt? with
      | some nx, some ny =>
        if nx != x'.toInt || ny != y'.toInt then
          throw (IO.userError s!"choose back mismatch: b={bs} x={x.toInt} y={y.toInt} r={r.toInt} lean=({x'.toInt},{y'.toInt}) native=({nx},{ny})")
        pure 1
      | _, _ => throw (IO.userError s!"choose back unparsable: {native}")
    | _ => throw (IO.userError s!"choose back bad shape: {native}")
  | .ok v =>
    throw (IO.userError s!"choose back unexpected shape: {(repr v).pretty}")
  | .error e =>
    throw (IO.userError s!"choose back unexpected error: {(repr e).pretty}")

/-- Fixed edge cases for `sum` (list, length). -/
def sumEdges : List (List Nat × Nat) :=
  [([], 0), ([0], 1), ([1, 2, 3], 3), ([5], 0),
   ([4294967295, 4294967295], 2), ([1, 2], 5), ([], 1), ([7, 8, 9], 2)]

def checkSum (sumBin : String) (l : List (BitVec 32)) (n : BitVec 32) :
    IO Nat := do
  if n.toNat ≤ l.length then
    match sumFwd l n, evalFunc sumFunc [.arr32 l, .u32 n] with
    | .ok (.u32 r), .ok (.u32 r2) =>
      if r != r2 then
        throw (IO.userError s!"sum eval/fwd mismatch (emit_correct violated at runtime)")
      let native ← runNative sumBin
        (#[toString n.toNat] ++ ((l.map fun x => toString x.toNat).toArray))
      match native.toNat? with
      | none => throw (IO.userError s!"sum native unparsable: {native}")
      | some m =>
        if m != r.toNat then
          throw (IO.userError s!"sum mismatch: n={n.toNat} lean={r.toNat} native={m}")
        pure 1
    | .ok _, _ =>
      throw (IO.userError s!"sum eval shape unexpected")
    | .error e, _ =>
      throw (IO.userError s!"sum wrongly strict on in-range input: {(repr e).pretty}")
  else
    match sumFwd l n with
    | .error .OOB => pure 1
    | .ok v =>
      throw (IO.userError s!"sum wrongly lenient: n={n.toNat} len={l.length} gave {(repr v).pretty}")
    | .error e =>
      throw (IO.userError s!"sum wrong error kind: {(repr e).pretty}")

def main (args : List String) : IO Unit := do
  let chooseBin := args.getD 0 "/tmp/opencode/circe_choose_native"
  let sumBin := args.getD 1 "/tmp/opencode/circe_sum_native"
  let trials := (args.getD 2 "1000").toNat?.getD 1000
  let mut passed := 0
  for (b, x, y) in chooseEdges do
    let xb := BitVec.ofInt 32 x
    let yb := BitVec.ofInt 32 y
    let c1 ← checkChooseFwd chooseBin b xb yb
    passed := passed + c1
    let c2 ← checkChooseBack chooseBin b xb yb xb
    passed := passed + c2
  for (xs, k) in sumEdges do
    let l := xs.map (BitVec.ofNat 32)
    let c ← checkSum sumBin l (BitVec.ofNat 32 k)
    passed := passed + c
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    let (x, s1) := drawI32 s
    let (y, s2) := drawI32 s1
    let (v, s3) := drawI32 s2
    let b := (s3 % 2 == 0)
    let xb := BitVec.ofInt 32 x
    let yb := BitVec.ofInt 32 y
    let vb := BitVec.ofInt 32 v
    let c1 ← checkChooseFwd chooseBin b xb yb
    passed := passed + c1
    let c2 ← checkChooseBack chooseBin b xb yb vb
    passed := passed + c2
    let k := s3 % 9
    let nn := lcgNext s3 % 10
    let mut l : List (BitVec 32) := []
    let mut t := s3
    for _ in List.range k do
      let (w, t') := drawU32 t
      t := t'
      l := l ++ [w]
    s := t
    let c3 ← checkSum sumBin l (BitVec.ofNat 32 nn)
    passed := passed + c3
  IO.println s!"DIFF4-OK passed={passed} (edges + {trials} random trials)"
