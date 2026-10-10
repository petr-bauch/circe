-- Differential KAT for the K3 quarter-round fold: verified Lean
-- `qrStep` vs the native C quarter round (test-only scaffolding in
-- `tests/diff/driver_qr.c` — never corpus, never admitted), plus the
-- RFC 8439 §2.1.1 vector as a directed leg.
--
-- Run: `lake env lean --run tests/lean/DiffQr.lean <qrbin> [trials]`
-- Every trial asserts the fold agrees with native on a random
-- 4-tuple (the fold is total — wrapping add, fixed in-range
-- rotates — so every trial compares against native).
-- Mismatch = P0.
import Circe.Crypto.Qr

namespace DiffQr

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Run a native binary with args, returning trimmed stdout. -/
def runNative (bin : String) (args : Array String) : IO String := do
  let out ← IO.Process.run { cmd := bin, args := args }
  pure out.trimAscii.toString

/-- The RFC 8439 §2.1.1 vector (cross-checked: 6+ web sources agree;
    a from-pseudocode Python implementation reproduces it). -/
def qrKatIn : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  (0x11111111, 0x01020304, 0x9b8d6f43, 0x01234567)

/-- Expected words after one quarter round. -/
def qrKatOut : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb)

def checkQr (qrBin : String) (a b c d : BitVec 32) : IO Nat := do
  let (a', b', c', d') := qrStep a b c d
  let native ← runNative qrBin
    #[toString a.toNat, toString b.toNat, toString c.toNat,
      toString d.toNat]
  let ws := native.splitOn " "
  if ws.length != 4 then
    throw (IO.userError s!"qr native arity unparsable: {native}")
  let vs := [a', b', c', d']
  for p in ws.zip vs do
    match p.1.toNat? with
    | none => throw (IO.userError s!"qr native unparsable: {native}")
    | some m =>
      if m != p.2.toNat then
        throw (IO.userError s!"qr mismatch: lean={p.2.toNat} native={m}")
  pure 1

def main (args : List String) : IO Unit := do
  let qrBin := args.getD 0 "/tmp/opencode/circe_qr_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  -- Directed KAT leg: the fold computes the RFC vector.
  let got := qrStep qrKatIn.1 qrKatIn.2.1 qrKatIn.2.2.1 qrKatIn.2.2.2
  if (repr got).pretty != (repr qrKatOut).pretty then
    throw (IO.userError s!"qr KAT mismatch (fold disagrees with RFC 8439 §2.1.1)")
  IO.println s!"PASS qr KAT (§2.1.1)"
  passed := passed + 1
  -- The KAT through native too (driver sanity on the same words).
  let c0 ← checkQr qrBin qrKatIn.1 qrKatIn.2.1 qrKatIn.2.2.1 qrKatIn.2.2.2
  passed := passed + c0
  -- Zero round-trips (second library leg, via native as well).
  let c1 ← checkQr qrBin 0 0 0 0
  passed := passed + c1
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    let mut w : List (BitVec 32) := []
    for _ in List.range 4 do
      s := lcgNext s
      w := BitVec.ofNat 32 (s % 2 ^ 32) :: w
    match w with
    | [a, b, c, d] =>
      let c2 ← checkQr qrBin a b c d
      passed := passed + c2
    | _ => throw (IO.userError s!"unreachable: fuzz tuple shape")
    s := lcgNext s
  IO.println s!"DIFFQR-OK passed={passed} (KAT + {trials} random trials)"

end DiffQr
