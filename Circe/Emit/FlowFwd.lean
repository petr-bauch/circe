/-
Circe.Emit.FlowFwd — S3 control-flow program translations (value level).

Canonical home of the loop/reader definitions the S3 goldens render and
the `DiffFlow` fuzzer executes: `nestedSumU32` (with `rowU32`),
`skipSumU32`, `findEqOut` (with `findIdxU32`). Names are unchanged
from their former `Circe.Base` home; only the address moved. Proofs of
the emitted entries (`emit_correct_*`, `memTransfer_*`, user specs in
`Circe.Specs`) stay in their fragment modules and import this module.
-/
import Circe.Base

/-! ## S3a control-flow folds: `nested_sum` / `skip_sum` value models -/

/-- One row of `nested_sum`: `Σ_{j<m} i*j` as a wrapping `u32` sum of
    `ofNat` products (rendered `nested_sum_fwd` references this). -/
def rowU32 (i m : Nat) : BitVec 32 :=
  ((List.range m).map (fun j => BitVec.ofNat 32 (i * j))).sum

/-- `nested_sum`: `Σ_{i<n} rowU32 i m` (rendered forward reference). -/
def nestedSumU32 (n m : Nat) : BitVec 32 :=
  ((List.range n).map (fun i => rowU32 i m)).sum

/-- `skip_sum`: `Σ` of `i ∈ [0, min n 8)`, skipping `2` (rendered
    forward reference; `break` at `8` caps the range, `continue`
    filters `2`). -/
def skipSumU32 (n : Nat) : BitVec 32 :=
  (((List.range (min n 8)).filter (fun i => i != 2)).map
    (fun i => BitVec.ofNat 32 i)).sum

/-! ## `find_eq` value model: first match, length-narrowed -/

/-- First match of `k` in `l[j]?` over `j ∈ [0, min n len)` (rendered
    forward reference). The search never passes `min n len`, so an
    early hit returns even when `n` exceeds the length (the OOB read
    never happens); running past the length with no hit is `OOB`. -/
def findIdxU32 (l : List (BitVec 32)) (n : Nat) (k : BitVec 32) :
    Option Nat :=
  ((List.range (min n l.length)).find?
    (fun j => decide (l[j]? = some k)))

/-- `find_eq` outcome on values: the first match, else the length when
    exact, else `OOB` (C would read out of bounds there — UB made
    loud). The length test is `decide`-headed so proofs rewrite it
    with a boolean equation. -/
def findEqOut (l : List (BitVec 32)) (n : Nat) (k : BitVec 32) :
    Result (BitVec 32) :=
  match findIdxU32 l n k with
  | some j => .ok (BitVec.ofNat 32 j)
  | none =>
    if decide (n ≤ l.length) then .ok (BitVec.ofNat 32 n)
    else .error .OOB
