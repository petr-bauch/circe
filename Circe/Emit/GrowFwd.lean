/-
Circe.Emit.GrowFwd — growth blit translations (value level).

Canonical home of the bulk word-copy folds the growth goldens render:
`stdVecBlitFold` (with source token), `stdVecBlitBackFold` (descending)
and `stdVecBlitFwdFold` (ascending). Names are unchanged from their
former `Circe.Base` home; only the address moved. The growth composers
(`Circe.Emit.VecCompose`), `VecGrow` leaves, transfer proofs and specs
import this module.
-/
import Circe.Base

/-! ## Bulk word-copy folds (growth relocation) -/

/-- Bulk word copy (`memmove` fused, N4d-iv-b1 `__relocate_a_1`): copy
    `n` words from `src` at `soff` to `dst` at `doff`. Reads go
    through the `vgrowAt` discipline (`freeS` is the source token:
    consumed source is `AssertFail`; `soff` at or past `lenS` is `OOB`,
    as is a short source list); writes go through `vecSet` (consumed
    or short destination propagates its error). Read-then-write per
    step, so overlapping ranges copy correctly. -/
def stdVecBlitFold (src : List (BitVec 32)) (lenS : Nat) (freeS : Bool)
    (dst : Vec32) (doff soff n : Nat) : Result Vec32 :=
  match n with
  | 0 => .ok dst
  | k + 1 =>
    if freeS then .error .AssertFail
    else if soff < lenS then
      match src[soff]? with
      | none => .error .OOB
      | some x =>
        match vecSet dst doff x with
        | .error e => .error e
        | .ok dst' =>
          stdVecBlitFold src lenS freeS dst' (doff + 1) (soff + 1) k
    else .error .OOB

/-- Backward blit: copy `n` words of `[soff, soff + n)` to
    `[doff, doff + n)` processing the top word first (N7c: the
    `move_backward` / `__copy_move_backward_a` / `_a1` / `_a2` /
    `__copy_move_b` chain fuses to the guarded `memmove`, which is
    this descending walk — read slot `soff + k` is never a previously
    written slot when `soff < doff`, so overlapping right-shifts are
    sound). Single triple (`src = dst`); `len` is the vector length
    (reads below it are live). -/
def stdVecBlitBackFold (b : Vec32) (len : Nat) (doff soff n : Nat) :
    Result Vec32 :=
  match n with
  | 0 => .ok b
  | k + 1 =>
    if b.freed then .error .AssertFail
    else if soff + k < len then
      match b.val[soff + k]? with
      | none => .error .OOB
      | some x =>
        match vecSet b (doff + k) x with
        | .error e => .error e
        | .ok b' => stdVecBlitBackFold b' len doff soff k
    else .error .OOB

/-- Forward blit: copy `n` words of `[soff, soff + n)` to
    `[doff, doff + n)` processing the bottom word first (N7d: the
    `std::move` / `__copy_move_a` / `_a1` / `_a2` / `__copy_m`
    chain fuses to the guarded `memmove`, which is this ascending
    walk — read slot `soff + (n - k)` is never a previously written
    slot when `doff < soff`, so overlapping left-shifts are
    sound). Single triple (`src = dst`); `len` is the vector length
    (reads below it are live). -/
def stdVecBlitFwdFold (b : Vec32) (len : Nat) (doff soff n : Nat) :
    Result Vec32 :=
  match n with
  | 0 => .ok b
  | k + 1 =>
    if b.freed then .error .AssertFail
    else if soff < len then
      match b.val[soff]? with
      | none => .error .OOB
      | some x =>
        match vecSet b doff x with
        | .error e => .error e
        | .ok b' => stdVecBlitFwdFold b' len (doff + 1) (soff + 1) k
    else .error .OOB
