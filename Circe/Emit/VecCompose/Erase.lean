/-
Circe.Emit.VecCompose.Erase — N7d single-element `erase` over the
frozen N4d+N7b leaves (ii-a: value forwards; proofs land in the
ii-b/c/d slices).

The corpus `erase(const_iterator)` forwarder converts to an erased
`u64` position and delegates into `_M_erase`; the core is a 2-arm
composer over erased positions:
- last (`pos + 1 == len`): no shift, shrink to `len - 1`;
- else: shift `[pos + 1, len)` down to `pos`, shrink to `len - 1`
  (the per-element `destroy` is trivial for `int`, so the shrink is
  the whole effect).

The shift (`std::move` → `__copy_move_a` → `_a1` → `_a2` →
`__copy_m`, with `__miter_base` / `__niter_base` / `__niter_wrap`
fused) is ONE canonical `Func`: the guarded `memmove` is an
ascending copy walk (`stdVecBlitFwdFold` in `Circe.Base` — the
bottom word moves first, so overlapping left-shifts are sound).
The `__copy_m` `if (_Num)` guard is subsumed by the trip count;
its pointer return drops (callers recompute offsets).

Iterator leaf: `ne` (`une` over erased offsets).
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose.Base

/-- Value-level forward for the ascending shift. -/
def stdVecShiftDownFwd (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) : Result Value :=
  match stdVecBlitFwdFold b len result.toNat first.toNat
      (last.toNat - first.toNat) with
  | .error e => .error e
  | .ok b' => .ok (.stdVecOwned b' len cap)

/-- Value-level forward for iterator inequality. -/
def stdVecIterNeFwd (a b : BitVec 64) : Result Value :=
  .ok (.b (a != b))

/-- Value-level forward for `_M_erase`. -/
def stdVecEraseCoreFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64) :
    Result Value :=
  if pos.toNat + 1 == len then .ok (.stdVecOwned b (len - 1) cap)
  else
    (stdVecShiftDownFwd b len cap (pos + 1) (BitVec.ofNat 64 len)
      pos).bind fun s =>
    vecGrowOwned s |>.bind fun (b', _, _) =>
      .ok (.stdVecOwned b' (len - 1) cap)

/-- Value-level forward for the `erase` forwarder (delegates to the
    core; the iterator return drops). -/
def stdVecEraseFwd (b : Vec32) (len cap : Nat) (pos : BitVec 64) :
    Result Value :=
  stdVecEraseCoreFwd b len cap pos

/-- Mangled name of the closed `vec_erase_sum` entry. -/
def vecEraseSumEntryName : String := "_Z13vec_erase_sumv"

/-- Canonical CoreIR for the closed `vec_erase_sum` entry: default
    ctor, `reserve(10)`, three pushes (`1`, `2`, `3`), `begin` + one
    step, one `erase` (at position `1`, iterator drops), two
    indexed reads, one add, destructor (ii-b proves the forward
    computes `1 + 3 = 4`). -/
def vecEraseSumEntryFunc : Func :=
  ⟨vecEraseSumEntryName, [], .i 32,
   .seq (.callRet "v0" stdVecCtorName [])
   (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
   (.seq (.callProg "v1" stdVecReserveName ["v0", "n"])
   (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
   (.seq (.callProg "v2" stdVecPushBackName ["v1", "c0"])
   (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
   (.seq (.callProg "v3" stdVecPushBackName ["v2", "c1"])
   (.seq (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
   (.seq (.callProg "v4" stdVecPushBackName ["v3", "c2"])
   (.seq (.callRet "bpos" stdVecBeginName ["v4"])
   (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "p1" stdVecPlusElName ["bpos", "one"])
   (.seq (.callProg "v5" stdVecEraseName ["v4", "p1"])
   (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.callRet "e0" stdVecGrowIndexName ["v5", "n0"])
   (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "e1" stdVecGrowIndexName ["v5", "n1"])
   (.seq (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
   (.seq (.callRet "v6" stdVecDtorName ["v5"])
     (.return_ (.var "s"))))))))))))))))))))⟩
