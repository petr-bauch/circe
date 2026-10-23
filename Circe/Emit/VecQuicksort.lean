/-
P2-M8 recursive quicksort over `std::vector<int>`.

Corpus: `tests/cpp/vec_quicksort.cpp` →
`tests/cir/vec_quicksort.cir` (entry
`_Z13vec_quicksortRSt6vectorIiSaIiEEmm`: one `mutBorrow`
vector + two owned `u64` bounds, `void` out; two early returns,
an inline Lomuto partition loop with a conditional swap, the
pivot place, and two self-calls on the strictly smaller ranges).

Model (the `vec_partition` fusion precedent): the `at()` reads
fuse into the pure reads (`stdVecAt`); both swap writes carry
the loop-guard shape (`i < hi - 1`, and `s ≤ i` keeps the `s`
write in bounds — the guard justifies every access, so the
model is total). The `slt` comparison on `s32` maps to the
plain signed less-than (total); the `u64` counter bumps are the
plain `.uadd` (exact below `2 ^ 64` by the length bound, the
`bv64_succ_toNat` idiom). The self-calls are `callProg` (fuel
steps down at each call — the spike result — so the model
terminates by fuel with exhaustion as `AssertFail`, the Rule 7
precedent). The `void` entry returns the sorted words (the
`xor_n` out-param idiom).
-/
import Circe.Emit.VecAtSet

namespace VecQuicksort

/-- Function name (Itanium mangling of a `vec_quicksort` free
    function taking `vector<int>&` + two `unsigned long`, returning
    `void`). -/
def vecQuicksortName : String :=
  "_Z13vec_quicksortRSt6vectorIiSaIiEEmm"

/-- Partition loop body: conditional swap of `v[i]` below the pivot
    to the store front, then advance `i`. -/
def qsPartBody : CStmt :=
  (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
            (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
              (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
                (.seq (.vecSet "v" (.var "s") (.var "t"))
                  (.assign "s"
                    (.uadd (.var "s") (.lit (.u64 (BitVec.ofNat 64 1))))))))
            .skip)
    (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- Partition loop `while (i < hi - 1) body`. -/
def qsPartLoop : CStmt :=
  (.while_ (.ult (.var "i")
    (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))) qsPartBody)

/-- Pivot place: `v[hi-1] ↔ v[s]` via the fused read/write pair. -/
def qsPlacePivot : CStmt :=
  (.seq (.vecSet "v"
          (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))
          (.stdVecAt "v" (.var "s")))
    (.vecSet "v" (.var "s") (.var "pivot")))

/-- Left self-call on `[lo, s)` (rebinds `"v"` to the sorted words). -/
def qsCallLeft : CStmt :=
  (.callProg "v" vecQuicksortName ["v", "lo", "s"])

/-- Right self-call on `[s+1, hi)` (rebinds `"v"` again). -/
def qsCallRight : CStmt :=
  (.callProg "v" vecQuicksortName ["v", "s1", "hi"])

/-- Whole function: two early returns (empty range, singleton),
    pivot/store/index prelude, partition loop, pivot place, the two
    self-calls, and the sorted words return. -/
def vecQuicksortFunc : Func :=
  ⟨vecQuicksortName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "lo", ty := .u 64, role := .owned },
    { name := "hi", ty := .u 64, role := .owned }],
   stdVecObjTy,
   (.if_ (.ult (.var "lo") (.var "hi"))
     (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 1)))
               (.usub (.var "hi") (.var "lo")))
       (.seq (.let_ "pivot" (.i 32)
               (.stdVecAt "v"
                 (.usub (.var "hi") (.lit (.u64 (BitVec.ofNat 64 1))))))
         (.seq (.let_ "s" (.u 64) (.var "lo"))
           (.seq (.let_ "i" (.u 64) (.var "lo"))
             (.seq qsPartLoop
               (.seq qsPlacePivot
                 (.seq (.let_ "s1" (.u 64)
                         (.uadd (.var "s")
                           (.lit (.u64 (BitVec.ofNat 64 1)))))
                   (.seq qsCallLeft
                     (.seq qsCallRight
                       (.return_ (.var "v"))))))))))
       (.return_ (.var "v")))
     (.return_ (.var "v")))⟩

/-- The quicksort program (single function; self-calls resolve by
    `findFunc` against this list). -/
def vecQuicksortProg : Prog := [vecQuicksortFunc]

/-! ## Forward models (fuel-threaded, mirroring evaluation) -/

/-- One Lomuto pass over `[i, hi)` with pivot `pivot`, store bound
    `s`. Fuel 0 returns the state so far (no more progress — the V1
    miss-default idiom); the `none` arms are unreachable
    in-invariant (every access is guard-justified: `i < hi - 1`
    from the loop guard, `s ≤ i` from the scan). -/
def qsPartFwd (pivot : BitVec 32) :
    List (BitVec 32) → Nat → Nat → Nat → Nat →
      Result (Nat × List (BitVec 32))
  | l, 0, _, _, s => .ok (s, l)
  | l, fuel + 1, hi, i, s =>
    if i + 1 < hi then
      match l[i]?, l[s]? with
      | some x, some w =>
        if x.slt pivot then
          qsPartFwd pivot ((l.set i w).set s x) fuel hi (i + 1) (s + 1)
        else qsPartFwd pivot l fuel hi (i + 1) s
      | _, _ => .error .AssertFail
    else .ok (s, l)

/-- Whole-function forward: the length guard, the pivot read, one
    partition pass, then the two recursive sorts at one less fuel
    (mirroring the `callProg` fuel step). Fuel 0 returns the input
    unchanged. -/
def vecQuicksortFwd :
    List (BitVec 32) → Nat → Nat → Nat → Result (List (BitVec 32))
  | l, 0, _, _ => .ok l
  | l, fuel + 1, lo, hi =>
    if lo < hi then
      if 1 < hi - lo then
        match l[hi - 1]? with
        | none => .error .AssertFail
        | some pivot =>
          match qsPartFwd pivot l fuel hi lo lo with
          | .error e => .error e
          | .ok (s, l1) =>
            match l1[s]?, l1[hi - 1]? with
            | some w, some _ =>
              let l1' := ((l1.set (hi - 1) w).set s pivot)
              match vecQuicksortFwd l1' fuel lo s with
              | .error e => .error e
              | .ok l2 => vecQuicksortFwd l2 fuel (s + 1) hi
            | _, _ => .error .AssertFail
      else .ok l
    else .ok l

end VecQuicksort
