/-
Circe.Emit.ArraySort — N9 insertion sort over `std::array<uint32_t, 4>`:
the `__array_traits::_S_ref` unchecked-index leaf (u32 monomorph) +
mutating `operator[]` + the sort loop + the `array_sort_sum` entry.

Fusion follows the N4d-i precedent one level up: the subscript-call +
load fuses into the `idxu` read downstream, and the subscript-call +
`cir.store` fuses into `arrSet` downstream (the call itself is a pure
projection, so the fused read is harmless). `_S_ref` still validates
separately (same value story), so misshapen variants of either def
reject loudly. The `while` condition's short-circuit `&&`
(`cir.ternary` over `j > 0`) maps to `tif` (lazy in the untaken arm,
so index `j - 1` never evaluates at `j = 0`); `cir.dec` fuses to
`usub`-one like `cir.inc` fuses to `uadd`-one.

The sort returns the array (C++ `void` functionalizes as threaded
state, the `push_back` precedent), so the entry communicates with it
by value like every N7 composer.
-/
import Circe.Emit.Fragment

/-! ## N9: `std::array<uint32_t, 4>` sort leaves, loop, entry -/

/-- Mangled callee names in `tests/cpp/array_sort_sum.cpp`. -/
def arrayRefU32Name : String :=
  "_ZNSt14__array_traitsIjLm4EE6_S_refERA4_Kjm"
def arrayAtU32Name : String := "_ZNSt5arrayIjLm4EEixEm"
def insertionSortName : String := "_Z14insertion_sortRSt5arrayIjLm4EE"
def arraySortSumName : String := "_Z14array_sort_sumv"

/-- Canonical CoreIR for the u32 `_S_ref` leaf: unchecked `u64` index
    into the 4-word `u32` array (`cir.get_element`, OOB is UB so the
    model reports `OOB`). -/
def arrayRefU32Func : Func :=
  ⟨arrayRefU32Name,
   [{ name := "t", ty := .array (.u 32) 4, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .u 32,
   .return_ (.idxu "t" (.var "n"))⟩

/-- Canonical CoreIR for the mutating `operator[]`: the `_M_elems`
    projection + `_S_ref` call fused into the `idxu` read (the store
    path fuses into `arrSet` downstream instead). -/
def arrayAtU32Func : Func :=
  ⟨arrayAtU32Name,
   [{ name := "a", ty := .array (.u 32) 4, role := .mutBorrow 0 },
    { name := "n", ty := .u 64, role := .owned }],
   .u 32,
   .return_ (.idxu "a" (.var "n"))⟩

/-- Canonical CoreIR for `insertion_sort`: outer `for`-as-`while`
    over `i in [1, 4)`, inner `while` over the short-circuit
    condition, swap via temp + two `arrSet`s, counters via
    `assign`. -/
def insertionSortFunc : Func :=
  ⟨insertionSortName,
   [{ name := "a", ty := .array (.u 32) 4, role := .mutBorrow 0 }],
   .array (.u 32) 4,
   .seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.while_ (.ult (.var "i") (.lit (.u64 (BitVec.ofNat 64 4))))
     (.seq (.let_ "j" (.u 64) (.var "i"))
     (.seq (.while_
       (.tif (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
         (.ult (.idxu "a" (.var "j"))
           (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
         (.lit (.b false)))
       (.seq (.let_ "t" (.u 32) (.idxu "a" (.var "j")))
       (.seq (.arrSet "a" (.var "j")
                (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
       (.seq (.arrSet "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
                (.var "t"))
         (.assign "j" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))))))
       (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))))))
   (.return_ (.var "a")))⟩

/-- Canonical CoreIR for `array_sort_sum`: const-record init (the
    `trailing_zeros` fourth word folded in), sort call, four indexed
    reads, three wrapping adds. -/
def arraySortSumEntryFunc : Func :=
  ⟨arraySortSumName, [], .u 32,
   .seq (.let_ "a" (.array (.u 32) 4)
     (.lit (.arr32 [BitVec.ofNat 32 3, BitVec.ofNat 32 1,
       BitVec.ofNat 32 2, BitVec.ofNat 32 0])))
   (.seq (.callProg "s" insertionSortName ["a"])
   (.seq (.let_ "i0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.callRet "e0" arrayAtU32Name ["s", "i0"])
   (.seq (.let_ "i1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "e1" arrayAtU32Name ["s", "i1"])
   (.seq (.let_ "i2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
   (.seq (.callRet "e2" arrayAtU32Name ["s", "i2"])
   (.seq (.let_ "i3" (.u 64) (.lit (.u64 (BitVec.ofNat 64 3))))
   (.seq (.callRet "e3" arrayAtU32Name ["s", "i3"])
          (.return_ (.uadd (.uadd (.uadd (.var "e0") (.var "e1"))
            (.var "e2")) (.var "e3"))))))))))))⟩

/-- Value-level forward for the u32 `_S_ref`: the word at `u64` index
    `n`, `OOB` off the end. -/
def arrayRefU32Fwd (l : List (BitVec 32)) (n : BitVec 64) :
    Result Value :=
  match l[n.toNat]? with
  | some x => .ok (.u32 x)
  | none => .error .OOB

/-- Value-level forward for the mutating `operator[]`: the same read
    (the call edge is fused, so the forward is the leaf forward by
    definition). -/
def arrayAtU32Fwd (l : List (BitVec 32)) (n : BitVec 64) :
    Result Value :=
  arrayRefU32Fwd l n

theorem arrayAtU32Fwd_is_call (l : List (BitVec 32)) (n : BitVec 64) :
    arrayAtU32Fwd l n = arrayRefU32Fwd l n := rfl

/-- Pure insertion sort over words (structural; the forward below runs
    it and wraps the result back into an array value). Insert before
    the first strictly greater word: equal words keep their relative
    order, matching the loop (which swaps only on strict `>`). -/
def insertU32 (x : BitVec 32) : List (BitVec 32) → List (BitVec 32)
  | [] => [x]
  | y :: ys => if x.ult y then x :: y :: ys else y :: insertU32 x ys

def insertionSortList : List (BitVec 32) → List (BitVec 32)
  | [] => []
  | x :: xs => insertU32 x (insertionSortList xs)

/-- Value-level forward for `insertion_sort`: the sorted array. -/
def insertionSortFwd (l : List (BitVec 32)) : Result Value :=
  .ok (.arr32 (insertionSortList l))

/-- Value-level forward for `array_sort_sum`: sort `[3, 1, 2, 0]`,
    add the four words (wrapping). -/
def arraySortSumEntryFwd : Result Value :=
  .ok (.u32 ((insertionSortList [BitVec.ofNat 32 3, BitVec.ofNat 32 1,
    BitVec.ofNat 32 2, BitVec.ofNat 32 0]).foldl (· + ·) (BitVec.ofNat 32 0)))
