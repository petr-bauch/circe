/-
Circe.Emit.ArraySort8 — N9b closed `array_sort_sum8` program over
`std::array<uint32_t, 8>`: the 8-word entry + closed program +
instance proofs. The sort loop, leaves, and all correctness proofs
are the size-generic machinery from `Circe.Emit.ArraySort`
(`insertionSortFunc 8`, `evalFuncFuel_insertionSort`,
`memTransfer_insertionSort`); this module only adds the 8-wide
closed entry (8-word init, eight indexed reads, seven wrapping adds)
and the closed-program instance. Funcs carried in the program use
`with name` overrides to the Lm8EE monomorph names so the program
mirrors the validated CIR text (evaluation is name-agnostic).
-/
import Circe.Emit.ArraySort

/-- Canonical CoreIR for `array_sort_sum8`: const-record init, sort
    call, eight indexed reads, seven wrapping adds. -/
def arraySortSum8EntryFunc : Func :=
  ⟨arraySortSum8Name, [], .u 32,
   .seq (.let_ "a" (.array (.u 32) 8)
     (.lit (.arr32 [BitVec.ofNat 32 3, BitVec.ofNat 32 1,
       BitVec.ofNat 32 2, BitVec.ofNat 32 0, BitVec.ofNat 32 7,
       BitVec.ofNat 32 5, BitVec.ofNat 32 6, BitVec.ofNat 32 4])))
   (.seq (.callProg "s" insertionSort8Name ["a"])
   (.seq (.let_ "i0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq (.callRet "e0" arrayAtU32_8Name ["s", "i0"])
   (.seq (.let_ "i1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq (.callRet "e1" arrayAtU32_8Name ["s", "i1"])
   (.seq (.let_ "i2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
   (.seq (.callRet "e2" arrayAtU32_8Name ["s", "i2"])
   (.seq (.let_ "i3" (.u 64) (.lit (.u64 (BitVec.ofNat 64 3))))
   (.seq (.callRet "e3" arrayAtU32_8Name ["s", "i3"])
   (.seq (.let_ "i4" (.u 64) (.lit (.u64 (BitVec.ofNat 64 4))))
   (.seq (.callRet "e4" arrayAtU32_8Name ["s", "i4"])
   (.seq (.let_ "i5" (.u 64) (.lit (.u64 (BitVec.ofNat 64 5))))
   (.seq (.callRet "e5" arrayAtU32_8Name ["s", "i5"])
   (.seq (.let_ "i6" (.u 64) (.lit (.u64 (BitVec.ofNat 64 6))))
   (.seq (.callRet "e6" arrayAtU32_8Name ["s", "i6"])
   (.seq (.let_ "i7" (.u 64) (.lit (.u64 (BitVec.ofNat 64 7))))
   (.seq (.callRet "e7" arrayAtU32_8Name ["s", "i7"])
          (.return_ (.uadd (.uadd (.uadd (.uadd (.uadd (.uadd
            (.uadd (.var "e0") (.var "e1")) (.var "e2")) (.var "e3"))
            (.var "e4")) (.var "e5")) (.var "e6")) (.var "e7"))))))))))))))))))))⟩

/-- Value-level forward for `array_sort_sum8`: sort
    `[3, 1, 2, 0, 7, 5, 6, 4]`, add the eight words (wrapping). -/
def arraySortSum8EntryFwd : Result Value :=
  .ok (.u32 ((insertionSortList [BitVec.ofNat 32 3, BitVec.ofNat 32 1,
    BitVec.ofNat 32 2, BitVec.ofNat 32 0, BitVec.ofNat 32 7,
    BitVec.ofNat 32 5, BitVec.ofNat 32 6,
    BitVec.ofNat 32 4]).foldl (· + ·) (BitVec.ofNat 32 0)))

/-- Closed program for the N=8 case study: the two array leaves, the
    sort, and the entry (leaf/sort funcs carry the Lm8EE names). -/
def arraySortProg8 : Prog :=
  [{ arrayRefU32Func with name := arrayRefU32_8Name },
    { arrayAtU32Func with name := arrayAtU32_8Name },
    { (insertionSortFunc 8) with name := insertionSort8Name },
    arraySortSum8EntryFunc]

/-- `findFunc` resolves the sort callee. -/
theorem findFunc_insertionSort8 :
    findFunc arraySortProg8 insertionSort8Name =
      some ({ (insertionSortFunc 8) with name := insertionSort8Name }) := by
  unfold arraySortProg8
  rw [findFunc_miss _ _ _ (by decide), findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the indexed-read leaf. -/
theorem findFunc_arrayAtU32_8 :
    findFunc arraySortProg8 arrayAtU32_8Name =
      some ({ arrayAtU32Func with name := arrayAtU32_8Name }) := by
  unfold arraySortProg8
  rw [findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `emit_correct` for `array_sort_sum8`: the closed entry over the
    sort program agrees with the compute-to-`28` forward.

    Collapsed proof (`cir_eval_closed`): both sides are closed terms,
    so the proof is computation, not reasoning. Fuel is `15`, the
    sort's own `(8-1)+8` budget (same accounting as the N=4 entry,
    whose fuel equals the sort fuel). -/
theorem evalProgFunc_arraySortSum8Entry :
    evalProgFunc arraySortProg8 15 arraySortSum8EntryFunc [] =
      arraySortSum8EntryFwd := by
  cir_eval_closed
