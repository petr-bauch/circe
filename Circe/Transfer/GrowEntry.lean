/-
Circe.Transfer.GrowEntry — N4d-iv-b2 `vec_push_sum` entry transfer.
Over `Circe.Transfer.GrowEmplace`.
-/
import Circe.Transfer.GrowEmplace

/-! ## N4d-iv-b2 `vec_push_sum` entry: memory agreement -/

/-- `memEval` for the closed entry: sixteen steps over `emptyMem`/`[]`
    (no caller footprint; every callee runs on its own binding) agree
    with `vecPushSumEntryFwd`.

    N8c: this was a ~1490-line hand evaluation mirroring
    `evalProgFunc_vecPushSumEntry` step for step. Both sides are
    closed terms, so the proof is `cir_eval_closed` (see the
    value-side note for the argument, and `Circe.Eval.Core` for why
    `native_decide` and not `rfl`). -/
theorem memEvalProgFunc_vecPushSumEntry :
    memEvalProgFunc vecGrowProg 6 vecPushSumEntryFunc [] =
      vecPushSumEntryFwd := by
  cir_eval_closed


/-- Transfer for the closed entry: program evaluation over the proved
    composer agrees on both sides (no caller footprint; the empty
    layout from `oracleNoalias_vecPushSumEntry` suffices). -/
theorem memTransfer_vecPushSumEntry
    (_h : oracleNoalias vecPushSumEntryFunc []) :
    memEvalProgFunc vecGrowProg 6 vecPushSumEntryFunc [] =
      evalProgFunc vecGrowProg 6 vecPushSumEntryFunc [] := by
  rw [memEvalProgFunc_vecPushSumEntry, evalProgFunc_vecPushSumEntry]



