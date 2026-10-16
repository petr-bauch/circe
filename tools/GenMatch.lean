-- Generator for `matchFrag` arms of large entry Funcs (C2 first
-- customer: the `merge_runs` callee + the `vec_merge_sort` entry,
-- whose 100-line bodies are never hand-transcribed).
-- Run from the repo root: `lake env lean --run tools/GenMatch.lean`
-- Prints each arm in `Match.lean` house style: fully literal except
-- `BitVec` words, which are bound + guarded since `BitVec.ofNat`
-- is not a pattern. Splice the output after the previous entry arm
-- and add the `matchFrag_<name> ... := rfl` theorem (the `rfl`
-- verifies the pattern; a corpus accept/cross-reject probe checks
-- the gate before commit). To cover a new entry: import its module
-- and add one `genArm` line in `main`.
import Circe.Emit.VecMergeRuns
import Circe.Emit.VecMergeSort

/-- Print one match arm for `f` in `Match.lean` house style:
    fully literal except `BitVec` words (bound + guarded, since
    `BitVec.ofNat` is not a pattern). Sub-defs (`mergeRunsMain`,
    `sortSegLoop`, ...) arrive already unfolded: passing a `CStmt`
    evaluates it to its constructor tree. -/
def genTy : CType → String
  | .void => ".void"
  | .bool => ".bool"
  | .i w => s!".i {w}"
  | .u w => s!".u {w}"
  | .array t n => s!".array {genTy t} {n}"
  | .struct name fields =>
    ".struct \"" ++ name ++ "\" [" ++
      String.intercalate ", " (fields.map genTy) ++ "]"
  | .vecBlock => ".vecBlock"

def genRole : BorrowRole → String
  | .owned => ".owned"
  | .mutBorrow _ => ".mutBorrow _"
  | .sharedBorrow => ".sharedBorrow"
  | .pinnedCell => ".pinnedCell"

def genParam (p : Param) : String :=
  "⟨\"" ++ p.name ++ "\", " ++ genTy p.ty ++ ", " ++
    genRole p.role ++ "⟩"

def genStrs (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map (fun x => "\"" ++ x ++ "\"")) ++ "]"

structure GenS where
  next : Nat
  guards : Array (Nat × Nat × String)

abbrev GenM := StateT GenS IO

def freshBV (w v : Nat) : GenM String := fun s =>
  let nm := s!"w{s.next}"
  let nx := s.next + 1
  let gs := s.guards.push (w, v, nm)
  pure (nm, { next := nx, guards := gs })

def genLit : CLit → GenM String
  | .i32 v => do return s!"(.i32 {← freshBV 32 v.toNat})"
  | .u32 v => do return s!"(.u32 {← freshBV 32 v.toNat})"
  | .i64 v => do return s!"(.i64 {← freshBV 64 v.toNat})"
  | .u64 v => do return s!"(.u64 {← freshBV 64 v.toNat})"
  | .b b => return s!"(.b {b})"
  | .arr32 _ => throw (IO.userError "arr32 literal in body")

def genExpr : CExpr → GenM String
  | .lit l => do return s!"(.lit {← genLit l})"
  | .var x => return s!"(.var \"{x}\")"
  | .add a b => do return s!"(.add {← genExpr a} {← genExpr b})"
  | .uadd a b => do return s!"(.uadd {← genExpr a} {← genExpr b})"
  | .usub a b => do return s!"(.usub {← genExpr a} {← genExpr b})"
  | .s64diff a b => do return s!"(.s64diff {← genExpr a} {← genExpr b})"
  | .tif c t e => do
    return s!"(.tif {← genExpr c} {← genExpr t} {← genExpr e})"
  | .umul a b => do return s!"(.umul {← genExpr a} {← genExpr b})"
  | .neg a => do return s!"(.neg {← genExpr a})"
  | .sdiv a b => do return s!"(.sdiv {← genExpr a} {← genExpr b})"
  | .bxor a b => do return s!"(.bxor {← genExpr a} {← genExpr b})"
  | .band a b => do return s!"(.band {← genExpr a} {← genExpr b})"
  | .bor a b => do return s!"(.bor {← genExpr a} {← genExpr b})"
  | .bshl a b => do return s!"(.bshl {← genExpr a} {← genExpr b})"
  | .bshr a b => do return s!"(.bshr {← genExpr a} {← genExpr b})"
  | .ult a b => do return s!"(.ult {← genExpr a} {← genExpr b})"
  | .slt a b => do return s!"(.slt {← genExpr a} {← genExpr b})"
  | .ueq a b => do return s!"(.ueq {← genExpr a} {← genExpr b})"
  | .une a b => do return s!"(.une {← genExpr a} {← genExpr b})"
  | .idx s e => do return s!"(.idx \"{s}\" {← genExpr e})"
  | .optHas s => return s!"(.optHas \"{s}\")"
  | .optGet s => return s!"(.optGet \"{s}\")"
  | .spanLen s => return s!"(.spanLen \"{s}\")"
  | .spanAt s e => do return s!"(.spanAt \"{s}\" {← genExpr e})"
  | .viewLen s => return s!"(.viewLen \"{s}\")"
  | .viewAt s e => do return s!"(.viewAt \"{s}\" {← genExpr e})"
  | .stdVecLen s => return s!"(.stdVecLen \"{s}\")"
  | .stdVecAt s e => do return s!"(.stdVecAt \"{s}\" {← genExpr e})"
  | .vgrowLen s => return s!"(.vgrowLen \"{s}\")"
  | .vgrowCap s => return s!"(.vgrowCap \"{s}\")"
  | .vgrowAt s e => do return s!"(.vgrowAt \"{s}\" {← genExpr e})"
  | .vgrowNew e => do return s!"(.vgrowNew {← genExpr e})"
  | .vgrowSetLen s e => do
    return s!"(.vgrowSetLen \"{s}\" {← genExpr e})"
  | .u64ofI64 e => do return s!"(.u64ofI64 {← genExpr e})"
  | .idxi s e => do return s!"(.idxi \"{s}\" {← genExpr e})"
  | .idxu s e => do return s!"(.idxu \"{s}\" {← genExpr e})"
  | .vnew e => do return s!"(.vnew {← genExpr e})"
  | .vget s e => do return s!"(.vget \"{s}\" {← genExpr e})"
  | .boxNew e => do return s!"(.boxNew {← genExpr e})"
  | .boxGet s => return s!"(.boxGet \"{s}\")"
  | .fget s f => return s!"(.fget \"{s}\" \"{f}\")"
  | .pmk x y => do return s!"(.pmk {← genExpr x} {← genExpr y})"
  | .pair x y => do return s!"(.pair {← genExpr x} {← genExpr y})"
  | .i32ofU64 e => do return s!"(.i32ofU64 {← genExpr e})"
  | .mload s e => do return s!"(.mload \"{s}\" {← genExpr e})"

def genStmt : CStmt → GenM String
  | .skip => return ".skip"
  | .seq a b => do return s!"(.seq {← genStmt a} {← genStmt b})"
  | .cleanup body => do return s!"(.cleanup {← genStmt body})"
  | .let_ n t v => do
    return s!"(.let_ \"{n}\" ({genTy t}) {← genExpr v})"
  | .assign n v => do return s!"(.assign \"{n}\" {← genExpr v})"
  | .vset v i x => do
    return s!"(.vset \"{v}\" {← genExpr i} {← genExpr x})"
  | .vrealloc v m => do return s!"(.vrealloc \"{v}\" {← genExpr m})"
  | .vfree v => return s!"(.vfree \"{v}\")"
  | .boxFree b => return s!"(.boxFree \"{b}\")"
  | .vgrowSet t i x => do
    return s!"(.vgrowSet \"{t}\" {← genExpr i} {← genExpr x})"
  | .vgrowFree t => return s!"(.vgrowFree \"{t}\")"
  | .arrSet a i x => do
    return s!"(.arrSet \"{a}\" {← genExpr i} {← genExpr x})"
  | .vecSet s i x => do
    return s!"(.vecSet \"{s}\" {← genExpr i} {← genExpr x})"
  | .mstore s i x => do
    return s!"(.mstore \"{s}\" {← genExpr i} {← genExpr x})"
  | .fail => return ".fail"
  | .if_ c t e => do
    return s!"(.if_ {← genExpr c} {← genStmt t} {← genStmt e})"
  | .while_ c b => do
    return s!"(.while_ {← genExpr c} {← genStmt b})"
  | .break_ => return ".break_"
  | .continue_ => return ".continue_"
  | .call f args => return s!"(.call \"{f}\" {genStrs args})"
  | .callRet d f args =>
    return s!"(.callRet \"{d}\" \"{f}\" {genStrs args})"
  | .callProg d f args =>
    return s!"(.callProg \"{d}\" \"{f}\" {genStrs args})"
  | .return_ v => do return s!"(.return_ {← genExpr v})"

def genArm (f : Func) (kind : String) : IO String := do
  let prog : GenM (String × List String × String) := do
    let b ← genStmt f.body
    return (b, f.args.map genParam, genTy f.ret)
  let (res, st) ← prog { next := 0, guards := #[] }
  let (body, (params, ret)) := res
  let paramText := String.intercalate ",\n        " params
  let guardText :=
    String.intercalate " &&\n        " (st.guards.toList.map
      (fun (w, v, nm) => s!"{nm} == BitVec.ofNat {w} {v}"))
  return s!"  | ⟨_, [{paramText}],\n      {ret},\n      {body}⟩ =>\n    if {guardText} then\n      some .{kind}\n    else none\n"

def main : IO Unit := do
  IO.println "===== MERGERUNS ARM ====="
  IO.println (← genArm VecMergeRuns.mergeRunsFunc "vecMergeRuns")
  IO.println "===== MERGESORT ARM ====="
  IO.println (← genArm VecMergeSort.vecMergeSortFunc "vecMergeSort")
