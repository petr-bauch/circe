-- Golden test for N4b-i: the `move_int` pipeline.
--
-- `std::move` on `int` erases to a copy, so `_Z8move_intii` validates
-- as `add` under its mangled name (no new gate shape — the probe in
-- `tests/cir/move_int.cir` is body-identical to the `add` shape). The
-- pipeline must emit byte-identical text to
-- `tests/golden/MoveInt.lean` under the explicit `unknown` fact.
-- (N4b-ii adds the `move_acc` module pipeline below; N4b-iii adds
-- the `scope_early` module pipeline.)
-- Mismatch policy: any in-subset divergence is P0; out-of-subset must
-- reject loudly.
import Circe.Validator

namespace GoldenMove

/-- Int-only leaves need explicit `unknown` facts (pure functions skip
    the oracle check but the wiring still requires the entry). -/
def lookupFacts (names : List String) : IO (List OracleFact) := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut out : List OracleFact := []
  for n in names do
    match lookupOracle verdicts n with
    | none => throw (IO.userError s!"no oracle fact for {n}")
    | some o =>
      if !decide (o.verdict = .unknown) then
        throw (IO.userError s!"unexpected verdict for {n}")
      out := out ++ [o]
  pure out

def checkMoveIntPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/move_int.cir"
  let want ← IO.FS.readFile "tests/golden/MoveInt.lean"
  let facts ← lookupFacts ["_Z8move_intii"]
  match runModulePipeline text facts with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected move_int: {msg}")
  | .ok [("_Z8move_intii", got)] =>
    if got != want then
      throw (IO.userError "golden mismatch for move_int leaf")
    IO.println "PASS pipeline move_int (trivial move erases to add, explicit unknown fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- `move_acc` module pipeline: the entry plus the five `Acc` leaves.
    The entry needs its explicit `unknown` fact; the leaves validate
    under synthetic facts (single-reference `this` params). The four
    shared leaves must render byte-identical to the M2b goldens
    (cross-module leaf stability), the move-ctor leaf to
    `tests/golden/MoveCtor.lean`, the entry to
    `tests/golden/MoveAcc.lean`. -/
def checkMoveAccPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/move_acc.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/MoveAcc.lean"
  let wantCtor ← IO.FS.readFile "tests/golden/AccCtor.lean"
  let wantAdd ← IO.FS.readFile "tests/golden/AccAdd.lean"
  let wantMove ← IO.FS.readFile "tests/golden/MoveCtor.lean"
  let wantGet ← IO.FS.readFile "tests/golden/AccGet.lean"
  let wantDtor ← IO.FS.readFile "tests/golden/AccDtor.lean"
  let facts ← lookupFacts ["_Z8move_accii"]
  match runModulePipeline text facts with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected move_acc: {msg}")
  | .ok [("_Z8move_accii", gotEntry), ("_ZN3AccC2Ev", gotCtor),
      ("_ZN3Acc3addEi", gotAdd), ("_ZN3AccC2EOS_", gotMove),
      ("_ZNK3Acc3getEv", gotGet), ("_ZN3AccD2Ev", gotDtor)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for move_acc entry")
    if gotCtor != wantCtor then
      throw (IO.userError "golden mismatch for move_acc ctor leaf (M2b drift)")
    if gotAdd != wantAdd then
      throw (IO.userError "golden mismatch for move_acc add leaf (M2b drift)")
    if gotMove != wantMove then
      throw (IO.userError "golden mismatch for move-ctor leaf")
    if gotGet != wantGet then
      throw (IO.userError "golden mismatch for move_acc get leaf (M2b drift)")
    if gotDtor != wantDtor then
      throw (IO.userError "golden mismatch for move_acc dtor leaf (M2b drift)")
    IO.println "PASS pipeline move_acc (entry + 5 leaves, 4 shared goldens stable)"
    pure 6
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- `scope_early` module pipeline: the entry plus the four shared
    `Acc` leaves (cross-module stability against the M2b goldens). The
    entry needs its explicit `unknown` fact; the leaves validate under
    synthetic facts. -/
def checkScopeEarlyPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/scope_early.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ScopeEarly.lean"
  let wantCtor ← IO.FS.readFile "tests/golden/AccCtor.lean"
  let wantAdd ← IO.FS.readFile "tests/golden/AccAdd.lean"
  let wantGet ← IO.FS.readFile "tests/golden/AccGet.lean"
  let wantDtor ← IO.FS.readFile "tests/golden/AccDtor.lean"
  let facts ← lookupFacts ["_Z11scope_earlyii"]
  match runModulePipeline text facts with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected scope_early: {msg}")
  | .ok [("_Z11scope_earlyii", gotEntry), ("_ZN3AccC2Ev", gotCtor),
      ("_ZN3Acc3addEi", gotAdd), ("_ZNK3Acc3getEv", gotGet),
      ("_ZN3AccD2Ev", gotDtor)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for scope_early entry")
    if gotCtor != wantCtor then
      throw (IO.userError "golden mismatch for scope_early ctor leaf (M2b drift)")
    if gotAdd != wantAdd then
      throw (IO.userError "golden mismatch for scope_early add leaf (M2b drift)")
    if gotGet != wantGet then
      throw (IO.userError "golden mismatch for scope_early get leaf (M2b drift)")
    if gotDtor != wantDtor then
      throw (IO.userError "golden mismatch for scope_early dtor leaf (M2b drift)")
    IO.println "PASS pipeline scope_early (entry + 4 shared leaves stable)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkMoveIntPipeline
  passed := passed + c0
  let c1 ← checkMoveAccPipeline
  passed := passed + c1
  let c2 ← checkScopeEarlyPipeline
  passed := passed + c2
  IO.println s!"GOLDENMOVE-OK passed={passed}"

end GoldenMove
