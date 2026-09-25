/-
Circe.Oracle — ownership-oracle verdict import (trusted).

Uniqueness verdicts come from Clang/CIR analysis (lifetime analysis +
CIR lifetime-checker prototype + LLVM `basicaa`), not from user proofs.
The translator trusts the oracle's `noalias` verdict per function;
`validate` rejects the function when the oracle is inconclusive.
Oracle verdict dumps are checked in under `tests/oracle/` (Phase 4;
currently a placeholder — see docs/PINS.md).
-/

/-- Per-function alias verdict from the oracle. -/
inductive Verdict : Type
  | noalias
  | mayAlias
  | unknown
  deriving DecidableEq, Repr

/-- One imported oracle fact: the verdict for a function. -/
structure OracleFact : Type where
  funcName : String
  verdict : Verdict
  deriving DecidableEq, Repr

/-- A function is translatable only on an explicit `noalias` verdict.
    Anything else is rejected loudly by `validate`. -/
def verdictAdmits (v : Verdict) : Bool :=
  match v with
  | .noalias => true
  | _ => false

/-! ## Verdict file import (trusted, Phase 4) -/

/-- Split text into lines. -/
def splitLinesAux : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (acc ++ [cur.reverse]).filter (fun l => !l.isEmpty)
  | '\n' :: cs, cur, acc => splitLinesAux cs [] (acc ++ [cur.reverse])
  | c :: cs, cur, acc => splitLinesAux cs (c :: cur) acc

def splitLines (s : String) : List String :=
  (splitLinesAux s.toList [] []).map String.ofList

/-- Split a line on spaces/tabs. -/
def splitSpacesAux : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (acc ++ [cur.reverse]).filter (fun l => !l.isEmpty)
  | ' ' :: cs, cur, acc => splitSpacesAux cs [] (acc ++ [cur.reverse])
  | '\t' :: cs, cur, acc => splitSpacesAux cs [] (acc ++ [cur.reverse])
  | c :: cs, cur, acc => splitSpacesAux cs (c :: cur) acc

/-- Parse one verdict token. -/
def parseVerdict : String → Option Verdict
  | "noalias" => some .noalias
  | "mayAlias" => some .mayAlias
  | "unknown" => some .unknown
  | _ => none

/-- Parse one `tests/oracle/verdicts.txt` line (`<func> <verdict>`,
    `#` comments, malformed lines dropped). -/
def parseOracleLine (line : String) : Option OracleFact :=
  let t := line.trimAscii.toString
  match t.toList with
  | '#' :: _ => none
  | _ =>
    match (splitSpacesAux t.toList [] []).filter (fun l => !l.isEmpty) |>.map String.ofList with
    | [name, vs] =>
      match parseVerdict vs with
      | some v => some ⟨name, v⟩
      | none => none
    | _ => none

/-- Parse a whole verdicts file. -/
def parseOracleFacts (text : String) : List OracleFact :=
  (splitLines text).filterMap parseOracleLine

/-- Look up a function's fact (`none` when missing — `validate` then
    rejects loudly). -/
def lookupOracle : List OracleFact → String → Option OracleFact
  | [], _ => none
  | f :: fs, name => if f.funcName == name then some f else lookupOracle fs name
