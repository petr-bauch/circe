/-
Circe.Parser — unverified, trusted text → `RawIR` front end.

Raw CIRGen output (`cir.func`, `cir.alloca/load/store`, …) is parsed here
into `RawIR`. This module is explicitly *unverified*: soundness comes from
`validate` (Circe.Validator), which gates every path from `RawIR` to
`CoreIR`/`Emit`. Thin and version-gated per pinned CIR SHA
(see docs/PINS.md).

Phase 4: the parser extracts per-function signatures
(`cir.func @name(...) -> ret` with `llvm.noalias` attrs) and keeps the raw
text for op-presence checks in `validate`. It is deliberately
string-pattern based (no verified MLIR grammar): any parse gap fails
loudly (`none`), and `validate` re-checks every extracted feature before
admitting anything.
-/

/-- One raw parameter: source name (`arg0`), raw CIR type text
    (e.g. `!s32i`, `!cir.ptr<!s32i>`), and whether it carries
    `llvm.noalias` (`__restrict__` evidence in the goldens). -/
structure RawParam where
  name : String
  ctype : String
  noalias : Bool
  deriving DecidableEq, Repr

/-- Raw parsed CIR for one function: signature features + full text
    (for op-presence checks). -/
structure RawFunc where
  name : String
  params : List RawParam
  ret : String
  text : String
  deriving DecidableEq, Repr

/-- Raw parsed CIR module: the functions found in one `.cir` file. -/
structure RawIR where
  funcs : List RawFunc
  deriving DecidableEq, Repr

/-! ## Tiny string utilities (no Mathlib/Batteries in the front end) -/

/-- ASCII whitespace. -/
def isSpaceChar : Char → Bool
  | ' ' => true
  | '\t' => true
  | '\n' => true
  | '\r' => true
  | _ => false

/-- Drop leading whitespace. -/
def dropSpaces : List Char → List Char
  | [] => []
  | c :: cs => if isSpaceChar c then dropSpaces cs else c :: cs

/-- Trim both ends. -/
def trimList (cs : List Char) : List Char :=
  dropSpaces ((dropSpaces cs.reverse).reverse)

/-- List-prefix test. -/
def isPrefixOfList : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, c :: cs => if p == c then isPrefixOfList ps cs else false

/-- Substring test used by `validate` op-presence checks. -/
def containsSubstr (hay needle : String) : Bool :=
  go hay.toList needle.toList
where
  go : List Char → List Char → Bool
    | _, [] => true
    | [], _ :: _ => false
    | h :: hs, n =>
      if isPrefixOfList n (h :: hs) then true else go hs n

/-- First occurrence of `needle` at or after `start` (character index). -/
def findSubstr? (hay needle : String) (start : Nat := 0) : Option Nat :=
  go (hay.toList.drop start) needle.toList start
where
  go : List Char → List Char → Nat → Option Nat
    | _, [], pos => some pos
    | [], _ :: _, _ => none
    | h :: hs, n, pos =>
      if isPrefixOfList n (h :: hs) then some pos
      else go hs n (pos + 1)

/-- Identifier characters in CIR (`%arg0`, `@add`, type aliases). -/
def isIdentChar : Char → Bool
  | c => c.isAlphanum || c == '_' || c == '-' || c == '.'

/-- Take an identifier off the front. -/
def takeIdent : List Char → List Char
  | [] => []
  | c :: cs => if isIdentChar c then c :: takeIdent cs else []

/-- Take a whitespace/`{`-terminated token (return types). -/
def takeToken : List Char → List Char
  | [] => []
  | c :: cs => if isSpaceChar c || c == '{' then [] else c :: takeToken cs

/-- Index of the paren matching the opening paren at the head
    (relative to the head; `none` if unbalanced). -/
def findCloseParen : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | '(' :: cs, d, p => findCloseParen cs (d + 1) (p + 1)
  | ')' :: cs, d, p => if d == 1 then some p else findCloseParen cs (d - 1) (p + 1)
  | _ :: cs, d, p => findCloseParen cs d (p + 1)

/-- Split at top-level commas (nesting `()[]{<>}` protects
    `loc(fused[…])`, `{llvm.noalias, …}`, `!cir.ptr<…>`). -/
def splitTopLevel (s : String) : List String :=
  (go s.toList 0 [] []).map String.ofList
where
  go : List Char → Nat → List Char → List (List Char) → List (List Char)
    | [], _, cur, acc => acc ++ [cur.reverse]
    | ',' :: cs, 0, cur, acc => go cs 0 [] (acc ++ [cur.reverse])
    | c :: cs, d, cur, acc =>
      let d' := match c with
        | '(' | '[' | '{' | '<' => d + 1
        | ')' | ']' | '}' | '>' => d - 1
        | _ => d
      go cs d' (c :: cur) acc

/-! ## Signature extraction -/

/-- Parse one `%argN: TYPE {attrs} loc…` parameter. -/
def parseParam (p : String) : Option RawParam := do
  let cs := trimList p.toList
  let _ ← match cs with
    | '%' :: _ => some ()
    | _ => none
  let nameChars := takeIdent (cs.drop 1)
  if nameChars.isEmpty then none else
  let rest := trimList (cs.drop (1 + nameChars.length))
  let _ ← match rest with
    | ':' :: _ => some ()
    | _ => none
  let afterColon := trimList (rest.drop 1)
  -- The type is the first token (CIR types contain no spaces).
  let typeChars := takeToken afterColon
  if typeChars.isEmpty then none else
  some { name := String.ofList nameChars, ctype := String.ofList typeChars,
         noalias := containsSubstr p "llvm.noalias" }

/-- Parse the `cir.func` signature at/after `off`.
    Returns name, params, return type (`""` for void), and the index just
    past the parameter list (for return-type scanning). -/
def parseSigAt (text : String) (off : Nat) :
    Option (String × List RawParam × String) := do
  let k ← findSubstr? text "cir.func " off
  let atPos ← findSubstr? text "@" (k + 9)
  let afterAt := atPos + 1
  let nameChars := takeIdent (text.toList.drop afterAt)
  if nameChars.isEmpty then none else
  let name := String.ofList nameChars
  let openRel ← findSubstr? text "(" (afterAt + nameChars.length)
  let tail := text.toList.drop openRel
  let closeRel ← findCloseParen tail 0 0
  let paramsText := String.ofList ((text.toList.drop (openRel + 1)).take (closeRel - 1))
  -- Empty parameter list (`int f(void)`) parses to `[]`; otherwise split
  -- at top-level commas (a blank split would fail `parseParam` loudly).
  let params ← if (trimList paramsText.toList).isEmpty then pure []
    else (splitTopLevel paramsText).mapM parseParam
  let after := trimList (text.toList.drop (openRel + closeRel + 1))
  let ret := match after with
    | '-' :: '>' :: rest =>
      String.ofList (takeToken (trimList rest))
    | _ => ""
  some (name, params, ret)

/-- Parse the single function starting at/after `off`. -/
def parseFuncAt (text : String) (off : Nat) : Option RawFunc := do
  let (name, params, ret) ← parseSigAt text off
  some { name, params, ret, text }

/-- Parse the first function in the text. -/
def parseFunc (text : String) : Option RawFunc :=
  parseFuncAt text 0

/-- Parse a whole module (all `cir.func`s). Fuel-bounded; exhaustion is a
    loud `none` (corpus files are small; fuel always suffices). -/
def parseModuleAux : Nat → String → Nat → List RawFunc → Option (List RawFunc)
  | 0, _, _, _ => none
  | fuel + 1, text, off, acc =>
    match findSubstr? text "cir.func " off with
    | none => some acc.reverse
    | some k =>
      match parseFuncAt text k with
      | none => none
      | some f => parseModuleAux fuel text (k + 9) (f :: acc)

/-- Parse a whole `.cir` file into `RawIR`. -/
def parseModule (text : String) : Option RawIR := do
  let funcs ← parseModuleAux (text.toList.length + 1) text 0 []
  some ⟨funcs⟩

/-! ## Type-shape classifiers (for `validate`) -/

/-- Raw pointer type (`!cir.ptr<…>`). -/
def isPtrType (t : String) : Bool :=
  isPrefixOfList "!cir.ptr<".toList t.toList

/-- Pointee of `!cir.ptr<INNER>` (one level). -/
def ptrInner (t : String) : Option String :=
  if isPrefixOfList "!cir.ptr<".toList t.toList then
    match (t.toList.drop 9).reverse with
    | '>' :: restRev => some (String.ofList restRev.reverse)
    | _ => none
  else none

/-- Canonical signed-32 spellings (`!s32i` alias or long form). -/
def isI32 (t : String) : Bool :=
  t == "!s32i" || t == "!cir.int<s, 32>" || t == "!cir.int<s,32>"

/-- Canonical unsigned-32 spellings. -/
def isU32 (t : String) : Bool :=
  t == "!u32i" || t == "!cir.int<u, 32>" || t == "!cir.int<u,32>"

/-- Canonical unsigned-64 spellings (length params). -/
def isU64 (t : String) : Bool :=
  t == "!u64i" || t == "!cir.int<u, 64>" || t == "!cir.int<u,64>"

/-- Length-like integer params (`size_t`/`uint32_t`/`int32_t`). -/
def isLengthType (t : String) : Bool :=
  isU64 t || isU32 t || t == "!s32i"

/-- `!cir.bool`. -/
def isBoolType (t : String) : Bool :=
  t == "!cir.bool"
