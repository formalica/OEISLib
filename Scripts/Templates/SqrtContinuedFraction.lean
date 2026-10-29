import Scripts.OeisTemplate.Recognize
import OEISLib.Common.SqrtContinuedFraction

/-!
# Template `sqrtContinuedFraction`

> Numerators of continued fraction convergents to sqrt(d).

~967 sequences, `d` a non-square. The shared math is `OEISLib.Common.SqrtContinuedFraction`,
whose `relation_nonsquare` / `relation_iff_eq_computed` tie the computable `computed d n` to
Mathlib's `GenContFract`.

* `maindef` (computable) `fun n => computed d n`
* `maindef` (prop)       `fun n p => relation d n p`, equivalent to `p = «main» n` for non-squares
* `mathematica`          `Numerator[Convergents[Sqrt[d],K]]`, `Convergents[…]//Numerator` and
                         `Table[Numerator[FromContinuedFraction[ContinuedFraction[Sqrt[d],n]]],{n,1,K}]`,
                         each with an optional leading `Join[{1}, …]`
-/

namespace Oeis.Template.SqrtContinuedFraction

open Recognize

private abbrev lib : String := "OEISLib.Common.SqrtContinuedFraction"

/-! ## 1. Title -/

/-- A non-square radicand from the exact title family. -/
def parseTitle (title : String) : Option Nat := do
  let titleStart := "numerators of continued fraction convergents to sqrt("
  let text := title.toLower
  guard (text.startsWith titleStart && text.endsWith ").")
  let d ← ((text.drop titleStart.length).toString.dropEnd 2).toString.toNat?
  guard (Nat.sqrt d * Nat.sqrt d != d)
  return d

/-- The two surveyed titles whose sequence carries a leading `1` not produced by the library. -/
def prependsOne (name : String) (d : Nat) : Bool :=
  (name == "A001077" && d == 5) || (name == "A005667" && d == 10)

/-! ## 2. Recognition

Only whole reconstructed expressions match; a resource cap bounds the numeric evaluation, it is
not a mathematical restriction. -/

inductive Flavor where
  | direct | postfix | table
  deriving DecidableEq, Repr

def Flavor.label : Flavor → String
  | .direct => "direct"
  | .postfix => "postfix"
  | .table => "table"

/-- The source expression for the given parameters. -/
def reconstruct (d count : Nat) (flavor : Flavor) (prependOne : Bool) : String :=
  let body := match flavor with
    | .direct => s!"Numerator[Convergents[Sqrt[{d}],{count}]]"
    | .postfix => s!"Convergents[Sqrt[{d}],{count}]//Numerator"
    | .table => "Table[Numerator[FromContinuedFraction[ContinuedFraction[Sqrt[" ++
        s!"{d}],n]]]," ++ "{n,1," ++ toString count ++ "}]"
  if prependOne then "Join[{1}," ++ body ++ "]" else body

private def wordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Tokenizes without merging identifiers or numbers separated by whitespace; returns the tokens
and the end position of the last token. A single complete trailing `(* … *)` comment is
allowed, executable suffixes are rejected. -/
private def lex (text : String) : Option (List String × Nat) := Id.run do
  let chars := text.toList.toArray
  let mut tokens : List String := []
  let mut i := 0
  let mut endPos := 0
  while i < chars.size do
    let c := chars[i]!
    if c.isWhitespace then
      i := i + 1
      continue
    if c == '(' && chars[i + 1]? == some '*' then
      let tail := String.ofList (chars.toList.drop (i + 2))
      match tail.splitOn "*)" with
      | [comment, rest] =>
        if rest.trimAscii.toString.isEmpty && (comment.splitOn "(*").length == 1 then
          return some (tokens.reverse, endPos)
        else return none
      | _ => return none
    if wordChar c then
      let start := i
      i := i + 1
      while i < chars.size && wordChar chars[i]! do i := i + 1
      tokens := String.ofList ((chars.toList.drop start).take (i - start)) :: tokens
    else if "[],{}/".contains c then
      tokens := String.singleton c :: tokens
      i := i + 1
    else return none
    endPos := i
  return some (tokens.reverse, endPos)

structure Snippet where
  flavor : Flavor
  count : Nat
  prependOne : Bool
  /-- End position of the expression inside the line (a trailing comment is excluded). -/
  endPos : Nat

/-- Recognizes a whole line as one of the supported shapes. -/
def recognizeLine (d : Nat) (content : String) : Option Snippet := do
  let (tokens, endPos) ← lex content
  let counts := (tokens.filterMap String.toNat?).eraseDups
  for count in counts do
    if count == 0 || count > 10000 then continue
    for flavor in [Flavor.direct, .postfix, .table] do
      for prependOne in [false, true] do
        let (expected, _) ← lex (reconstruct d count flavor prependOne)
        if tokens == expected then
          return ⟨flavor, count, prependOne, endPos⟩
  none

/-- One flavor key: every distinct expression is its own snippet (`byText`). -/
def sections (d : Nat) : List (String × List LineRecognizer) :=
  [("mathematica", [("wolfram-sqrt-cf", fun t => (recognizeLine d t).map (·.endPos))])]

/-! ## 3. Candidates -/

private def paramsJson (d : Nat) (extra : String := "") : String :=
  s!"\{\"d\":{d}{extra}}"

private def mainTerm (d : Nat) (prependOne : Bool) : String :=
  if prependOne then s!"fun n => if n = 0 then 1 else {lib}.computed {d} (n - 1)"
  else s!"fun n => {lib}.computed {d} n"

def mainDefinition (d : Nat) (title : String) (prependOne : Bool) (verified : Nat) : Candidate where
  language := Section.maindef
  originalText := title
  argKind := "Nat"
  leanType := "Nat → Nat"
  leanCode := mainTerm d prependOne
  imports := #[lib]
  verifiedUpto := verified
  params := paramsJson d s!",\"prependOne\":{prependOne}"

/-- The defining relation through Mathlib's continued fractions. -/
def mainRelation (d : Nat) (title : String) (prependOne : Bool) (verified : Nat) : Candidate :=
  let nonsquare := s!"have nonsquare : Nat.sqrt {d} * Nat.sqrt {d} ≠ {d} := by decide +kernel\n"
  let proof :=
    if prependOne then
      "intro n p\n" ++ nonsquare ++
      "by_cases h : n = 0\n" ++
      "· simp [«self», «main», h]\n" ++
      "· simp only [«self», «main», h, ite_false]\n" ++
      s!"  exact {lib}.relation_iff_eq_computed {d} nonsquare _ p"
    else
      "intro n p\n" ++ nonsquare ++
      s!"exact {lib}.relation_iff_eq_computed {d} nonsquare n p"
  { mainDefinition d title prependOne verified with
    leanKind := .prop
    leanType := "Nat → Nat → Prop"
    leanCode :=
      if prependOne then s!"fun n p => if n = 0 then p = 1 else {lib}.relation {d} (n - 1) p"
      else s!"fun n p => {lib}.relation {d} n p"
    eqStatement := "∀ (n p : Nat), «self» n p ↔ p = «main» n"
    eqProof := proof }

/-- The Wolfram program as a list, equal to the main definition position by position. -/
def snippet (d : Nat) (h : Hit) (s : Snippet) (verified : Nat) : Candidate :=
  let proof :=
    if s.prependOne then
      "intro i h\n" ++
      s!"have hi : i < {s.count} + 1 := by\n" ++
      s!"  simpa [«self», {lib}.program_length] using h\n" ++
      s!"simpa [«self», «main»] using {lib}.program_prepend_getElem? {d} {s.count} i hi"
    else
      "intro i h\n" ++
      s!"have hi : i < {s.count} := by\n" ++
      s!"  simpa [«self», {lib}.program_length] using h\n" ++
      s!"exact {lib}.program_getElem? {d} {s.count} i hi"
  { language := h.language
    blockIndex := h.blockIndex
    originalText := h.text
    argKind := "Nat"
    leanType := "List Nat"
    leanCode := s!"{lib}.program {d} {s.count} {s.prependOne}"
    imports := #[lib]
    eqStatement := "∀ (i : Nat) (h : i < «self».length), «self»[i]? = some («main» i)"
    eqProof := proof
    verifiedUpto := verified
    params := paramsJson d s!",\"count\":{s.count},\"prependOne\":{s.prependOne}"
    notes := s.flavor.label }

/-! ## 4. The template -/

/-- A snippet counts only if its leading-one convention matches the sequence's and all
published terms it overlaps agree; returns the number of terms compared. -/
private def overlap (d : Nat) (s : Snippet) (terms : Array Nat) : Option Nat :=
  let values := (OEISLib.Common.SqrtContinuedFraction.program d s.count s.prependOne).toArray
  (checkPrefix values terms).toOption

def formalize (_extras : List String) (src : SeqSource) : Verdict :=
  match parseTitle src.title with
  | none => .skip "title or non-square radicand unsupported"
  | some d =>
    if src.offset != 0 then .skip "unsupported offset"
    else match termsNat src.terms with
      | .error e => .fail e
      | .ok terms =>
        if terms.isEmpty then .fail "sequence has no known terms"
        else
          let prepend := prependsOne src.name d
          let values := (OEISLib.Common.SqrtContinuedFraction.program d terms.size prepend).toArray
          if values.size < terms.size then .fail "library produced fewer values than published"
          else match checkPrefix values terms with
            | .error e => .fail e
            | .ok verified =>
              let found := (sections d).foldl (init := (#[] : Array Hit)) fun acc (lang, recs) =>
                acc ++ hits src lang recs (byText := true)
              let snippets := found.filterMap fun h => do
                let s ← recognizeLine d h.text
                guard (s.prependOne == prepend)
                let n ← overlap d s terms
                return snippet d h s n
              .items (#[mainDefinition d src.title prepend verified,
                        mainRelation d src.title prepend verified] ++ snippets)

def template : Template where
  name := "sqrtContinuedFraction"
  descr := "sqrt convergent numerators (~967 sequences; %t Numerator/Convergents programs)"
  selectWhere := "lower(title) LIKE 'numerators of continued fraction convergents to sqrt(%'"
  formalize := formalize

end Oeis.Template.SqrtContinuedFraction
