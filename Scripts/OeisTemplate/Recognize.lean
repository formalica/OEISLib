module
public import Scripts.OeisTemplate.Base
public meta import Scripts.OeisTemplate.Base

/-!
Shared toolkit for template authors: whitespace-tolerant matching over a character array,
splitting a section into recognizable lines, and comparing computed values with the data.
-/

namespace Oeis.Template.Recognize
public section

def chars (s : String) : Array Char := s.toList.toArray

def slice (a : Array Char) (i j : Nat) : String := String.ofList (a.extract i j).toList

/-! ### Cursor over a character array -/

partial def skipWs (a : Array Char) (i : Nat) : Nat :=
  match a[i]? with
  | some c => if c.isWhitespace then skipWs a (i + 1) else i
  | none => i

private partial def eatChars (a : Array Char) (i : Nat) : List Char → Option Nat
  | [] => some i
  | c :: rest =>
    let i := skipWs a i
    if c.isWhitespace then eatChars a i rest
    else if a[i]? == some c then eatChars a (i + 1) rest
    else none

/-- Matches `lit` character by character, ignoring any whitespace in the text before each
character; returns the position just after the match. -/
def eatLit (a : Array Char) (i : Nat) (lit : String) : Option Nat :=
  eatChars a i lit.toList

private partial def digitsGo (a : Array Char) (i acc : Nat) : Nat × Nat :=
  match a[i]? with
  | some c => if c.isDigit then digitsGo a (i + 1) (acc * 10 + (c.toNat - '0'.toNat)) else (acc, i)
  | none => (acc, i)

/-- A natural number literal after optional whitespace: `(value, position after)`. -/
def digitsFrom (a : Array Char) (i : Nat) : Option (Nat × Nat) :=
  let i := skipWs a i
  match a[i]? with
  | some c => if c.isDigit then some (digitsGo a (i + 1) (c.toNat - '0'.toNat)) else none
  | none => none

/-- End of a recognized statement that stops at `i`: includes one directly following `;`, but
never a trailing comment or credit. -/
def endAfterSemicolon (a : Array Char) (i : Nat) : Nat :=
  let j := skipWs a i
  if a[j]? == some ';' then j + 1 else i

/-! ### Finding snippets in sections -/

/-- After the closing `_` of an author name: `, Dec 29 2012`. -/
private def isDateTail (a : Array Char) (i stop : Nat) : Bool :=
  let rest := slice a i stop
  rest.startsWith "," && rest.length ≤ 24 && rest.any Char.isDigit

/-- End position of the code of a line: before a trailing OEIS author credit
` - _Name_, Dec 29 2012` or a trailing `(* … *)` comment, which are not part of the formula. -/
def codeEnd (line : String) : Nat := Id.run do
  let a := chars line
  let mut stop := a.size
  -- trailing `(* … *)`
  let trimmed := line.trimAsciiEnd.toString
  if trimmed.endsWith "*)" then
    let b := chars trimmed
    for i' in [0:b.size] do
      let i := b.size - 1 - i'
      if b[i]? == some '(' && b[i + 1]? == some '*' then
        stop := i
        break
  -- trailing ` - _Name_, date`
  for i in [0:stop] do
    if slice a i (i + 4) == " - _" then
      if let some k := (a.extract (i + 4) stop).toList.findIdx? (· == '_') then
        if isDateTail a (i + 4 + k + 1) stop then
          stop := i
          break
  -- trailing whitespace
  while stop > 0 && (a[stop - 1]?).any Char.isWhitespace do
    stop := stop - 1
  return stop

/-! ### Snippet hits -/

/-- A recognized snippet: `text` is a verbatim slice of the line it came from. -/
structure Hit where
  language : String
  blockIndex : Nat
  flavor : String
  text : String

/-- A line recognizer returns the end position of the code it recognizes at the line start. -/
abbrev LineRecognizer := String × (String → Option Nat)

/-- Applies the recognizers to the lines of one section text; first hit per flavor wins (with
`byText`, every distinct snippet text wins instead, for families whose flavor does not
determine the snippet). With `maxLines > 1` it also tries runs of 2..`maxLines` consecutive
lines (joined with `\n`), but only after all single lines were tried, so a formula that fits on
one line is never widened. -/
def hitsInText (language : String) (blockIndex : Nat) (text : String)
    (recognizers : List LineRecognizer) (seen : Array String := #[]) (maxLines : Nat := 1)
    (byText : Bool := false) : Array Hit := Id.run do
  let mut out : Array Hit := #[]
  let mut keys := seen
  let lines := (text.splitOn "\n").toArray
  for width in [1:maxLines + 1] do
    for i in [0:lines.size] do
      if i + width > lines.size then break
      let run := "\n".intercalate (lines.extract i (i + width)).toList
      for (flavor, recog) in recognizers do
        if !byText && keys.contains flavor then continue
        if let some stop := recog run then
          let hit := (run.take stop).toString
          let key := if byText then hit else flavor
          unless hit.trimAscii.isEmpty || keys.contains key do
            out := out.push { language, blockIndex, flavor, text := hit }
            keys := keys.push key
  return out

/-- `hitsInText` over every block of a program language, or over the `formula` / `comment`
section. -/
def hits (src : SeqSource) (language : String) (recognizers : List LineRecognizer)
    (seen : Array String := #[]) (maxLines : Nat := 1) (byText : Bool := false) :
    Array Hit := Id.run do
  let mut out : Array Hit := #[]
  let mut keys := seen
  let sections : Array (Nat × String) :=
    if language == Section.formula then #[(0, src.formulaText)]
    else if language == Section.comment then #[(0, src.commentText)]
    else (src.blocksOf language).map fun p => (p.blockIndex, p.text)
  for (blockIndex, text) in sections do
    let found := hitsInText language blockIndex text recognizers keys maxLines byText
    out := out ++ found
    keys := keys ++ found.map fun h => if byText then h.text else h.flavor
  return out

/-! ### Values -/

/-- The published terms as natural numbers. -/
def termsNat (terms : Array String) : Except String (Array Nat) :=
  terms.mapM fun t => match t.toNat? with
    | some v => .ok v
    | none => .error s!"term '{t}' is not a natural number"

/-- Compares computed values with the published ones term by term from the offset; returns how
many terms were compared. -/
def checkPrefix (computed expected : Array Nat) : Except String Nat := do
  let n := min computed.size expected.size
  if n == 0 then throw "no values to compare"
  for i in [0:n] do
    unless computed[i]! == expected[i]! do
      throw s!"value mismatch at term #{i} (counting from the offset): computed \
        {computed[i]!}, OEIS data says {expected[i]!}"
  return n

end
end Oeis.Template.Recognize
