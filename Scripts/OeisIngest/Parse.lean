module
public import Scripts.OeisIngest.Json

/-!
Parser for the OEIS "internal format" `.seq` files shipped in `oeisdata/seq`.

Every line has the shape `%<tag> <A-number> <content>`. The tags used here:

* `%S`/`%T`/`%U` the terms of the sequence (comma separated, wrapped over lines)
* `%N` name / title of the sequence
* `%O` offset (`<offset>,<index of first term with absolute value > 1>`)
* `%K` keywords
* `%F` formulas
* `%C` comments
* `%p` Maple programs, `%t` Mathematica programs, `%o` other-language programs
-/

namespace Oeis
public section

private def trimStr (s : String) : String := s.trimAscii.toString
private def trimEndStr (s : String) : String := s.trimAsciiEnd.toString

/-- One program block attached to a sequence, e.g. a `%p` Maple snippet. -/
public structure Program where
  /-- `maple`, `mathematica`, or the lowercased `(Lang)` marker of a `%o` block. -/
  language : String
  /-- Originating record tag: `p`, `t`, or `o`. -/
  sourceTag : String
  /-- Position of this block among the blocks of the same language. -/
  blockIndex : Nat
  /-- Raw text, newline separated, exactly as it appears in the `.seq` file. -/
  text : String
  deriving Inhabited

/-- Everything the ingest step extracts from a single `.seq` file. -/
public structure Entry where
  name : String
  title : String
  offset : Int
  /-- Second component of the `%O` line: index of the first term of absolute value > 1. -/
  offsetFirstBig : Option Int
  keywords : Array String
  terms : Array String
  formulas : Array String
  /-- `%C` lines, in file order, tag stripped. -/
  comments : Array String
  programs : Array Program
  sourceFile : String
  deriving Inhabited

/-- Splits `%<tag> <A-number> <content>` into `("%<tag>", "<A-number>", "<content>")`. -/
def parseRecordLine (line : String) : Option (String × String × String) :=
  match line.splitOn " " with
  | tag :: anum :: rest =>
    if tag.length == 2 && tag.startsWith "%" then
      some (tag, anum, trimStr (String.intercalate " " rest))
    else
      none
  | _ => none

private def splitCommas (s : String) : Array String :=
  (s.splitOn ",").foldl (init := #[]) fun acc t =>
    let t := trimStr t
    if t.isEmpty then acc else acc.push t

/-- `%o` blocks start with a `(Lang)` marker; returns the lowercased language name. -/
private def parseLangMarker (line : String) : Option String :=
  let l := trimStr line
  if !l.startsWith "(" then none
  else
    match (l.drop 1).toString.splitOn ")" with
    | lang :: _ =>
      let lang := (trimStr lang).toLower
      -- `(PARI) ...` yes, `(x-1)*(x+1)` no.
      if lang.isEmpty || lang.length > 20 then none
      else if lang.any (fun c => !(c.isAlphanum || c == ' ' || c == '/' || c == '_' ||
          c == '-' || c == '.' || c == '+' || c == '#')) then none
      else some lang
    | _ => none

/-- Groups the collected lines of one record tag into separate program blocks.

`%p`/`%t` are never split further — a Maple/Mathematica block often merges several
programs (main definition, `# Alternative:` variant, driver lines, ...) and the
formalization pipeline's LLM step is responsible for splitting those itself, from the
raw block exactly as OEIS wrote it. Only `%o` splits, at each `(Lang)` marker, since
those really are different languages concatenated in one tag run. -/
private def buildPrograms (sourceTag : String) (defaultLang : String)
    (lines : Array String) : Array Program := Id.run do
  let useMarkers := sourceTag == "o"
  let mut out : Array Program := #[]
  let mut cur : Array String := #[]
  let mut lang := defaultLang
  -- Block counts stay per language; there are only a handful of blocks per sequence.
  let flush := fun (out : Array Program) (lang : String) (cur : Array String) =>
    let text := trimStr (String.intercalate "\n" cur.toList)
    if text.isEmpty then out
    else
      let idx := out.foldl (init := 0) fun n p => if p.language == lang then n + 1 else n
      out.push { language := lang, sourceTag, blockIndex := idx, text }
  for line in lines do
    let marker := if useMarkers then parseLangMarker line else none
    if let some newLang := marker then
      out := flush out lang cur
      cur := #[]; lang := newLang
      let rest := trimStr (String.intercalate ")" ((line.trimAscii.toString.splitOn ")").drop 1))
      if !rest.isEmpty then cur := cur.push rest
    else
      cur := cur.push line
  return flush out lang cur

/-- Parses the contents of one `.seq` file. Returns `none` if it holds no OEIS records. -/
def parseSeqFile (sourceFile : String) (fallbackName : String) (contents : String) :
    Option Entry := Id.run do
  let mut name := ""
  let mut title := ""
  let mut offsetLine := ""
  let mut keywords : Array String := #[]
  let mut sTerms := ""
  let mut tTerms := ""
  let mut uTerms := ""
  let mut formulas : Array String := #[]
  let mut comments : Array String := #[]
  let mut mapleLines : Array String := #[]
  let mut mmaLines : Array String := #[]
  let mut otherLines : Array String := #[]
  let mut sawAny := false
  for rawLine in contents.splitOn "\n" do
    match parseRecordLine (trimEndStr rawLine) with
    | none => pure ()
    | some (tag, anum, content) =>
      sawAny := true
      if name.isEmpty then name := anum
      match tag with
      | "%N" => if title.isEmpty then title := content
      | "%O" => if offsetLine.isEmpty then offsetLine := content
      | "%K" => keywords := keywords ++ splitCommas content
      | "%S" => sTerms := sTerms ++ content
      | "%T" => tTerms := tTerms ++ content
      | "%U" => uTerms := uTerms ++ content
      | "%F" => if !content.isEmpty then formulas := formulas.push content
      | "%C" => if !content.isEmpty then comments := comments.push content
      | "%p" => mapleLines := mapleLines.push content
      | "%t" => mmaLines := mmaLines.push content
      | "%o" => otherLines := otherLines.push content
      | _ => pure ()
  if !sawAny then
    return none
  let offsetParts := splitCommas offsetLine
  let offset := (offsetParts[0]?.bind String.toInt?).getD 0
  let offsetFirstBig := offsetParts[1]?.bind String.toInt?
  -- `%S`/`%T` lines usually already end with a comma; joining with one more and
  -- dropping empty tokens handles both conventions.
  let terms := splitCommas (String.intercalate "," [sTerms, tTerms, uTerms])
  let programs :=
    buildPrograms "p" "maple" mapleLines ++
    buildPrograms "t" "mathematica" mmaLines ++
    buildPrograms "o" "unknown" otherLines
  return some {
    name := if name.isEmpty then fallbackName else name
    title, offset, offsetFirstBig, keywords, terms, formulas, comments, programs, sourceFile
  }

/-- Stable identifier of a formula: hex encoding of `String.hash` of its text. -/
public def formulaHash (text : String) : String :=
  Json.toHex (String.hash text).toNat 16

end
end Oeis
