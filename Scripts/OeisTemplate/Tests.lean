module
public import Scripts.OeisTemplate.Recognize
public meta import Scripts.OeisTemplate.Recognize
public import Scripts.OeisIngest.Json
public meta import Scripts.OeisIngest.Json
public import Scripts.OeisIngest.Parse
public meta import Scripts.OeisIngest.Parse

/-! `#guard` tests for the pure parts of the template infrastructure; a failure breaks `lake build`. -/

namespace Oeis.Template.Tests
public section

open Recognize

private def src : SeqSource where
  name := "A000001"
  title := "Number of groups of order n."
  offset := 0
  terms := #["1", "1"]
  formulaLines := #["a(n) = n + 1.", "b(n) = 2*n", "c(n) =", "  3*n"]
  commentLines := #["First comment"]
  programs := #[{ language := "pari", blockIndex := 0, text := "a(n)=n+1\nb(n)=2", hash := "h" }]

private def cand (language text : String) (blockIndex : Nat := 0) : Source :=
  { language, blockIndex, originalText := text }

private def spanOf (s : Source) : Option (Nat × Nat) :=
  (locate src s).toOption.map fun p => (p.start, p.stop)

/-! ### `locate`: the original-text check -/

-- title (maindef), program and comment sections
#guard spanOf (cand "maindef" "groups of order") == some (10, 25)
#guard spanOf (cand "pari" "b(n)=2") == some (9, 15)
#guard spanOf (cand "comment" "comment") == some (6, 13)
-- the %F section is the lines joined with `\n`: a formula may span lines
#guard spanOf (cand "formula" "b(n) = 2*n") == some (14, 24)
#guard spanOf (cand "formula" "c(n) =\n  3*n") == some (25, 37)
-- ... but the text must be quoted exactly: re-joining with a space is not original text
#guard spanOf (cand "formula" "c(n) = 3*n") == none
-- other rejections: absent text, wrong section, missing block, empty text, unknown section
#guard spanOf (cand "formula" "a(n) = n + 2.") == none
#guard spanOf (cand "comment" "b(n) = 2*n") == none
#guard spanOf (cand "pari" "a(n)=n+1" 3) == none
#guard spanOf (cand "maindef" "   ") == none
#guard spanOf (cand "magma" "a") == none
-- the source hash of a program section is the stored `program.hash`
#guard (locate src (cand "pari" "a(n)=n+1")).toOption.map (·.sourceHash) == some "h"

-- a position hint selects the occurrence; a hint that does not point at the text is refused
#guard spanOf { cand "pari" "n" with start? := some 2 } == some (2, 3)
#guard spanOf { cand "pari" "n" with start? := some 0 } == none

/-! ### Sources of one item: canonical order and identity -/

private def placed (s : Source) : Placed :=
  (locate src s).toOption.get!

private def order (ss : List Source) : List String :=
  (canonical (ss.map placed).toArray).toList.map (·.src.originalText)

-- title, formulas, comments, programs; whatever order the template lists them in
#guard order [cand "pari" "b(n)=2", cand "comment" "comment", cand "formula" "b(n) = 2*n",
    cand "maindef" "groups of order"] == ["groups of order", "b(n) = 2*n", "comment", "b(n)=2"]
-- two sources at the same place are one source
#guard (order [cand "pari" "b(n)=2", cand "pari" "b(n)=2"]).length == 1
-- the identity of an item is the hash of its texts joined with a newline
#guard itemHash #[placed (cand "pari" "b(n)=2")] == formulaHash "b(n)=2"
#guard itemHash (canonical #[placed (cand "pari" "b(n)=2"), placed (cand "formula" "b(n) = 2*n")])
    == formulaHash "b(n) = 2*n\nb(n)=2"

#guard findSub? (chars "abcabc") (chars "ca") == some 2
#guard findSub? (chars "abc") (chars "abcd") == none
#guard findSub? (chars "abc") #[] == none

/-! ### `codeEnd`: credits and comments are not part of the formula -/

#guard codeEnd "G.f.: 1/(1-x). - _Name Here_, Dec 29 2012" == 14
#guard codeEnd "Series[x] (* _Joe_, Aug 04 2012 *)" == 9
#guard codeEnd "a - _b" == 6
#guard codeEnd "x^2 - _Joe_ is not a date" == 25
#guard codeEnd "plain text  " == 10

/-! ### `hitsInText` -/

private def whole (want : String) : List LineRecognizer :=
  [("w", fun t => if t == want then some t.length else none)]

#guard (hitsInText "formula" 0 "a\nb" (whole "a\nb")).size == 0
#guard (hitsInText "formula" 0 "a\nb" (whole "a\nb") (maxLines := 2)).map (·.text) == #["a\nb"]
-- a flavor yields one hit unless `byText` asks for every distinct text
#guard (hitsInText "formula" 0 "x\nx\ny" [("f", fun t => some t.length)]).size == 1
#guard (hitsInText "formula" 0 "x\nx\ny" [("f", fun t => some t.length)] (byText := true)).size == 2
-- a hit remembers where its line starts in the section text
#guard (hitsInText "formula" 0 "ab\ncd" [("f", fun t => if t == "cd" then some 2 else none)]).map
  (·.start) == #[3]

#guard endAfterSemicolon (chars "foo ; // x") 3 == 5
#guard endAfterSemicolon (chars "foo // x") 3 == 3

/-! ### JSON arrays stored in the database -/

#guard Json.parseArray (Json.strArray #["a\"b", "c\\d\ne", "ü"]) == some #["a\"b", "c\\d\ne", "ü"]
#guard Json.parseArray "[]" == some #[]
#guard Json.parseArray (Json.termArray #["1", "-2", "x"]) == some #["1", "-2", "x"]
#guard Json.parseArray "[\"a\"" == none

end
end Oeis.Template.Tests
