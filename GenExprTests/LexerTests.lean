module
public import GenExpr.Lexer
public meta import GenExpr.Lexer

/-!
Lexer tests.

These are `#guard`s, so a regression fails `lake build` rather than only `lake exe genexpr-test`.
-/

namespace GenExprTests.LexerTests
public section

open GenExpr

/-- Compact rendering of a token stream, used as the golden form in every check below. -/
def toks (s : String) : String :=
  String.intercalate " " ((Lexer.run s).2.toList.map toString)

/-- Same, but marking tokens that are glued to what precedes them. -/
def glued (s : String) : String :=
  String.join
    ((Lexer.run s).2.toList.map fun t => (if t.spaceBefore then " " else "·") ++ toString t)

/-- Byte span of the `i`-th token, as `start..stop`. -/
def spanOf (s : String) (i : Nat) : String :=
  let (inp, ts) := Lexer.run s
  let t := ts[i]!
  toString (inp.span t.start t.stop)

/-! ### Numbers, identifiers and glued alphanumerics -/

#guard toks "123" == "num:123"
#guard toks "1.25" == "dec:1.25"
#guard toks "A000045" == "ident:A000045"

-- A `.` is a decimal point only when a digit follows immediately; otherwise it is junk,
-- which is what stops an expression at the end of a sentence.
#guard toks "x^2. Then" == "ident:x op:^ num:2 junk:. ident:Then"
#guard toks "6." == "num:6 junk:."

-- Digits glued to letters split here and are rejoined (or not) by the parser.
#guard toks "3n^2" == "num:3 ident:n op:^ num:2"
#guard toks "2F1" == "num:2 ident:F1"

/-! ### Whitespace sensitivity

`2n` is a product but `2 for` must not be: the only difference is `spaceBefore`. -/

#guard glued "2n" == "·num:2·ident:n"
#guard glued "2 for" == "·num:2 ident:for"
#guard glued "n(n+1)" == "·ident:n·(:(·ident:n·op:+·num:1·):)"
#guard glued "words (1+x)" == "·ident:words (:(·num:1·op:+·ident:x·):)"

/-! ### Operators -/

#guard toks "a<=b" == "ident:a op:<= ident:b"
#guard toks "a>=b" == "ident:a op:>= ident:b"
#guard toks "a<>b" == "ident:a op:<> ident:b"
#guard toks "a!=b" == "ident:a op:!= ident:b"
#guard toks "n!!" == "ident:n op:! op:!"
#guard toks "k=0..n" == "ident:k op:= num:0 op:.. ident:n"
#guard toks "log_2" == "ident:log op:_ num:2"
#guard toks "|n-1|" == "op:| ident:n op:- num:1 op:|"
#guard toks "9*n mod 6" == "num:9 op:* ident:n ident:mod num:6"

/-! ### Junk

Every non-ASCII character is junk, and adjacent junk collapses into one token so that a run of
punctuation is a single barrier. -/

#guard toks "a ≤ b" == "ident:a junk:≤ ident:b"
#guard toks "Hervé" == "ident:Herv junk:é"
#guard toks "a(n) = 1, b" == "ident:a (:( ident:n ):) op:= num:1 ,:, ident:b"
#guard toks "x: y" == "ident:x junk:: ident:y"
#guard toks "a ?! b" == "ident:a junk:? op:! ident:b"

/-! ### Spans are byte offsets, so multi-byte prose before a formula does not shift them -/

#guard spanOf "é + 1" 1 == "3..4"
#guard spanOf "é + 1" 2 == "5..6"
#guard (Lexer.run "é + 1").1.extract 2 5 == "+ 1"

end
end GenExprTests.LexerTests
