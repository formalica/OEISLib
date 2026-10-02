import GenExpr.Frontend.Raw.Segmenter

/-!
Segmenter tests: which stretches of a line are formulas, and why the rest is not.
-/

namespace GenExprTests.SegmenterTests

open GenExpr GenExpr.Raw

private def mk (fns vals : List String) : Classifier :=
  { functions := fns.toArray, values := vals.toArray }

/-- The chosen fragments, as their exact source text. -/
def frags (fns vals : List String) (s : String) : String :=
  String.intercalate " | " ((scan (mk fns vals) {} s).chosen.toList.map (·.text))

/-- The chosen fragments as parse trees. -/
def trees (fns vals : List String) (s : String) : String :=
  String.intercalate " | "
    ((scan (mk fns vals) {} s).chosen.toList.map fun g =>
      match g.best? with
      | some r => r.ast.format
      | none => "<none>")

/-- Byte spans of the chosen fragments. -/
def spans (fns vals : List String) (s : String) : String :=
  String.intercalate " | " ((scan (mk fns vals) {} s).chosen.toList.map fun g => toString g.span)

/-- Why the widest candidate covering the whole input was rejected, if it was. -/
def wholeReason (fns vals : List String) (s : String) : String :=
  let sc := scan (mk fns vals) {} s
  match sc.all.filter (fun g => g.startTok == 0 && g.stopTok == sc.toks.size) |>.toList with
  | g :: _ => String.intercalate ", " (g.reasons.map Reject.describe)
  | [] => "<no candidate>"

/-! ### Formulas buried in prose

The generating function is found without any prose handling: `words (1+2*x^4)` parses perfectly
well as a call, but it introduces a second unbound name and so scores zero. -/

#guard frags [] [] "another words (1+2*x^4)/((1-x^3)*(1-x-x^2)). - _John Doe_, Dec 29 2012"
  == "(1+2*x^4)/((1-x^3)*(1-x-x^2))"
#guard spans [] [] "another words (1+2*x^4)/((1-x^3)*(1-x-x^2)). - _John Doe_, Dec 29 2012"
  == "14..43"
#guard wholeReason [] [] "words (1+2*x^4)" == "too many free variables: [words, x]"

#guard frags [] [] "a(n) = 3n^2 - 7*n + 6. - _Jane Roe_, Jul 24 2016"
  == "a(n) = 3n^2 - 7*n + 6"
#guard frags [] [] "From _Mitch Harris_, Jul 24 2016: (Start)" == ""
#guard frags [] [] "(End)" == ""

/-! ### One line, several formulas -/

#guard frags ["A046080", "A046109", "a"] []
    "A046080(a(n)) = 1, A046109(a(n)) = 12. - Jean-Christophe Hervé, Dec 01 2013"
  == "A046080(a(n)) = 1 | A046109(a(n)) = 12"

-- `Jean-Christophe` is a well-formed subtraction of two names; it is dropped for having no
-- ground content and two unbound names, not by any list of words.
#guard wholeReason [] [] "Jean-Christophe"
  == "too many free variables: [Jean, Christophe], unsupported: no ground content"

#guard frags [] [] "b(n) = n^2+1; a(n) = b(b(b(n)))" == "b(n) = n^2+1 | a(n) = b(b(b(n)))"
#guard trees [] [] "b(n) = n^2+1; a(n) = b(b(b(n)))"
  == "(b(n) = ((n ^ 2) + 1)) | (a(n) = b(b(b(n))))"

#guard frags ["floor"] [] "a = c^c + c where c=floor(3^10/2^10)"
  == "a = c^c + c | c=floor(3^10/2^10)"

-- The guard is a fragment in its own right, so the verifier can find it later.
#guard frags [] [] "a(n) = a(n-1)+n^2 for n > 1" == "a(n) = a(n-1)+n^2 | n > 1"

/-! ### Unfillable holes reject the whole line

`T` is used as a call head and resolves to nothing, so no reading of the line survives — which is
the reported outcome when the catalogue does not supply it. -/

#guard wholeReason [] [] "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2" == "unresolved name 'T'"
#guard trees ["T"] [] "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2"
  == "(A(x) = (((1 + T(x)) - ((T(x) ^ 2) / 2)) + (T((x ^ 2)) / 2)))"

-- `n` also appears as an operand (`n+1`), so `n(n+1)` is a product, not a call to a hole.
#guard trees [] [] "2 | n(n+1)" == "(2 | (n * (n + 1)))"
#guard trees [] [] "n(n+1)/2" == "((n * (n + 1)) / 2)"

/-! ### Fragments that state nothing

A lone name, and equally a bare call, are not formulas. -/

#guard frags [] [] "Dec 29 2012" == ""
#guard frags ["a"] [] "a(n)" == ""
#guard frags ["sin"] ["pi", "e"] "res = sin(2*pi)*e" == "res = sin(2*pi)*e"

/-! ### Spans are byte offsets, so multi-byte prose does not shift them -/

#guard spans [] [] "Hervé: n^2+1" == "8..13"
#guard frags [] [] "Hervé: n^2+1" == "n^2+1"

end GenExprTests.SegmenterTests
