module
public import GenExpr.Frontend.Raw.Parser
public meta import GenExpr.Frontend.Raw.Parser

/-!
Parser tests: precedence, associativity, and the readings offered where the surface syntax is
genuinely ambiguous.

`full` asks for the cheapest parse that covers the whole input, which is what the segmenter picks
when nothing else competes.
-/

namespace GenExprTests.ParserTests
public section

open GenExpr GenExpr.Raw

private def sorted (rs : List Res) : List Res :=
  (rs.toArray.qsort fun a b => a.cost < b.cost).toList

/-- Cheapest reading that consumes every token. -/
def full (fns : List String) (s : String) : String :=
  let (_, toks, rs) := parseAll { functions := fns.toArray } s
  match sorted (rs.filter (·.pos == toks.size)) with
  | r :: _ => r.ast.format
  | [] => "<none>"

/-- All whole-input readings, cheapest first, as `cost:tree`. -/
def fullAlts (fns : List String) (s : String) : String :=
  let (_, toks, rs) := parseAll { functions := fns.toArray } s
  String.intercalate " | "
    ((sorted (rs.filter (·.pos == toks.size))).map fun r => s!"{r.cost}:{r.ast.format}")

/-- Byte span of the cheapest whole-input reading. -/
def fullSpan (fns : List String) (s : String) : String :=
  let (_, toks, rs) := parseAll { functions := fns.toArray } s
  match sorted (rs.filter (·.pos == toks.size)) with
  | r :: _ => toString r.ast.span
  | [] => "<none>"

/-! ### Precedence and associativity -/

#guard full [] "a+b*c" == "(a + (b * c))"
#guard full [] "a*b+c" == "((a * b) + c)"
#guard full [] "a-b-c" == "((a - b) - c)"
#guard full [] "a/b/c" == "((a / b) / c)"
#guard full [] "2^3^2" == "(2 ^ (3 ^ 2))"
#guard full [] "-x^2" == "(-(x ^ 2))"
#guard full [] "-1^n" == "(-(1 ^ n))"
#guard full [] "(-1)^n" == "((-1) ^ n)"
#guard full [] "2^n!" == "(2 ^ (n!))"
#guard full [] "n!^2" == "((n!) ^ 2)"
#guard full [] "n!!" == "(n!!)"

-- `mod` sits at Lean's `%` level, which is what the spec's reading of this line requires.
#guard full [] "3*n + (9*n mod 6 - 6)" == "((3 * n) + (((9 * n) mod 6) - 6))"
#guard full [] "9*n mod 6 - 6" == "(((9 * n) mod 6) - 6)"

/-! ### Implicit multiplication

Only glued tokens multiply, and never two names in a row — that is what keeps prose from parsing. -/

#guard full [] "3n^2" == "(3 * (n ^ 2))"
#guard full [] "2(n+1)" == "(2 * (n + 1))"
#guard full [] "(n+1)(n+2)" == "((n + 1) * (n + 2))"
#guard full [] "1/2n" == "(1 / (2 * n))"
#guard full [] "a b" == "<none>"
#guard full [] "2 for" == "<none>"
#guard full [] "Dec 29 2012" == "<none>"

-- `n` is a parameter of the definition on the left, so `n(n+1)` can only be a product.
#guard full [] "a(n) = n(n+1)/2" == "(a(n) = ((n * (n + 1)) / 2))"
#guard full [] "a(n) = n(1+2+4)" == "(a(n) = (n * ((1 + 2) + 4)))"

-- `2a(n)` splits unless the glued name is in the catalogue.
#guard full ["a"] "2a(n)" == "(2 * a(n))"
#guard full ["a", "2F1"] "2F1(a,b)" == "2F1(a, b)"
#guard full ["a"] "2F1(a,b)" == "(2 * F1(a, b))"

/-! ### Relations

A relation is a proposition, so it never becomes an operand: `a(n) = 0^n + n` has exactly one
whole-input reading. -/

#guard full [] "a(n) = 0^n + n" == "(a(n) = ((0 ^ n) + n))"
#guard fullAlts [] "a(n) = 0^n + n" == "0:(a(n) = ((0 ^ n) + n))"
#guard full [] "a(n) = n^2 = n*n" == "(a(n) = (n ^ 2) = (n * n))"
#guard full [] "n > 1" == "(n > 1)"
#guard full [] "0 <= k" == "(0 <= k)"

/-! ### Calls, subscripts and powers written before the arguments -/

#guard full ["log"] "log_2(n)" == "log(2, n)"
#guard full ["log"] "log_x(2)" == "log(x, 2)"
#guard full ["log"] "log_{10}(n)" == "log(10, n)"
#guard full ["a"] "a_{n-1}" == "a((n - 1))"
#guard full ["T"] "T^2(x)" == "(T(x) ^ 2)"
#guard full ["sin"] "sin^2(x)" == "(sin(x) ^ 2)"
#guard full ["T"] "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2"
  == "(A(x) = (((1 + T(x)) - ((T(x) ^ 2) / 2)) + (T((x ^ 2)) / 2)))"

/-! ### Absolute value versus divides -/

#guard full [] "a(n) = |n-1|" == "(a(n) = |(n - 1)|)"
#guard full [] "|a|*|b|" == "(|a| * |b|)"
#guard full [] "d | n" == "(d | n)"

/-! ### Aggregators

All surface spellings normalise to the same binder record, and the body is a product chain, so a
trailing `+ 1` lands outside the sum. -/

#guard full [] "Sum_{k=0..n} k^2" == "sum{0<=k<=n}((k ^ 2))"
#guard full [] "sum_(k=0)^n k^2" == "sum{0<=k<=n}((k ^ 2))"
#guard full [] "Sum_{k=0}^{n} k^2" == "sum{0<=k<=n}((k ^ 2))"
#guard full [] "Sum_{0<=k<=n} k^2" == "sum{0<=k<=n}((k ^ 2))"
#guard full [] "Sum_{k>=1} 1/k^2" == "sum{k>=1}((1 / (k ^ 2)))"
#guard full [] "sum{k>=1} 1/k^2" == "sum{k>=1}((1 / (k ^ 2)))"
#guard full [] "Sum_{d|n} d" == "sum{d|n}(d)"
#guard full [] "Product_{k=1..n} k" == "prod{1<=k<=n}(k)"
#guard full [] "integral(x=0)^1 x^2" == "int{0<=x<=1}((x ^ 2))"
#guard full [] "Integral_{x=0..1} x^2 dx" == "int{0<=x<=1}((x ^ 2))"
#guard full [] "Sum_{k=0..n} k*2^k + 1" == "(sum{0<=k<=n}((k * (2 ^ k))) + 1)"
#guard full ["A002157"] "a(n)=sum_(k=0)^n sum_(i=0)^n A002157(k,i)"
  == "(a(n) = sum{0<=k<=n}(sum{0<=i<=n}(A002157(k, i))))"

-- A binder shadows the catalogue, so `i` here is a variable rather than the imaginary unit.
#guard full ["i"] "Sum_{i=0..n} i" == "sum{0<=i<=n}(i)"

/-! ### Whole spec corner cases -/

#guard full [] "3n^2 - 7*n + 6" == "(((3 * (n ^ 2)) - (7 * n)) + 6)"
#guard full [] "2*3^n+(n-2)*2^(2n-1)"
  == "((2 * (3 ^ n)) + ((n - 2) * (2 ^ ((2 * n) - 1))))"
#guard full ["sqrt"] "sqrt(6*n*(3*n + (-1)^n - 3)-3*(-1)^n + 5)/sqrt(2)"
  == "(sqrt(((((6 * n) * (((3 * n) + ((-1) ^ n)) - 3)) - (3 * ((-1) ^ n))) + 5)) / sqrt(2))"
#guard full [] "a(n)=2*n+n/2+n!!" == "(a(n) = (((2 * n) + (n / 2)) + (n!!)))"
#guard full ["sin"] "res = sin(2*pi)*e" == "(res = (sin((2 * pi)) * e))"
#guard full [] "a(n) = a(n-1)+n^2" == "(a(n) = (a((n - 1)) + (n ^ 2)))"
#guard full [] "b(n) = n^2+1" == "(b(n) = ((n ^ 2) + 1))"
#guard full [] "a = c^c + c" == "(a = ((c ^ c) + c))"
#guard full [] "(1+2*x^4)/((1-x^3)*(1-x-x^2))"
  == "((1 + (2 * (x ^ 4))) / ((1 - (x ^ 3)) * ((1 - x) - (x ^ 2))))"

/-! ### Spans are byte offsets into the original text -/

#guard fullSpan [] "n+1" == "0..3"
#guard fullSpan [] "(n+1)(n+2)" == "0..10"

end
end GenExprTests.ParserTests
