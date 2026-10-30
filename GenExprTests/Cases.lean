module
public import GenExpr.Api
public meta import GenExpr.Api
public import GenExprTests
public meta import GenExprTests

/-!
The acceptance corpus: every "important corner case" and "multiplication corner case" from the
specification, as data.

Kept separate from the `#guard` suites so the runner can report coverage in one table.
-/

namespace GenExprTests.Cases
public section

open GenExpr

def N : FnTy := { args := [.nat], ret := .nat }
def NQ : FnTy := { args := [.nat], ret := .rat }
def NR : FnTy := { args := [.nat], ret := .real }
def R : FnTy := { args := [], ret := .real }
def Nc : FnTy := { args := [], ret := .nat }
def ZZ : FnTy := { args := [.int], ret := .int }
def P1 : FnTy := { args := [.nat], ret := .prop }

/-- One entry of the corpus. `expect` is the body the parser should settle on, or `none` when the
line must be rejected. -/
structure Case where
  name : String
  input : String
  names : Array String := #["a"]
  types : Array FnTy := #[N]
  values : List Int := []
  /-- Index of the first value. -/
  start : Nat := 0
  allowed : Nat := 0
  custom : Array Alt := #[]
  removeBuiltins : Array String := #[]
  tables : Array (String × Array (Array Int × Int)) := #[]
  expect : Option String
  expectDecl : Option String := none
  /-- Every result's body, in order, when the line holds several formulas. -/
  expectAll : Option (Array String) := none
  /-- Some rejection reason must contain this. -/
  expectReason : Option String := none
  /-- Only meaningful when values are checked by Lean. -/
  leanOnly : Bool := false

private def table1 (rows : List (Int × Int)) : Array (Array Int × Int) :=
  rows.toArray.map fun (a, v) => (#[a], v)

/-- A catalogue entry whose Lean rendering deliberately means something else than its key: the
interpreter evaluates `sqrt`, the emitted code computes `Nat.log 2`. Only an engine that runs the
emitted code can notice. -/
private def driftingSqrt : Alt :=
  { key := "sqrt", template := "Nat.log 2 {0}", params := #[.nat], result := .nat, prec := 1023
    argPrec := #[1024], imports := #["Mathlib.Data.Nat.Log"] }

def corpus : Array Case := #[
  { name := "01 generating function in prose"
    input := "another words (1+2*x^4)/((1-x^3)*(1-x-x^2)). - _John Doe_, Dec 29 2012"
    names := #[], types := #[NQ]
    expect := some "(1 + 2 * (x : ℚ) ^ 4) / ((1 - (x : ℚ) ^ 3) * (1 - (x : ℚ) - (x : ℚ) ^ 2))" },
  { name := "02 0^0 = 1"
    input := "a(n) = 0^n + n", values := [1, 1, 2, 3, 4, 5]
    expect := some "0 ^ n + n" },
  { name := "03 nested sums"
    input := "a(n)=sum_(k=0)^n sum_(i=0)^n T(k,i)"
    tables := #[("T", #[(#[0, 0], 1), (#[1, 0], 1), (#[1, 1], 1)])]
    expect := some "∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), T k i" },
  { name := "04 unbounded sum"
    input := "g = sum{k>=1} 1/k^2", names := #["g"], types := #[R]
    expect := some "∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2" },
  { name := "05 recursion with a stated domain"
    input := "a(n) = a(n-1)+n^2 for n > 1", values := [0, 1, 5, 14, 30, 55]
    expect := some "«self» (n - 1) + n ^ 2"
    expectDecl := some "def a : ℕ → ℕ\n  | 0 => 0\n  | n + 1 => a n + (n + 1) ^ 2" },
  { name := "06 division and double factorial"
    input := "a(n)=2*n+n/2+n!!"
    expect := some "2 * n + n / 2 + Nat.doubleFactorial n" },
  { name := "07 integral"
    input := "a = integral(x=0)^1 x^2", types := #[R]
    expect := some "∫ x in (0 : ℝ)..1, x ^ 2" },
  { name := "08 truncated subtraction"
    input := "a(n) = 3n^2 - 7*n + 6", values := [6, 2, 4, 12, 26, 46]
    expect := some "3 * n ^ 2 + 6 - 7 * n" },
  { name := "09 A084847, rational intermediates"
    input := "a(n) = 2*3^n+(n-2)*2^(2n-1)", values := [1, 4, 18, 86, 418, 2022]
    expect := some "⌊2 * 3 ^ n + ((n : ℚ) - 2) * 2 ^ (2 * (n : ℤ) - 1)⌋₊" },
  { name := "10 mod precedence"
    input := "a(n) = 3*n + (9*n mod 6 - 6)"
    expect := some "3 * n + (9 * n % 6 - 6)" },
  { name := "11 nested sqrt precedence"
    input := "a(n) = sqrt(6*n*(3*n + (-1)^n - 3)-3*(-1)^n + 5)/sqrt(2)", types := #[NR]
    expect := some
      ("(Int.sqrt (6 * (n : ℤ) * (3 * (n : ℤ) + (-1 : ℤ) ^ n - 3) - 3 * (-1 : ℤ) ^ n + 5) : ℝ)" ++
        " / (Nat.sqrt 2 : ℝ)") },
  { name := "12 constants"
    input := "res = sin(2*pi)*e", names := #["res"], types := #[R]
    expect := some "Real.sin (2 * Real.pi) * Real.exp 1" },
  { name := "13a power written before the arguments"
    input := "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2", names := #["A"]
    tables := #[("T", table1 [(0, 0), (1, 1), (2, 1)])]
    -- `T^2(x)` is `(T x)^2`; over ℕ the subtraction is moved past the additions.
    expect := some "1 + T x + T (x ^ 2) / 2 - T x ^ 2 / 2" },
  { name := "13b the same line without T is unparsable"
    input := "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2", names := #["A"]
    expect := none },
  { name := "15 subscript is the first argument"
    input := "a(n) = log_2(n)"
    expect := some "Nat.log 2 n" },
  { name := "16 a binder shadows the catalogue"
    input := "a(n) = Sum_{i=0..n} i"
    expect := some "∑ i ∈ Finset.range (n + 1), i" },
  { name := "17 absolute value"
    input := "a(n) = |n-1|", values := [1, 0, 1, 2, 3, 4]
    expect := some "((n : ℤ) - 1).natAbs" },
  { name := "18 auxiliary function"
    input := "b(n) = n^2+1; a(n) = b(b(b(n)))", values := [5, 26, 677]
    expect := some "b (b (b n))" },
  { name := "19 auxiliary constant"
    input := "a = c^c + c where c=floor(3^10/2^10)", types := #[Nc]
    expect := some "c ^ c + c" },
  { name := "20a implicit multiplication"
    input := "a(n) = n(n+1)/2", values := [0, 1, 3, 6, 10]
    expect := some "n * (n + 1) / 2" },
  { name := "20b glued factor"
    input := "a(n) = 2(n+1)", values := [2, 4, 6, 8]
    expect := some "2 * (n + 1)" },
  { name := "20c adjacent parentheses"
    input := "a(n) = (n+1)(n+2)", values := [2, 6, 12, 20]
    expect := some "(n + 1) * (n + 2)" },
  { name := "20d two names never multiply"
    input := "a(n) = n b", expect := some "n" },
  { name := "21 recursion whose data starts at 1"
    input := "a(n) = a(n-1)+n^2 for n > 1", values := [1, 5, 14, 30, 55], start := 1
    expect := some "«self» (n - 1) + n ^ 2"
    -- The base case is keyed by its argument; index 0 is outside the data and gets a junk arm.
    expectDecl := some "def a : ℕ → ℕ\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => a (n + 1) + (n + 2) ^ 2" },
  { name := "22 Fibonacci, two base cases"
    input := "a(n) = a(n-1)+a(n-2)", values := [0, 1, 1, 2, 3, 5, 8, 13, 21], allowed := 2
    expect := some "«self» (n - 1) + «self» (n - 2)"
    expectDecl := some "def a : ℕ → ℕ\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => a (n + 1) + a n" },
  { name := "23 data-only function"
    input := "a(n) = F(n)+1", values := [1, 2, 3, 5]
    tables := #[("F", table1 [(0, 0), (1, 1), (2, 2), (3, 4)])]
    expect := some "F n + 1" },
  { name := "24 emitted code that drifts from the interpreter is caught"
    input := "a(n) = sqrt(n)", values := [0, 1, 1, 1, 2, 2, 2, 2, 2, 3]
    removeBuiltins := #["sqrt"], custom := #[driftingSqrt]
    expect := none, expectReason := some "point 1", leanOnly := true },
  { name := "25 a slow evaluation times out without failing the formula"
    -- Exponential in Lean, which does not memoise: late points time out, which lowers the
    -- success rate but is not evidence against the formula.
    input := "a(n) = a(n-1)+a(n-2)", allowed := 2
    values := [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181,
      6765, 10946, 17711, 28657, 46368, 75025, 121393, 196418, 317811, 514229, 832040, 1346269,
      2178309, 3524578, 5702887, 9227465, 14930352, 24157817, 39088169, 63245986]
    expect := some "«self» (n - 1) + «self» (n - 2)" },
  { name := "26 non-structural recursion, pattern form"
    input := "a(n) = a(floor(n/2)) + n mod 2", values := [0, 1, 1, 2, 1, 2, 2, 3, 1], allowed := 1
    expect := some "«self» (n / 2) + n % 2"
    expectDecl := some "def a : ℕ → ℕ\n  | 0 => 0\n  | n + 1 => a ((n + 1) / 2) + (n + 1) % 2" },
  { name := "27 integer argument, well-founded form"
    input := "a(n) = a(n-1) + 2*n", types := #[ZZ], values := [0, 2, 6, 12, 20], start := 0
    allowed := 1
    expect := some "«self» (n - 1) + 2 * n"
    expectDecl := some ("def a (n : ℤ) : ℤ :=\n  if n < 1 then if n = 0 then 0 else 0 " ++
      "else a (n - 1) + 2 * n\ntermination_by n.toNat\ndecreasing_by all_goals omega") },
  { name := "28 nested recursion, fuel form"
    input := "a(n) = a(n-a(n-1)) + a(n-a(n-2)) for n > 2", start := 1
    values := [1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 6, 8]
    expect := some "«self» (n - «self» (n - 1)) + «self» (n - «self» (n - 2))"
    expectDecl := some ("def a (n : ℕ) : ℕ :=\n  go (2 * n + 2) n\nwhere\n  go : ℕ → ℕ → ℕ\n" ++
      "    | 0, _ => 0\n    | fuel + 1, n => if n = 1 then 1 else if n = 2 then 1 else " ++
      "go fuel (n - go fuel (n - 1)) + go fuel (n - go fuel (n - 2))") },
  { name := "14 two statements in one line"
    input := "A046080(a(n)) = 1, A046109(a(n)) = 12. - Jean-Christophe Hervé, Dec 01 2013"
    names := #[], types := #[P1], values := [0, 0, 0]
    tables := #[("a", table1 [(0, 5), (1, 13), (2, 17)]),
      ("A046080", table1 [(5, 1), (13, 1), (17, 1)]),
      ("A046109", table1 [(5, 12), (13, 12), (17, 12)])]
    expect := some "∀ n : ℕ, A046080 (a n) = 1"
    expectAll := some #["∀ n : ℕ, A046080 (a n) = 1", "∀ n : ℕ, A046109 (a n) = 12"] },
  { name := "29 statement under a stated domain"
    input := "n^2 > 2n for n > 2", names := #[], types := #[P1], values := [0, 0, 0, 0, 0, 0]
    expect := some "∀ n : ℕ, n > 2 → n ^ 2 > 2 * n"
    expectDecl := some "theorem statement : ∀ n : ℕ, n > 2 → n ^ 2 > 2 * n := by\n  sorry" },
  { name := "30 equality chain repeats its smallest member"
    input := "a(n) = n^2 = n*n", names := #[], types := #[P1], values := [0, 0, 0]
    tables := #[("a", table1 [(0, 0), (1, 1), (2, 4)])]
    expect := some "∀ n : ℕ, a n = n ^ 2 ∧ a n = n * n" },
  { name := "31 a false statement is rejected"
    input := "2^n > n^2", names := #[], types := #[P1], values := [0, 0, 0, 0, 0, 0]
    expect := none, expectReason := some "point 2" }
]

def request (c : Case) (engine : Engine) : Request :=
  { input := c.input, names := c.names, types := c.types, custom := c.custom
    removeBuiltins := c.removeBuiltins, tables := c.tables
    values := c.values.toArray.mapIdx fun i v => (#[((i + c.start : Nat) : Int)], v)
    verify := { engine, allowedFailures := c.allowed } }

def judge (c : Case) (r : GenExpr.Result) : GenExprTests.Result := Id.run do
  let got := (r.items[0]?.map (·.body))
  let mut out := check c.name c.expect got
  if let some d := c.expectDecl then
    out := out ++ check (c.name ++ " (decl)") (some d) (r.items[0]?.map (·.decl))
  if let some all := c.expectAll then
    out := out ++ check (c.name ++ " (all)") all (r.items.map (·.body))
  if let some needle := c.expectReason then
    let reasons := r.rejected.toList.map fun (_, rj) => rj.describe
    out := out ++ checkTrue (c.name ++ " (reason)")
      (reasons.any fun s => (s.splitOn needle).length > 1)
      s!"no reason mentions '{needle}': {reasons}"
  return out

/-- Run one case with the interpreter only. -/
def runCase (c : Case) : GenExprTests.Result := judge c (analyze (request c .internal))

/-- Run one case with the given engine, Lean included. -/
def runCaseWith (s : LeanEngine.Session) (engine : Engine) (c : Case) : IO GenExprTests.Result :=
  return judge c (← run s (request c engine))

end
end GenExprTests.Cases
