import GenExpr.Render

/-!
End-to-end tests: raw text in, Lean source out.

These cover inference and rendering together, since the rendered string is the contract. Every
expected string here has been checked to elaborate against Mathlib and, where it is computable,
to produce the sequence it claims.
-/

namespace GenExprTests.RenderTests

open GenExpr GenExpr.Raw

private def reg : Registry := Builtins.standard

private def cls : Classifier := { functions := reg.names, values := reg.constants }

private def typings (fns names : List String) (want : FnTy) (s : String) : List Typing :=
  let r := { alts := reg.alts ++ fns.toArray.map fun f =>
    { key := f, template := f ++ " {0}", params := #[.nat], result := .nat, prec := 1023,
      argPrec := #[1024] } }
  let c : Classifier := { functions := r.names, values := r.constants }
  match (plan (scan c {} s) { names := names.toArray, arity := want.args.length }).goals[0]? with
  | none => []
  | some g => typeGoal r 4 g want

/-- The cheapest reading, rendered. -/
def lean (names : List String) (want : FnTy) (s : String) : String :=
  match typings [] names want s with
  | [] => "<none>"
  | t :: _ => renderBody {} t

/-- The `n` cheapest readings, rendered. -/
def leanAlts (n : Nat) (names : List String) (want : FnTy) (s : String) : String :=
  String.intercalate " | " ((typings [] names want s).take n |>.map (renderBody {}))

/-- Whether any reading within the first `n` renders to `expected`. -/
def leanHas (n : Nat) (names : List String) (want : FnTy) (s : String) (expected : String) : Bool :=
  ((typings [] names want s).take n).any fun t => renderBody {} t == expected

def leanDef (names : List String) (want : FnTy) (s : String) (nm : String)
    (patched : Array (Array Int × Int) := #[]) : String :=
  match typings [] names want s with
  | [] => "<none>"
  | t :: _ => renderDef {} t nm patched

def N : FnTy := { args := [.nat], ret := .nat }
def NZ : FnTy := { args := [.nat], ret := .int }
def NQ : FnTy := { args := [.nat], ret := .rat }
def NR : FnTy := { args := [.nat], ret := .real }
def R : FnTy := { args := [], ret := .real }
def Nc : FnTy := { args := [], ret := .nat }

/-! ### Truncated subtraction

Over `ℕ`, `3 * n ^ 2 - 7 * n + 6` is wrong at `n = 1`; the reordered form is right everywhere. -/

#guard lean ["a"] N "a(n) = 3n^2 - 7*n + 6" == "3 * n ^ 2 + 6 - 7 * n"
#guard lean ["a"] NZ "a(n) = 3n^2 - 7*n + 6" == "3 * (n : ℤ) ^ 2 - 7 * (n : ℤ) + 6"
#guard lean ["a"] N "a(n) = n/2*3 - 1 + 4 - n" == "n * 3 / 2 + 4 - 1 - n"

/-! ### The numeric tower

Cheap readings come first, and a reading that needs a wider type is offered too — a formula can
typecheck over `ℕ` and still be wrong there. -/

#guard lean ["a"] N "a(n) = 0^n + n" == "0 ^ n + n"
#guard lean ["a"] NZ "a(n) = (-1)^n*n" == "(-1 : ℤ) ^ n * (n : ℤ)"
#guard lean ["a"] N "a(n) = (-1)^n*n" == "((-1 : ℤ) ^ n * (n : ℤ)).toNat"
#guard lean ["a"] N "a(n) = |n-1|" == "n - 1"
#guard leanHas 3 ["a"] N "a(n) = |n-1|" "((n : ℤ) - 1).natAbs"
#guard lean ["a"] NQ "a(n) = 1.5*n" == "1.5 * (n : ℚ)"

-- A084847: over `ℕ` and `ℤ` the closed form is wrong at small `n`, and only the reading with a
-- rational base and an integer exponent reproduces 1, 4, 18, 86, …
#guard lean ["a"] N "a(n) = 2*3^n+(n-2)*2^(2n-1)" == "2 * 3 ^ n + (n - 2) * 2 ^ (2 * n - 1)"
#guard leanHas 6 ["a"] N "a(n) = 2*3^n+(n-2)*2^(2n-1)"
  "⌊2 * 3 ^ n + ((n : ℚ) - 2) * 2 ^ (2 * (n : ℤ) - 1)⌋₊"

/-! ### Alternatives of one name, cheapest first -/

#guard leanAlts 2 ["a"] N "a(n) = 2*n+n/2+n!!"
  == "2 * n + n / 2 + Nat.doubleFactorial n | 2 * n + n / 2 + Nat.factorial (Nat.factorial n)"
#guard lean ["a"] N "a(n) = sqrt(n)" == "Nat.sqrt n"
#guard lean ["a"] N "a(n) = log_2(n)" == "Nat.log 2 n"
#guard lean ["a"] N "a(n) = binomial(n,2)" == "Nat.choose n 2"

/-! ### Aggregators

A big operator's body extends to the right, so one used as an operand is always parenthesised. -/

#guard lean ["a"] N "a(n) = Sum_{k=0..n} k^2" == "∑ k ∈ Finset.range (n + 1), k ^ 2"
#guard lean ["a"] N "a(n) = Sum_{k=1..n} k*2^k + 1"
  == "(∑ k ∈ Finset.Icc 1 n, k * 2 ^ k) + 1"
#guard lean ["a"] N "a(n) = Sum_{d|n} d" == "∑ d ∈ Nat.divisors n, d"
#guard lean ["a"] N "a(n)=sum_(k=0)^n sum_(i=0)^n binomial(k,i)"
  == "∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1), Nat.choose k i"

-- An unbounded sum is reindexed from zero rather than guarded inside the body.
#guard lean ["g"] R "g = sum{k>=1} 1/k^2" == "∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2"
#guard lean ["a"] R "a = integral(x=0)^1 x^2" == "∫ x in (0 : ℝ)..1, x ^ 2"

/-! ### Constants and prose-heavy input -/

#guard lean ["res"] R "res = sin(2*pi)*e" == "Real.sin (2 * Real.pi) * Real.exp 1"
#guard lean [] NQ "another words (1+2*x^4)/((1-x^3)*(1-x-x^2)). - _John Doe_, Dec 29 2012"
  == "(1 + 2 * (x : ℚ) ^ 4) / ((1 - (x : ℚ) ^ 3) * (1 - (x : ℚ) - (x : ℚ) ^ 2))"

/-! ### Auxiliary definitions and recursion -/

#guard lean ["a"] N "b(n) = n^2+1; a(n) = b(b(b(n)))" == "b (b (b n))"
#guard lean ["a"] Nc "a = c^c + c where c=floor(3^10/2^10)" == "c ^ c + c"

-- The body is stored name-free, so it can be re-rendered under any name.
#guard lean ["a"] N "a(n) = a(n-1)+n^2 for n > 1" == "«self» (n - 1) + n ^ 2"
#guard leanDef ["a"] N "a(n) = a(n-1)+n^2" "A000330" #[(#[0], 0), (#[1], 1)]
  == "def A000330 : ℕ → ℕ\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => A000330 (n + 1) + (n + 2) ^ 2"

-- Base cases are keyed by their argument, so data starting at 1 does not shift onto 0; the
-- index below the data gets a junk arm only because structural recursion needs one.
#guard leanDef ["a"] N "a(n) = a(n-1)+n^2" "A000330" #[(#[1], 1)]
  == "def A000330 : ℕ → ℕ\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => A000330 (n + 1) + (n + 2) ^ 2"

-- Without recursion there is nothing to shift, so a patched value is just an earlier arm.
#guard leanDef ["a"] N "a(n) = n - 1" "f" #[(#[0], 7)]
  == "def f : ℕ → ℕ\n  | 0 => 7\n  | n => n - 1"
#guard leanDef ["a"] { args := [.int], ret := .int } "a(n) = n*n" "f" #[(#[-1], 5)]
  == "def f (n : ℤ) : ℤ :=\n  if n = (-1) then 5 else n * n"
#guard leanDef ["a"] N "a(n) = 3n^2 - 7*n + 6" "A000567"
  == "def A000567 (n : ℕ) : ℕ :=\n  3 * n ^ 2 + 6 - 7 * n"
#guard leanDef ["g"] R "g = sum{k>=1} 1/k^2" "zeta2"
  == "noncomputable def zeta2 : ℝ :=\n  ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2"

/-! ### Computability is tracked, since only evaluable readings can be checked against data -/

#guard ((typings [] ["a"] N "a(n) = Sum_{k=0..n} k^2").head!).computable
#guard !((typings [] ["g"] R "g = sum{k>=1} 1/k^2").head!).computable
#guard !((typings [] ["res"] R "res = sin(2*pi)*e").head!).computable

end GenExprTests.RenderTests
