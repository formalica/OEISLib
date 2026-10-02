import GenExpr.Api

/-!
Verification tests: raw text plus known values in, a checked Lean definition out.

Every accepted declaration here has been compiled against Mathlib and evaluated to confirm it
produces the listed values.
-/

namespace GenExprTests.VerifyTests

open GenExpr

private def N : FnTy := { args := [.nat], ret := .nat }

/-- Points indexed from zero, as a sequence's first terms. -/
private def seq (vs : List Int) : Array (Array Int × Int) :=
  vs.toArray.mapIdx fun i v => (#[(i : Int)], v)

private def req (s : String) (vs : List Int) (allowed : Nat := 0)
    (types : Array FnTy := #[N]) : Request :=
  { input := s, names := #["a"], types, values := seq vs
    verify := { engine := .internal, allowedFailures := allowed } }

/-- The declaration of the first accepted reading. -/
def decl (s : String) (vs : List Int) (allowed : Nat := 0) (types : Array FnTy := #[N]) : String :=
  match (analyze (req s vs allowed types)).items[0]? with
  | some i => i.decl
  | none => "<none>"

/-- The body of the first accepted reading. -/
def body (s : String) (vs : List Int) (allowed : Nat := 0) : String :=
  match (analyze (req s vs allowed)).items[0]? with
  | some i => i.body
  | none => "<none>"

/-- Per-point outcome: `.` verified, `b` supplied as a base case, `X` wrong, `t` timed out. -/
def trace (s : String) (vs : List Int) (allowed : Nat := 0) : String :=
  match (analyze (req s vs allowed)).items[0]? with
  | some i => i.report.trace
  | none => "<none>"

def why (s : String) (vs : List Int) (allowed : Nat := 0) (types : Array FnTy := #[N]) : String :=
  let r := analyze (req s vs allowed types)
  match r.items[0]?, r.rejected[0]? with
  | some _, _ => "<accepted>"
  | none, some (_, e) => e.describe
  | none, none => "<nothing>"

/-! ### The cheapest reading that survives the data is the one returned

Each of these needs the ones before it to fail first. -/

#guard body "a(n) = 3n^2 - 7*n + 6" [6, 2, 4, 12, 26, 46] == "3 * n ^ 2 + 6 - 7 * n"
#guard body "a(n) = 0^n + n" [1, 1, 2, 3, 4, 5] == "0 ^ n + n"

-- The `ℕ` reading `n - 1` is wrong at `n = 0`, so the integer one wins.
#guard body "a(n) = |n-1|" [1, 0, 1, 2, 3, 4] == "((n : ℤ) - 1).natAbs"

-- A084847: `ℕ` and `ℤ` both typecheck and both disagree with the data; only a rational base with
-- an integer exponent reproduces it.
#guard body "a(n) = 2*3^n+(n-2)*2^(2n-1)" [1, 4, 18, 86, 418, 2022]
  == "⌊2 * 3 ^ n + ((n : ℚ) - 2) * 2 ^ (2 * (n : ℤ) - 1)⌋₊"

#guard body "a(n) = Sum_{k=0..n} k^2" [0, 1, 5, 14, 30, 55]
  == "∑ k ∈ Finset.range (n + 1), k ^ 2"
#guard body "b(n) = n^2+1; a(n) = b(b(b(n)))" [5, 26, 677] == "b (b (b n))"

/-! ### Recursion

A recursive body cannot produce its own base cases, so evaluating one diverges until it is
supplied. `for n > 1` says how many to supply; otherwise the caller must allow them. -/

#guard decl "a(n) = a(n-1)+n^2 for n > 1" [0, 1, 5, 14, 30, 55]
  == "def a : ℕ → ℕ\n  | 0 => 0\n  | n + 1 => a n + (n + 1) ^ 2"
#guard trace "a(n) = a(n-1)+n^2 for n > 1" [0, 1, 5, 14, 30, 55] == "b....."

#guard decl "a(n) = a(n-1)+n^2" [0, 1, 5, 14, 30, 55] == "<none>"
#guard decl "a(n) = a(n-1)+n^2" [0, 1, 5, 14, 30, 55] 1
  == "def a : ℕ → ℕ\n  | 0 => 0\n  | n + 1 => a n + (n + 1) ^ 2"

#guard decl "a(n) = a(n-1)+a(n-2)" [0, 1, 1, 2, 3, 5, 8, 13, 21] 2
  == "def a : ℕ → ℕ\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => a (n + 1) + a n"

/-! ### Failures are only forgivable as a prefix -/

#guard why "a(n) = n*n" [0, 1, 4, 99, 16] 3 == "value mismatch at point 3: expected 99, got 9"
#guard trace "a(n) = n*n" [0, 1, 4, 9, 16] == "....."

/-! ### Not everything can be checked

A reading that cannot be run is still returned, flagged and unverified; it is up to the caller
whether to keep it. A computable reading that fails is never replaced by an unrunnable one. -/

private def first (s : String) (vs : List Int) (types : Array FnTy) : Option Item :=
  (analyze (req s vs 0 types)).items[0]?

#guard (first "a = sum{k>=1} 1/k^2" [1] #[{ args := [], ret := .real }]).map
    (fun i => (i.computable, i.report.accepted, i.report.reason.map Reject.describe))
  == some (false, false, some "not computable, cannot be checked against data")
#guard (first "a = sum{k>=1} 1/k^2" [1] #[{ args := [], ret := .real }]).map (·.decl)
  == some "noncomputable def a : ℝ :=\n  ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2"
#guard decl "a(n) = n*n" [0, 1, 4, 99, 16] == "<none>"

/-! ### Reported spans cover exactly the parts used -/

#guard (analyze (req "a(n) = 3n^2 - 7*n + 6. - _Jane Roe_, Jul 24 2016" [6, 2, 4, 12, 26, 46]))
    |>.items[0]!.text == "a(n) = 3n^2 - 7*n + 6"
#guard (analyze (req "a(n) = a(n-1)+n^2 for n > 1" [0, 1, 5, 14, 30, 55])).items[0]!.text
  == "a(n) = a(n-1)+n^2 … n > 1"

/-! ### Auxiliary definitions come out with the item -/

#guard (analyze (req "b(n) = n^2+1; a(n) = b(b(b(n)))" [5, 26, 677])).items[0]!.aux
  == #["def b (n : ℕ) : ℕ :=\n  n ^ 2 + 1"]

/-! ### Functions known only by their values

A call inside the table is evidence; one outside it proves nothing, so those points are neither
passes nor failures. -/

private def withTable (s : String) (vs : List Int) (tbl : Array (Array Int × Int)) : Request :=
  { input := s, names := #["a"], types := #[N], values := seq vs
    tables := #[("F", tbl)], verify := { engine := .internal } }

#guard (analyze (withTable "a(n) = F(n)+1" [1, 2, 3, 5]
    #[(#[0], 0), (#[1], 1), (#[2], 2), (#[3], 4)])).items[0]!.body == "F n + 1"
#guard (analyze (withTable "a(n) = F(n)+1" [1, 2, 3, 5]
    #[(#[0], 0), (#[1], 1), (#[2], 2)])).items[0]!.report.trace == "...?"

/-! ### The recursion ladder

The cheapest form the shape allows: pattern arms for a `ℕ` argument, even when the call is not
structural, since Lean finds that termination argument itself; `termination_by` for a `ℤ`
argument; fuel for nested recursion, which Lean cannot see terminate at all. Every declaration
here was elaborated and evaluated by the Lean engine. -/

private def seqFrom (start : Int) (vs : List Int) : Array (Array Int × Int) :=
  vs.toArray.mapIdx fun i v => (#[(i : Int) + start], v)

private def declOf (r : Request) : String :=
  match (analyze r).items[0]? with
  | some i => i.decl
  | none => "<none>"

#guard declOf { input := "a(n) = a(floor(n/2)) + n mod 2", names := #["a"]
                values := seqFrom 0 [0, 1, 1, 2, 1, 2, 2, 3, 1]
                verify := { engine := .internal, allowedFailures := 1 } }
  == "def a : ℕ → ℕ\n  | 0 => 0\n  | n + 1 => a ((n + 1) / 2) + (n + 1) % 2"

#guard declOf { input := "a(n) = a(n-1) + 2*n", names := #["a"]
                types := #[{ args := [.int], ret := .int }], values := seqFrom (-1) [0, 0, 2, 6, 12]
                verify := { engine := .internal, allowedFailures := 1 } }
  == "def a (n : ℤ) : ℤ :=\n  if n < 0 then if n = (-1) then 0 else 0 else a (n - 1) + 2 * n\n" ++
     "termination_by (n - (-1)).toNat\ndecreasing_by all_goals omega"

-- Hofstadter's Q: each call's argument contains another call.
#guard declOf { input := "a(n) = a(n-a(n-1)) + a(n-a(n-2)) for n > 2", names := #["a"]
                values := seqFrom 1 [1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 6, 8]
                verify := { engine := .internal } }
  == "def a (n : ℕ) : ℕ :=\n  go (2 * n + 2) n\nwhere\n  go : ℕ → ℕ → ℕ\n    | 0, _ => 0\n" ++
     "    | fuel + 1, n => if n = 1 then 1 else if n = 2 then 1 else " ++
     "go fuel (n - go fuel (n - 1)) + go fuel (n - go fuel (n - 2))"

/-! ### Statements

A relation becomes a `∀` over its free variables, its guards become hypotheses, and it is decided
at every data index. Each statement in the input is its own result. -/

private def P1 : FnTy := { args := [.nat], ret := .prop }

private def stmts (input : String) (n : Nat)
    (tables : Array (String × Array (Array Int × Int)) := #[]) : Array String :=
  (analyze { input, types := #[P1], tables, values := seqFrom 0 (List.replicate n 0)
             verify := { engine := .internal } }).items.map (·.body)

#guard stmts "A046080(a(n)) = 1, A046109(a(n)) = 12. - Jean-Christophe Hervé, Dec 01 2013" 3
    #[("a", seqFrom 0 [5, 13, 17]), ("A046080", #[(#[5], 1), (#[13], 1), (#[17], 1)]),
      ("A046109", #[(#[5], 12), (#[13], 12), (#[17], 12)])]
  == #["∀ n : ℕ, A046080 (a n) = 1", "∀ n : ℕ, A046109 (a n) = 12"]

#guard stmts "n^2 > 2n for n > 2" 7 == #["∀ n : ℕ, n > 2 → n ^ 2 > 2 * n"]
#guard stmts "2 | n(n+1)" 5 == #["∀ n : ℕ, 2 ∣ n * (n + 1)"]

-- An equality chain repeats its smallest member, or lists big members once.
#guard stmts "a(n) = n^2 = n*n" 3 #[("a", seqFrom 0 [0, 1, 4])]
  == #["∀ n : ℕ, a n = n ^ 2 ∧ a n = n * n"]
#guard stmts "(n+1)^2 = n^2+2n+1 = (n+1)*(n+1)" 4
  == #["∀ n : ℕ, List.Pairwise (· = ·) [(n + 1) ^ 2, n ^ 2 + 2 * n + 1, (n + 1) * (n + 1)]"]

-- False at n = 2, so no statement survives; and without the function `a` there is nothing to state.
#guard stmts "2^n > n^2" 6 == #[]
#guard stmts "a(n) = n^2 = n*n" 3 == #[]

#guard (analyze { input := "n^2 > 2n for n > 2", types := #[P1], values := seqFrom 0 [0, 0, 0]
                  verify := { engine := .internal } }).items[0]!.decl
  == "theorem statement : ∀ n : ℕ, n > 2 → n ^ 2 > 2 * n := by\n  sorry"

end GenExprTests.VerifyTests
