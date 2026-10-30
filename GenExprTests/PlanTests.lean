module
public import GenExpr.Plan
public meta import GenExpr.Plan

/-!
Planner tests: which definition becomes the goal, what it depends on, and what is rejected.
-/

namespace GenExprTests.PlanTests
public section

open GenExpr GenExpr.Raw

private def run (fns names : List String) (arity : Nat) (s : String) : PlanResult :=
  plan (scan { functions := fns.toArray } {} s) { names := names.toArray, arity }

private def showDef (d : Definition) : String :=
  s!"{d.name}({String.intercalate "," d.params.toList}) := {d.body.format}"

/-- The best goal, with its auxiliary definitions and guards. -/
def goal (fns names : List String) (arity : Nat) (s : String) : String :=
  match (run fns names arity s).goals[0]? with
  | none => "<none>"
  | some g =>
    let aux := if g.aux.isEmpty then ""
      else " | aux " ++ String.intercalate "; " (g.aux.toList.map showDef)
    let gs := if g.guards.isEmpty then ""
      else " | guard " ++ String.intercalate "; " (g.guards.toList.map fun x =>
        s!"{x.var} {x.op} {x.bound}")
    let loop := if g.main.recursive then " | recursive" else ""
    showDef g.main ++ aux ++ gs ++ loop

/-- All goals, best first. -/
def goals (fns names : List String) (arity : Nat) (s : String) : String :=
  String.intercalate " || " ((run fns names arity s).goals.toList.map fun g => showDef g.main)

/-- Byte ranges the best goal is built from. -/
def spans (fns names : List String) (arity : Nat) (s : String) : String :=
  match (run fns names arity s).goals[0]? with
  | none => "<none>"
  | some g => String.intercalate " " (g.spans.toList.map toString)

def rejects (fns names : List String) (arity : Nat) (s : String) : String :=
  String.intercalate "; "
    ((run fns names arity s).rejected.toList.map fun (_, r) => r.describe).eraseDups

def points (fns names : List String) (arity : Nat) (s : String) : String :=
  String.intercalate "; " ((run fns names arity s).pointValues.toList.map fun (n, args, v) =>
    s!"{n}{args.toList} = {v.format}")

/-! ### Auxiliary definitions

The goal is the requested name even when another definition is written first, and the definition
it needs comes along in dependency order. -/

#guard goal [] ["a"] 1 "b(n) = n^2+1; a(n) = b(b(b(n)))"
  == "a(n) := b(b(b(n))) | aux b(n) := ((n ^ 2) + 1)"
#guard spans [] ["a"] 1 "b(n) = n^2+1; a(n) = b(b(b(n)))" == "0..12 14..31"

#guard goal ["floor"] ["a"] 0 "a = c^c + c where c=floor(3^10/2^10)"
  == "a() := ((c ^ c) + c) | aux c() := floor(((3 ^ 10) / (2 ^ 10)))"

-- Only what the goal actually uses is pulled in.
#guard goal [] ["a"] 1 "b(n) = n+1; d(n) = n*9; a(n) = b(n)"
  == "a(n) := b(n) | aux b(n) := (n + 1)"

/-! ### Guards and recursion -/

#guard goal [] ["a"] 1 "a(n) = a(n-1)+n^2 for n > 1"
  == "a(n) := (a((n - 1)) + (n ^ 2)) | guard n > 1 | recursive"
#guard spans [] ["a"] 1 "a(n) = a(n-1)+n^2 for n > 1" == "0..17 22..27"

-- A guard on a variable the goal does not bind is not attached to it.
#guard goal [] ["a"] 1 "a(n) = n+1 for k > 3" == "a(n) := (n + 1)"

/-! ### Equality chains give one goal per right-hand side, in source order -/

#guard goals [] ["a"] 1 "a(n) = n^2 = n*n" == "a(n) := (n ^ 2) || a(n) := (n * n)"

/-! ### Anonymous expressions

A formula with no equation becomes a function of the single name it leaves unbound. -/

#guard goal [] [] 1 "x*(x-1)" == "f(x) := (x * (x - 1))"
#guard goal [] ["a"] 1 "x*(x-1)" == "a(x) := (x * (x - 1))"
#guard goal [] [] 2 "x*(x-1)" == "<none>"

/-! ### Values stated in the text are recorded, not turned into definitions -/

#guard goal [] ["a"] 1 "a(0)=1, a(1)=2, a(n)=a(n-1)+a(n-2)"
  == "a(n) := (a((n - 1)) + a((n - 2))) | recursive"
#guard points [] ["a"] 1 "a(0)=1, a(1)=2, a(n)=a(n-1)+a(n-2)" == "a[0] = 1; a[1] = 2"

/-! ### Rejections carry a reason -/

#guard rejects [] ["a"] 1 "a(n) = b(n); b(n) = a(n)+1"
  == "mutual recursion between [a, b]; mutual recursion between [b, a]"
#guard rejects [] ["A"] 1 "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2" == "unresolved name 'T'"
#guard goal [] ["A"] 1 "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2" == "<none>"
#guard goal ["T"] ["A"] 1 "A(x) = 1 + T(x) - T^2(x)/2 + T(x^2)/2"
  == "A(x) := (((1 + T(x)) - ((T(x) ^ 2) / 2)) + (T((x ^ 2)) / 2))"

-- A line that sets out to define `a` and fails yields nothing, rather than a stray sub-expression
-- of it renamed to `a`.
#guard goal [] ["a"] 1 "a(n) = c(n)+1" == "<none>"
#guard rejects [] ["a"] 1 "a(n) = c(n)+1" == "unresolved name 'c'"

end
end GenExprTests.PlanTests
