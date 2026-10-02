import GenExpr.Ast

/-!
The catalogue of Lean terms a surface name can stand for.

Every callable thing — arithmetic operators, library functions, constants, user-supplied
functions, auxiliary definitions found in the text, and the goal itself when it recurses — is a
list of `Alt`s. One mechanism then covers typing, rendering, imports and computability.

The one distinction that matters is `transparent`:

* **transparent** alternatives are the arithmetic operators. They are usable only when their
  result type is exactly the context type, and their result is never cast. This is what keeps
  `(n - 2) * 2^(2n-1)` at `ℚ` from becoming `↑(n - 2 : ℕ) * …` — the subtraction is elaborated
  *at* `ℚ` and the cast lands on the leaf `n` instead;
* **opaque** alternatives are everything else. They are usable when their result type is at most
  the context type, and the cast is placed on their result.

Casts therefore only ever appear on leaves and on opaque results, which is what keeps the search
space small and the output readable.
-/

namespace GenExpr

/-- One Lean term a surface name can denote, with everything needed to type and print it. -/
structure Alt where
  /-- Surface name: `sqrt`, `+`, `^`, `A000045`. -/
  key : String
  /-- Rendering template with `{0}`, `{1}` … placeholders. -/
  template : String
  params : Array Ty
  result : Ty
  /-- Arithmetic operator: usable only at its exact result type, never cast. -/
  transparent : Bool := false
  /-- Whether the term can be evaluated, as opposed to merely elaborated. -/
  computable : Bool := true
  imports : Array String := #[]
  opens : Array String := #[]
  /-- Precedence of the rendered form. -/
  prec : Nat := 1024
  /-- Precedence context for each argument. -/
  argPrec : Array Nat := #[]
  /-- Tie-breaker between alternatives with the same types. -/
  bias : Nat := 0
deriving Inhabited, Repr, BEq

namespace Alt

def arity (a : Alt) : Nat := a.params.size

/-- Cheaper alternatives are tried first: lower in the numeric tower, evaluable, less exotic. -/
def cost (a : Alt) : Nat :=
  a.result.level + (if a.computable then 0 else 4) + a.bias

end Alt

structure Registry where
  alts : Array Alt := #[]
deriving Inhabited

namespace Registry

def find (r : Registry) (key : String) (arity : Nat) : Array Alt :=
  r.alts.filter fun a => a.key == key && a.arity == arity

def names (r : Registry) : Array String :=
  r.alts.foldl (fun acc a => if acc.contains a.key then acc else acc.push a.key) #[]

/-- Names usable without arguments, such as `pi` and `e`. -/
def constants (r : Registry) : Array String :=
  r.alts.foldl (fun acc a => if a.arity == 0 && !acc.contains a.key then acc.push a.key else acc)
    #[]

def add (r : Registry) (a : Alt) : Registry := { r with alts := r.alts.push a }

/-- User alternatives are appended, so a custom `sqrt` competes with the built-in ones; keys in
`remove` drop the built-ins entirely. -/
def merge (r : Registry) (custom : Array Alt) (remove : Array String := #[]) : Registry :=
  { alts := (r.alts.filter fun a => !remove.contains a.key) ++ custom }

end Registry

namespace Builtins

private def tower : List Ty := [.nat, .int, .rat, .real, .complex]

private def arith (key template : String) (t : Ty) (prec : Nat) (argPrec : Array Nat) : Alt :=
  { key, template, params := #[t, t], result := t, transparent := true,
    computable := t.isComputable, prec, argPrec }

/-- `+ - * / % ^` and unary minus, one row per type. -/
def arithmetic : Array Alt := Id.run do
  let mut out : Array Alt := #[]
  for t in tower do
    out := out.push (arith "+" "{0} + {1}" t 65 #[65, 66])
    out := out.push (arith "-" "{0} - {1}" t 65 #[65, 66])
    out := out.push (arith "*" "{0} * {1}" t 70 #[70, 71])
    out := out.push (arith "/" "{0} / {1}" t 70 #[70, 71])
    -- `Monoid.npow`: any base with a natural exponent.
    out := out.push
      { key := "^", template := "{0} ^ {1}", params := #[t, .nat], result := t,
        transparent := true, computable := t.isComputable, prec := 75, argPrec := #[76, 75] }
    if t != .nat then
      out := out.push
        { key := "neg", template := "-{0}", params := #[t], result := t, transparent := true,
          computable := t.isComputable, prec := 75, argPrec := #[75] }
  for t in [Ty.nat, .int] do
    out := out.push (arith "%" "{0} % {1}" t 70 #[70, 71])
  -- `zpow`: a negative exponent needs a field. This is what makes `2^(2n-1)` work at `ℚ`, and
  -- with it sequences whose closed form passes through negative powers.
  for t in [Ty.rat, .real, .complex] do
    out := out.push
      { key := "^", template := "{0} ^ {1}", params := #[t, .int], result := t,
        transparent := true, computable := t.isComputable, bias := 1, prec := 75,
        argPrec := #[76, 75], imports := #["Mathlib.Algebra.Field.Rat"] }
  out := out.push
    { key := "^", template := "{0} ^ {1}", params := #[.real, .real], result := .real,
      transparent := true, computable := false, bias := 2, prec := 75, argPrec := #[76, 75],
      imports := #["Mathlib.Analysis.SpecialFunctions.Pow.Real"] }
  return out

private def fn (key template : String) (params : Array Ty) (result : Ty)
    (computable := true) (imports : Array String := #[]) (bias := 0) : Alt :=
  -- 1023 rather than 1024: an application used as another application's argument needs
  -- parentheses, so its own precedence must sit just below the argument context.
  { key, template, params, result, computable, imports, bias, prec := 1023,
    argPrec := Array.replicate params.size 1024 }

private def bracket (key template : String) (params : Array Ty) (result : Ty)
    (computable := true) (imports : Array String := #[]) (bias := 0) : Alt :=
  { key, template, params, result, computable, imports, bias, prec := 1024,
    argPrec := Array.replicate params.size 0 }

def functions : Array Alt := #[
  fn "sqrt" "Nat.sqrt {0}" #[.nat] .nat,
  fn "sqrt" "Int.sqrt {0}" #[.int] .int (imports := #["Mathlib.Data.Int.Sqrt"]),
  fn "sqrt" "Real.sqrt {0}" #[.real] .real (computable := false)
    (imports := #["Mathlib.Analysis.Real.Sqrt"]),

  -- `|n-1|` at `ℕ` goes through `Int.natAbs`, which is why an opaque result may sit below its
  -- context type.
  bracket "abs" "{0}" #[.nat] .nat,
  bracket "abs" "({0}).natAbs" #[.int] .nat,
  bracket "abs" "|{0}|" #[.int] .int (bias := 1)
    (imports := #["Mathlib.Algebra.Order.Group.Int", "Mathlib.Algebra.Order.Group.Unbundled.Abs"]),
  bracket "abs" "|{0}|" #[.real] .real (computable := false) (bias := 1)
    (imports := #["Mathlib.Algebra.Order.Group.Unbundled.Abs"]),

  bracket "floor" "{0}" #[.nat] .nat,
  bracket "floor" "{0}" #[.int] .int,
  bracket "floor" "⌊{0}⌋₊" #[.rat] .nat (imports := #["Mathlib.Data.Rat.Floor"]),
  bracket "floor" "⌊{0}⌋" #[.rat] .int (imports := #["Mathlib.Data.Rat.Floor"]) (bias := 1),
  bracket "floor" "⌊{0}⌋₊" #[.real] .nat (computable := false)
    (imports := #["Mathlib.Algebra.Order.Archimedean.Real.Basic"]),
  bracket "ceiling" "⌈{0}⌉₊" #[.rat] .nat (imports := #["Mathlib.Data.Rat.Floor"]),
  bracket "ceiling" "⌈{0}⌉" #[.rat] .int (imports := #["Mathlib.Data.Rat.Floor"]) (bias := 1),

  fn "!" "Nat.factorial {0}" #[.nat] .nat (imports := #["Mathlib.Data.Nat.Factorial.Basic"]),
  fn "!!" "Nat.doubleFactorial {0}" #[.nat] .nat
    (imports := #["Mathlib.Data.Nat.Factorial.DoubleFactorial"]),

  fn "binomial" "Nat.choose {0} {1}" #[.nat, .nat] .nat
    (imports := #["Mathlib.Data.Nat.Choose.Basic"]),
  fn "gcd" "Nat.gcd {0} {1}" #[.nat, .nat] .nat,
  fn "lcm" "Nat.lcm {0} {1}" #[.nat, .nat] .nat,
  fn "gcd" "Int.gcd {0} {1}" #[.int, .int] .nat (bias := 1),
  fn "min" "min {0} {1}" #[.nat, .nat] .nat,
  fn "max" "max {0} {1}" #[.nat, .nat] .nat,
  fn "min" "min {0} {1}" #[.int, .int] .int,
  fn "max" "max {0} {1}" #[.int, .int] .int,

  -- A subscript is the first argument, so `log_2(n)` and `log(2, n)` reach the same rows.
  fn "log" "Nat.log {0} {1}" #[.nat, .nat] .nat (imports := #["Mathlib.Data.Nat.Log"]),
  fn "log" "Real.logb {0} {1}" #[.real, .real] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Log.Base"]),
  fn "log" "Real.log {0}" #[.real] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Log.Basic"]),
  fn "ln" "Real.log {0}" #[.real] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Log.Basic"]),
  fn "exp" "Real.exp {0}" #[.real] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Exp"]),
  fn "sin" "Real.sin {0}" #[.real] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"]),
  fn "cos" "Real.cos {0}" #[.real] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"]),
  fn "tan" "Real.tan {0}" #[.real] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"]),

  fn "fibonacci" "Nat.fib {0}" #[.nat] .nat (imports := #["Mathlib.Data.Nat.Fib.Basic"]),
  fn "phi" "Nat.totient {0}" #[.nat] .nat (imports := #["Mathlib.Data.Nat.Totient"]),
  fn "totient" "Nat.totient {0}" #[.nat] .nat (imports := #["Mathlib.Data.Nat.Totient"]),

  -- Arity tells `pi` the constant from `pi(x)` the prime-counting function.
  fn "pi" "Real.pi" #[] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic"]),
  fn "pi" "Nat.primeCounting {0}" #[.nat] .nat
    (imports := #["Mathlib.NumberTheory.PrimeCounting"]),
  fn "e" "Real.exp 1" #[] .real (computable := false)
    (imports := #["Mathlib.Analysis.SpecialFunctions.Exp"]),
  fn "i" "Complex.I" #[] .complex (computable := false)
    (imports := #["Mathlib.Data.Complex.Basic"])
]

/-- Applied at the root only, when nothing produces the requested type directly. -/
def narrowings : Array Alt := #[
  bracket "narrow" "({0}).toNat" #[.int] .nat,
  bracket "narrow" "⌊{0}⌋₊" #[.rat] .nat (imports := #["Mathlib.Data.Rat.Floor"]),
  bracket "narrow" "⌊{0}⌋" #[.rat] .int (imports := #["Mathlib.Data.Rat.Floor"]),
  bracket "narrow" "⌊{0}⌋₊" #[.real] .nat (computable := false)
    (imports := #["Mathlib.Algebra.Order.Archimedean.Real.Basic"]),
  bracket "narrow" "⌊{0}⌋" #[.real] .int (computable := false)
    (imports := #["Mathlib.Algebra.Order.Archimedean.Real.Basic"])
]

def standard : Registry := { alts := arithmetic ++ functions }

/-! ## Propositions

Relations, conjunction and implication are alternatives with result type `prop`. They are built
on demand by `GenExpr.Infer` rather than listed in `standard`, since a relation is never an
operand of arithmetic. -/

/-- The Lean symbol of a relation, and the types it is decidable at. -/
def relSymbol : RelOp → String × List Ty
  | .eq => ("=", [.nat, .int, .rat, .real, .complex])
  | .ne => ("≠", [.nat, .int, .rat, .real, .complex])
  | .lt => ("<", [.nat, .int, .rat, .real])
  | .le => ("≤", [.nat, .int, .rat, .real])
  | .gt => (">", [.nat, .int, .rat, .real])
  | .ge => ("≥", [.nat, .int, .rat, .real])
  | .divides => ("∣", [.nat, .int])

/-- `l op r` with both sides at `t`. -/
def relAlt (op : RelOp) (t : Ty) : Alt :=
  let sym := (relSymbol op).1
  { key := sym, template := "{0} " ++ sym ++ " {1}", params := #[t, t], result := .prop
    computable := t.isComputable, prec := 50, argPrec := #[51, 51] }

def andAlt : Alt :=
  { key := "∧", template := "{0} ∧ {1}", params := #[.prop, .prop], result := .prop
    prec := 35, argPrec := #[36, 35] }

def impAlt : Alt :=
  { key := "→", template := "{0} → {1}", params := #[.prop, .prop], result := .prop
    prec := 25, argPrec := #[26, 25] }

/-- All `n` members equal, written `List.Pairwise` when every member is too long to repeat. -/
def pairwiseAlt (t : Ty) (n : Nat) : Alt :=
  { key := "pairwise"
    template := "List.Pairwise (· = ·) [" ++
      String.intercalate ", " ((List.range n).map fun i => s!"\{{i}}") ++ "]"
    params := Array.replicate n t, result := .prop, computable := t.isComputable
    prec := 1023, argPrec := Array.replicate n 0 }

/-- Modules providing the notation (`ℕ`, `ℚ`, …) and arithmetic instances a type needs. -/
def typeImports : Ty → Array String
  | .nat => #["Mathlib.Data.Nat.Notation"]
  | .int => #["Mathlib.Data.Int.Notation"]
  | .rat => #["Mathlib.Data.Rat.Init"]
  | .real => #["Mathlib.Data.Real.Basic"]
  | .complex => #["Mathlib.Data.Complex.Basic"]
  | _ => #[]

/-- Modules the lowering of an aggregator needs, by kind and by whether it is bounded. -/
def aggImports (kind : AggKind) (bounded divisors : Bool) : Array String :=
  match kind with
  | .integral => #["Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic"]
  | _ =>
    if divisors then #["Mathlib.Algebra.BigOperators.Group.Finset.Defs", "Mathlib.NumberTheory.Divisors"]
    else if bounded then
      #["Mathlib.Algebra.BigOperators.Group.Finset.Defs", "Mathlib.Order.Interval.Finset.Nat"]
    else #["Mathlib.Topology.Algebra.InfiniteSum.Defs", "Mathlib.Topology.Instances.Real.Lemmas"]

/-- Every import a computable reading of the standard catalogue can need. Importing these once
lets a single environment serve every candidate that can be evaluated. -/
def computableImports : Array String :=
  let alts := (standard.alts ++ narrowings).filter (·.computable)
  let all := (alts.map (·.imports)).flatten ++ typeImports .nat ++ typeImports .int ++
    typeImports .rat ++ aggImports .sum true false ++ aggImports .sum true true
  (all.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]).qsort (· < ·)

/-- Every import any reading of the standard catalogue can need, including the analysis behind
`∑'`, `∫` and the real functions. Much heavier than `computableImports`. -/
def allImports : Array String :=
  let all := ((standard.alts ++ narrowings).map (·.imports)).flatten ++
    ([Ty.nat, .int, .rat, .real, .complex].map typeImports).toArray.flatten ++
    aggImports .sum true false ++ aggImports .sum true true ++ aggImports .sum false false ++
    aggImports .integral true false
  (all.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]).qsort (· < ·)

end Builtins

end GenExpr
