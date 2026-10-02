/-!
Core data types shared by every stage of GenExpr.

Nothing in this module (or in the rest of `GenExpr`, except `GenExpr.Verify`) depends on
Mathlib or on the OEIS project: the parser is a standalone library.
-/

namespace GenExpr

/-! ## Source locations -/

/-- Byte range `[start, stop)` into the original input string. -/
structure Span where
  start : Nat := 0
  stop : Nat := 0
deriving DecidableEq, Repr, Inhabited, Hashable

namespace Span

/-- Smallest span covering both arguments. -/
def merge (a b : Span) : Span := ⟨min a.start b.start, max a.stop b.stop⟩

def size (s : Span) : Nat := s.stop - s.start

def isEmpty (s : Span) : Bool := s.stop ≤ s.start

instance : ToString Span where
  toString s := s!"{s.start}..{s.stop}"

end Span

/-! ## Types -/

/-- Scalar types a formula can be interpreted at.

`nat < int < rat < real < complex` is a total order (the *numeric tower*); widening along it is
always available as a coercion. `prop` and `other` sit outside the tower — `other` is reserved so
that `PNat`, subtypes, `EReal` and `PowerSeries` can be added later without touching inference. -/
inductive Ty where
  | nat
  | int
  | rat
  | real
  | complex
  | prop
  | other (name : String)
deriving DecidableEq, Repr, Inhabited, Hashable

namespace Ty

/-- Position in the numeric tower; `98`/`99` keep non-numeric types out of every comparison. -/
def level : Ty → Nat
  | .nat => 0
  | .int => 1
  | .rat => 2
  | .real => 3
  | .complex => 4
  | .other _ => 98
  | .prop => 99

def ofLevel : Nat → Ty
  | 0 => .nat
  | 1 => .int
  | 2 => .rat
  | 3 => .real
  | _ => .complex

def isNumeric : Ty → Bool
  | .nat | .int | .rat | .real | .complex => true
  | _ => false

/-- Values of `nat`/`int`/`rat` can be evaluated; `real`/`complex` cannot. -/
def isComputable : Ty → Bool
  | .nat | .int | .rat => true
  | _ => false

/-- `a ≤ b`: a value of type `a` widens to `b`. Never narrows, never crosses out of the tower. -/
def le (a b : Ty) : Bool :=
  if a == b then true
  else a.isNumeric && b.isNumeric && a.level ≤ b.level

def max (a b : Ty) : Ty :=
  if a.le b then b else if b.le a then a else a

def render : Ty → String
  | .nat => "ℕ"
  | .int => "ℤ"
  | .rat => "ℚ"
  | .real => "ℝ"
  | .complex => "ℂ"
  | .prop => "Prop"
  | .other n => n

instance : ToString Ty where
  toString := render

end Ty

/-- The type of a whole formalization: `args → ret`. `args = []` means a constant or a `Prop`. -/
structure FnTy where
  args : List Ty := []
  ret : Ty
deriving DecidableEq, Repr, Inhabited

namespace FnTy

def arity (t : FnTy) : Nat := t.args.length

def render (t : FnTy) : String :=
  String.intercalate " → " ((t.args.map Ty.render) ++ [t.ret.render])

instance : ToString FnTy where
  toString := render

end FnTy

/-! ## Type sets

A 5-bit mask over the numeric tower. Feasibility analysis works entirely with these, which keeps
the bottom-up pass at `O(nodes × alternatives × 5)`. -/

/-- Subset of `{nat, int, rat, real, complex}`; never contains `prop` or `other`. -/
structure TySet where
  mask : UInt8 := 0
deriving DecidableEq, Repr, Inhabited, Hashable

namespace TySet

def empty : TySet := ⟨0⟩

def full : TySet := ⟨0x1F⟩

def single (t : Ty) : TySet :=
  if t.isNumeric then ⟨(1 : UInt8) <<< t.level.toUInt8⟩ else empty

/-- Every type `t` widens to: `{t, ...}` upwards in the tower. -/
def upClosure (t : Ty) : TySet :=
  if t.isNumeric then ⟨(0x1F <<< t.level.toUInt8) &&& 0x1F⟩ else empty

def mem (s : TySet) (t : Ty) : Bool := s.mask &&& (single t).mask != 0

def inter (a b : TySet) : TySet := ⟨a.mask &&& b.mask⟩

def union (a b : TySet) : TySet := ⟨a.mask ||| b.mask⟩

def isEmpty (s : TySet) : Bool := s.mask == 0

def toList (s : TySet) : List Ty :=
  [Ty.nat, .int, .rat, .real, .complex].filter s.mem

/-- Cheapest member, i.e. the lowest rung of the tower present. -/
def min? (s : TySet) : Option Ty := s.toList.head?

instance : ToString TySet where
  toString s := "{" ++ String.intercalate ", " (s.toList.map Ty.render) ++ "}"

end TySet

/-! ## Rejection reasons

Every candidate that does not make it into the result keeps a reason. Tests assert on these, and
they are what a "which formulas can we no longer parse?" report is built from. -/

inductive Reject where
  /-- A lone identifier or number: syntactically fine, carries no formula. -/
  | bareAtom
  /-- An identifier that resolves to nothing (not a parameter, binder, builtin, custom or aux def). -/
  | hole (name : String)
  /-- More free variables than the requested signature can bind. -/
  | tooManyFreeVars (names : List String)
  /-- No interpretation of the expression has the requested type. -/
  | typeUnachievable (ty : Ty)
  /-- Requested a function but the fragment is not of the form `f(x…) = rhs`. -/
  | notDefinitionForm
  | mutualRecursion (names : List String)
  | insufficientBaseValues (needed available : Nat)
  | unbalanced
  | elabError (msg : String)
  /-- Value mismatch at a data point that may not be patched away. -/
  | failedAt (index : Nat) (expected got : String)
  | belowSuccessRate (passed total : Nat)
  /-- A data-only custom function was queried outside its table, so the point proves nothing. -/
  | indeterminate
  | nonTerminating
  /-- Well typed but not evaluable, so it cannot be checked against data. -/
  | notComputable
  /-- The two verification engines computed different values for the same point. -/
  | engineDisagreement (index : Nat) (internal lean : String)
  | unsupported (what : String)
deriving DecidableEq, Repr, Inhabited

namespace Reject

def describe : Reject → String
  | .bareAtom => "bare atom, not a formula"
  | .hole n => s!"unresolved name '{n}'"
  | .tooManyFreeVars ns => s!"too many free variables: {ns}"
  | .typeUnachievable t => s!"no interpretation of type {t}"
  | .notDefinitionForm => "not of the form f(x…) = rhs"
  | .mutualRecursion ns => s!"mutual recursion between {ns}"
  | .insufficientBaseValues need avail => s!"needs {need} base values, {avail} available"
  | .unbalanced => "unbalanced brackets"
  | .elabError m => s!"Lean rejected the rendering: {m}"
  | .failedAt i exp got => s!"value mismatch at point {i}: expected {exp}, got {got}"
  | .belowSuccessRate p t => s!"only {p}/{t} data points verified"
  | .indeterminate => "depends on values outside every known table"
  | .nonTerminating => "recursion does not terminate"
  | .notComputable => "not computable, cannot be checked against data"
  | .engineDisagreement i a b => s!"engines disagree at point {i}: internal {a}, Lean {b}"
  | .unsupported w => s!"unsupported: {w}"

instance : ToString Reject where
  toString := describe

end Reject

end GenExpr
