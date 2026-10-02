import GenExpr.Eval.Interp

/-!
Checking a candidate against known values.

The policy follows the spec: failures are only forgivable as a *prefix*. A formula that is right
from some index onwards is repaired by turning the leading disagreements into base cases, which
is allowed either because the caller permits that many (`allowedFailures`) or because the text
itself said so (`for n > 1`). A failure in the middle rejects the candidate outright.

Points that time out, or that depend on a value no table knows, never count as failures — they
just do not count as evidence either, so they lower the success rate.

The policy is written once, in `runPolicy`, over an abstract point evaluator. The interpreter
here and the Lean backend in `GenExpr.LeanEngine` only differ in how one point is evaluated, so
the two engines cannot drift apart on *what* counts as verified.
-/

namespace GenExpr

/-- Which backend checks the values.

The interpreter has real step budgets, which a compiled Lean term cannot offer, so it is the
default for the pure API; `lean` checks the declaration exactly as emitted; `internalThenLean`
uses the interpreter to choose and Lean to confirm; `crossCheck` runs both independently and
rejects on any disagreement, which is what keeps the two semantics from drifting. -/
inductive Engine where
  | internal
  | lean
  | internalThenLean
  | crossCheck
deriving DecidableEq, Repr, Inhabited

namespace Engine

def ofString? : String → Option Engine
  | "internal" => some .internal
  | "lean" => some .lean
  | "internalThenLean" | "internal+lean" => some .internalThenLean
  | "crossCheck" => some .crossCheck
  | _ => none

def name : Engine → String
  | .internal => "internal" | .lean => "lean" | .internalThenLean => "internalThenLean"
  | .crossCheck => "crossCheck"

def usesLean : Engine → Bool
  | .internal => false
  | _ => true

end Engine

structure VerifyConfig where
  engine : Engine := .internalThenLean
  /-- How many leading disagreements may be turned into base cases. -/
  allowedFailures : Nat := 0
  /-- Fraction of the supplied points that must actually verify. -/
  minSuccessRate : Float := 0.66
  budgetPerPoint : Nat := 200000
deriving Inhabited

inductive PointStatus where
  | pass
  | patched
  | fail (got : String)
  | unknown
  | timeout
deriving Repr, BEq, Inhabited

namespace PointStatus

def symbol : PointStatus → String
  | .pass => "." | .patched => "b" | .fail _ => "X" | .unknown => "?" | .timeout => "t"

/-- Whether the point counts as evidence for the formula. -/
def isGood : PointStatus → Bool
  | .pass | .patched => true
  | _ => false

end PointStatus

structure VerifyReport where
  statuses : Array PointStatus := #[]
  passed : Nat := 0
  /-- Leading points supplied as base cases; these become the arms of the emitted definition. -/
  patched : Array (Array Int × Int) := #[]
  accepted : Bool := false
  reason : Option Reject := none
  /-- Points whose value Lean computed from the emitted declaration and confirmed. -/
  leanChecked : Nat := 0
  /-- `some true` once Lean has elaborated the emitted declaration; `none` if it was never asked. -/
  elaborated : Option Bool := none
  /-- The rung of the recursion ladder Lean accepted, when Lean was asked. -/
  recForm : Option RecForm := none
deriving Inhabited

namespace VerifyReport

def trace (r : VerifyReport) : String := String.join (r.statuses.toList.map PointStatus.symbol)

end VerifyReport

/-- What evaluating one point produced. -/
inductive Outcome where
  /-- The computed value, printed the way `toString` prints an `Int`. -/
  | value (s : String)
  /-- It depended on a value no table knows. -/
  | unknown
  /-- It depended on a junk base case or ran out of fuel: repairable by a base case at a
  patchable position, otherwise merely unknown. -/
  | undetermined
  | timeout
  /-- Could not be evaluated; repairable by a base case at a patchable position. -/
  | error (r : Reject)
  /-- Rejects the reading outright, wherever it happens. -/
  | fatal (r : Reject)
deriving Inhabited

/-- Smallest index the text claims the formula holds from, if it says so. -/
def guardLowerBound (guards : Array Guard) (param : String) : Option Int :=
  guards.foldl (init := none) fun acc g =>
    if g.var != param then acc
    else
      let b? := match g.op with
        | .gt => some (g.bound + 1)
        | .ge => some g.bound
        | _ => none
      match acc, b? with
      | some a, some b => some (max a b)
      | none, b => b
      | a, none => a

/-- What to do about one data point. -/
private inductive Decision where
  | pass
  | patch
  | unknown
  | timeoutRest
  | reject (r : Reject)

/-- The verification policy, shared by every engine. `eval overrides args` evaluates the candidate
at `args` with the given points already supplied as base cases. -/
def runPolicy [Monad m] (cfg : VerifyConfig) (points : Array (Array Int × Int))
    (lowerBound : Option Int) (eval : Array (Array Int × Int) → Array Int → m Outcome) :
    m VerifyReport := do
  if points.isEmpty then return { accepted := false, reason := some (.belowSuccessRate 0 0) }
  let mut overrides : Array (Array Int × Int) := #[]
  let mut statuses : Array PointStatus := #[]
  let mut passed := 0
  let mut i := 0
  for (args, expected) in points do
    let r ← eval overrides args
    -- A recursive body cannot produce its own base cases, so *any* outcome at a patchable
    -- position — mismatch, divergence, or an out-of-domain value — is repaired the same way.
    let patchable :=
      i == overrides.size &&
        (overrides.size < cfg.allowedFailures ||
          (match lowerBound, args[0]? with
            | some b, some a => a < b
            | _, _ => false))
    let decision : Decision :=
      match r with
      | .value v =>
        if v == toString expected then .pass
        else if patchable then .patch
        else .reject (.failedAt i (toString expected) v)
      | .unknown => .unknown
      | .undetermined => if patchable then .patch else .unknown
      | .timeout => if patchable then .patch else .timeoutRest
      | .error rj => if patchable then .patch else .reject rj
      | .fatal rj => .reject rj
    match decision with
    | .pass =>
      statuses := statuses.push .pass
      passed := passed + 1
    | .patch =>
      overrides := overrides.push (args, expected)
      statuses := statuses.push .patched
      passed := passed + 1
    | .unknown => statuses := statuses.push .unknown
    | .timeoutRest =>
      statuses := statuses ++ Array.replicate (points.size - statuses.size) PointStatus.timeout
      break
    | .reject rj =>
      let got := match rj with | .failedAt _ _ g => g | _ => "?"
      return { statuses := statuses.push (.fail got), passed, patched := overrides
               accepted := false, reason := some rj }
    i := i + 1
  let rate := passed.toFloat / points.size.toFloat
  if rate < cfg.minSuccessRate then
    return { statuses, passed, patched := overrides, accepted := false
             reason := some (.belowSuccessRate passed points.size) }
  return { statuses, passed, patched := overrides, accepted := true }

/-- Everything the interpreter needs, assembled from a typing. -/
def evalCtxOf (t : Typing) (tables : Array (String × Array (Array Int × Int)) := #[]) : EvalCtx :=
  { self := { params := t.params, body := t.expr }
    aux := t.aux.map fun (n, ps, b) => (n, { params := ps, body := b })
    tables }

/-- The interpreter as a point evaluator. Its memo table is only valid for one set of base
cases, so it is dropped whenever another one is added. -/
private def internalEval (budget : Nat) (ctx : EvalCtx) (overrides : Array (Array Int × Int))
    (args : Array Int) : StateM (Nat × Std.HashMap String Val) Outcome := do
  let (seen, memo) ← get
  let memo := if seen == overrides.size then memo else {}
  let (r, memo') := evalAt { ctx with overrides } args budget memo
  set (overrides.size, memo')
  return match r with
    | .ok v => .value v.render
    | .unknown => .unknown
    | .error .budget => .timeout
    | .error e => .error (.unsupported e.describe)

/-- Run the interpreter over the points, repairing a leading prefix where that is allowed. -/
def verifyInternal (cfg : VerifyConfig) (ctx : EvalCtx) (points : Array (Array Int × Int))
    (lowerBound : Option Int := none) : VerifyReport :=
  (runPolicy cfg points lowerBound (internalEval cfg.budgetPerPoint ctx)).run' (0, {})

/-- Check one typing against known values with the interpreter. -/
def verify (cfg : VerifyConfig) (t : Typing) (points : Array (Array Int × Int))
    (guards : Array Guard := #[]) (tables : Array (String × Array (Array Int × Int)) := #[]) :
    VerifyReport :=
  if !t.computable then
    { accepted := false, reason := some .notComputable }
  else
    let bound := (t.params[0]?.map (·.1)).bind (guardLowerBound guards)
    verifyInternal cfg (evalCtxOf t tables) points bound

/-- Try the readings in order and return the first that verifies, with its report. -/
def firstVerified (cfg : VerifyConfig) (ts : List Typing) (points : Array (Array Int × Int))
    (guards : Array Guard := #[]) (tables : Array (String × Array (Array Int × Int)) := #[]) :
    Option (Typing × VerifyReport) × Array (Typing × VerifyReport) := Id.run do
  let mut tried : Array (Typing × VerifyReport) := #[]
  for t in ts do
    let r := verify cfg t points guards tables
    tried := tried.push (t, r)
    if r.accepted then return (some (t, r), tried)
  return (none, tried)

end GenExpr
