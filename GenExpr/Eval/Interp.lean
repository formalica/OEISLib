import GenExpr.Render
import Std.Data.HashMap

/-!
Exact evaluator for typed expressions over `ℕ`, `ℤ` and `ℚ`.

It is deliberately built on Lean's own `Nat`, `Int` and `Rat` operations rather than on a
reimplementation, so truncated subtraction, floor division and Euclidean `Int` division agree with
the emitted code by construction.

Two things it provides that a Lean-level `#eval` cannot do cheaply:

* a **step budget**, giving real termination for recursive definitions — a compiled Lean term
  cannot be interrupted once it is running;
* an **override table**, consulted before a definition's body, so patching base cases costs
  nothing and a patched `a(0)` is immediately visible to the recursive calls that need it.

A call to a function known only by data points, outside its table, does not fail: it marks the
result *unknown*, so the point proves nothing rather than counting against the formula.
-/

namespace GenExpr

inductive Val where
  | nat (n : Nat)
  | int (n : Int)
  | rat (q : Rat)
deriving Inhabited, BEq, Repr

namespace Val

def render : Val → String
  | .nat n => toString n
  | .int n => toString n
  | .rat q => if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

def toRat : Val → Rat
  | .nat n => Rat.ofInt (Int.ofNat n)
  | .int n => Rat.ofInt n
  | .rat q => q

def toInt? : Val → Option Int
  | .nat n => some (Int.ofNat n)
  | .int n => some n
  | .rat q => if q.den == 1 then some q.num else none

def toNat? : Val → Option Nat
  | .nat n => some n
  | .int n => if n ≥ 0 then some n.toNat else none
  | .rat q => if q.den == 1 && q.num ≥ 0 then some q.num.toNat else none

/-- Whether the value equals an integer the caller expects. -/
def eqInt (v : Val) (e : Int) : Bool := v.toInt? == some e

end Val

inductive EvalError where
  | budget
  | unsupported (what : String)
  | notComputable (ty : Ty)
  | badValue (what : String)
deriving BEq, Repr

namespace EvalError

def describe : EvalError → String
  | .budget => "step budget exhausted"
  | .unsupported w => s!"cannot evaluate {w}"
  | .notComputable t => s!"{t} is not evaluable"
  | .badValue w => s!"bad value: {w}"

end EvalError

/-! ## Number-theoretic helpers

Written here rather than taken from Mathlib so that the evaluator stays importable without it. -/

namespace Interp

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def doubleFactorial : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Largest `k` with `b ^ k ≤ n`, matching `Nat.log`. -/
def natLog (b n : Nat) : Nat := Id.run do
  if b < 2 || n == 0 then return 0
  let mut k := 0
  let mut acc := b
  for _ in [0:n] do
    if acc > n then break
    k := k + 1
    acc := acc * b
  return k

def fib (n : Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for _ in [0:n] do
    let t := a + b
    a := b
    b := t
  return a

def totient (n : Nat) : Nat := Id.run do
  if n == 0 then return 0
  let mut c := 0
  for i in [1:n + 1] do
    if Nat.gcd i n == 1 then c := c + 1
  return c

def divisors (n : Nat) : Array Nat := Id.run do
  if n == 0 then return #[]
  let mut out := #[]
  for d in [1:n + 1] do
    if n % d == 0 then out := out.push d
  return out

/-- `⌊q⌋`. -/
def ratFloor (q : Rat) : Int :=
  if q.den == 1 then q.num
  else if q.num ≥ 0 then q.num / (Int.ofNat q.den)
  else q.num / (Int.ofNat q.den) - 1

def ratCeil (q : Rat) : Int := -(ratFloor (-q))

/-- `q ^ k` for a possibly negative exponent. -/
def ratZpow (q : Rat) (k : Int) : Rat :=
  if k ≥ 0 then q ^ k.toNat
  else if q == 0 then 0
  else (1 / q) ^ (-k).toNat

end Interp

/-! ## Evaluation -/

/-- A definition the evaluator can call: the goal itself, or one of its auxiliaries. -/
structure EvalDef where
  params : Array (String × Ty)
  body : TExpr
deriving Inhabited

structure EvalCtx where
  self : EvalDef
  /-- Auxiliary definitions, by name. -/
  aux : Array (String × EvalDef) := #[]
  /-- Functions known only by data points; a call outside the table yields `unknown`. -/
  tables : Array (String × Array (Array Int × Int)) := #[]
  /-- Values patched in as base cases, consulted before any body runs. -/
  overrides : Array (Array Int × Int) := #[]
deriving Inhabited

structure EvalState where
  steps : Nat := 200000
  memo : Std.HashMap String Val := {}
  /-- Set when a data-only function was queried outside its table. -/
  usedUnknown : Bool := false
deriving Inhabited

abbrev EvalM := ExceptT EvalError (StateM EvalState)

private def tick : EvalM Unit := do
  let s ← get
  if s.steps == 0 then throw .budget
  set { s with steps := s.steps - 1 }

private def castTo (dst : Ty) (v : Val) : EvalM Val :=
  match dst with
  | .nat => match v.toNat? with
    | some n => pure (.nat n)
    | none => throw (.badValue "negative or fractional value where ℕ expected")
  | .int => match v.toInt? with
    | some n => pure (.int n)
    | none => throw (.badValue "fractional value where ℤ expected")
  | .rat => pure (.rat v.toRat)
  | t => throw (.notComputable t)

private def asNat (v : Val) : EvalM Nat :=
  match v.toNat? with
  | some n => pure n
  | none => throw (.badValue "expected a natural number")

private def asInt (v : Val) : EvalM Int :=
  match v.toInt? with
  | some n => pure n
  | none => throw (.badValue "expected an integer")

/-- Arithmetic, evaluated at the type the alternative was chosen at. -/
private def arith (key : String) (ty : Ty) (expTy : Ty) (a b : Val) : EvalM Val := do
  match ty with
  | .nat =>
    let x ← asNat a
    let y ← asNat b
    match key with
    | "+" => pure (.nat (x + y))
    | "-" => pure (.nat (x - y))
    | "*" => pure (.nat (x * y))
    | "/" => pure (.nat (x / y))
    | "%" => pure (.nat (x % y))
    | "^" => pure (.nat (x ^ y))
    | k => throw (.unsupported s!"{k} over ℕ")
  | .int =>
    match key with
    | "^" => pure (.int ((← asInt a) ^ (← asNat b)))
    | _ =>
      let x ← asInt a
      let y ← asInt b
      match key with
      | "+" => pure (.int (x + y))
      | "-" => pure (.int (x - y))
      | "*" => pure (.int (x * y))
      | "/" => pure (.int (x / y))
      | "%" => pure (.int (x % y))
      | k => throw (.unsupported s!"{k} over ℤ")
  | .rat =>
    match key with
    | "^" =>
      let base := a.toRat
      if expTy == .int then pure (.rat (Interp.ratZpow base (← asInt b)))
      else pure (.rat (base ^ (← asNat b)))
    | _ =>
      let x := a.toRat
      let y := b.toRat
      match key with
      | "+" => pure (.rat (x + y))
      | "-" => pure (.rat (x - y))
      | "*" => pure (.rat (x * y))
      | "/" => pure (.rat (if y == 0 then 0 else x / y))
      | k => throw (.unsupported s!"{k} over ℚ")
  | t => throw (.notComputable t)

private def unary (key : String) (params : Array Ty) (result : Ty) (v : Val) : EvalM Val := do
  match key, params[0]!, result with
  | "neg", .int, _ => pure (.int (-(← asInt v)))
  | "neg", .rat, _ => pure (.rat (-v.toRat))
  | "sqrt", .nat, _ => pure (.nat (Nat.sqrt (← asNat v)))
  | "sqrt", .int, _ =>
    let n ← asInt v
    pure (.int (Int.ofNat (Nat.sqrt (if n < 0 then 0 else n.toNat))))
  | "abs", .nat, _ => pure v
  | "abs", .int, .nat => pure (.nat (← asInt v).natAbs)
  | "abs", .int, .int => do
    let n ← asInt v
    pure (.int (if n < 0 then -n else n))
  | "floor", .nat, _ | "floor", .int, _ => pure v
  | "floor", .rat, .nat => pure (.nat (Interp.ratFloor v.toRat).toNat)
  | "floor", .rat, .int => pure (.int (Interp.ratFloor v.toRat))
  | "ceiling", .rat, .nat => pure (.nat (Interp.ratCeil v.toRat).toNat)
  | "ceiling", .rat, .int => pure (.int (Interp.ratCeil v.toRat))
  | "narrow", .int, .nat => pure (.nat (← asInt v).toNat)
  | "narrow", .rat, .nat => pure (.nat (Interp.ratFloor v.toRat).toNat)
  | "narrow", .rat, .int => pure (.int (Interp.ratFloor v.toRat))
  | "!", _, _ => pure (.nat (Interp.factorial (← asNat v)))
  | "!!", _, _ => pure (.nat (Interp.doubleFactorial (← asNat v)))
  | "fibonacci", _, _ => pure (.nat (Interp.fib (← asNat v)))
  | "phi", _, _ | "totient", _, _ => pure (.nat (Interp.totient (← asNat v)))
  | k, p, r => throw (.unsupported s!"{k} : {p} → {r}")

private def binary (key : String) (result : Ty) (a b : Val) : EvalM Val := do
  match key with
  | "binomial" => pure (.nat (Interp.choose (← asNat a) (← asNat b)))
  | "gcd" =>
    if result == .nat then pure (.nat (Nat.gcd (← asInt a).natAbs (← asInt b).natAbs))
    else pure (.int (Int.ofNat (Nat.gcd (← asInt a).natAbs (← asInt b).natAbs)))
  | "lcm" => pure (.nat (Nat.lcm (← asNat a) (← asNat b)))
  | "log" => pure (.nat (Interp.natLog (← asNat a) (← asNat b)))
  | "min" =>
    if result == .nat then pure (.nat (min (← asNat a) (← asNat b)))
    else pure (.int (min (← asInt a) (← asInt b)))
  | "max" =>
    if result == .nat then pure (.nat (max (← asNat a) (← asNat b)))
    else pure (.int (max (← asInt a) (← asInt b)))
  | k => throw (.unsupported s!"{k}/2")

private def zeroOf : Ty → Val
  | .nat => .nat 0
  | .int => .int 0
  | _ => .rat 0

private def oneOf : Ty → Val
  | .nat => .nat 1
  | .int => .int 1
  | _ => .rat 1

private def litVal (text : String) : Ty → EvalM Val
  | .nat => pure (.nat text.toNat!)
  | .int => pure (.int (Int.ofNat text.toNat!))
  | .rat => pure (.rat (Rat.ofInt (Int.ofNat text.toNat!)))
  | t => throw (.notComputable t)

private def decVal (whole frac : String) : Ty → EvalM Val
  | .rat | .real | .complex =>
    pure (.rat (Rat.ofInt (Int.ofNat (whole ++ frac).toNat!) / Rat.ofInt (10 ^ frac.length)))
  | t => throw (.notComputable t)

private def memoKey (name : String) (args : Array Int) : String :=
  name ++ "|" ++ String.intercalate "," (args.toList.map toString)

/-- A decided proposition is `1` or `0`, which is also what a `decide` probe prints. -/
private def ofBool (b : Bool) : Val := .nat (if b then 1 else 0)

private def isTrue (v : Val) : Bool := v == .nat 1

/-- One relation between two values at the type the relation was chosen at. -/
private def relate (key : String) (a b : Val) : EvalM Bool := do
  match key with
  | "∣" =>
    let x ← asInt a
    let y ← asInt b
    -- Lean's `∣`: `0 ∣ y` iff `y = 0`.
    pure (if x == 0 then y == 0 else y % x == 0)
  | _ =>
    let x := a.toRat
    let y := b.toRat
    match key with
    | "=" => pure (x == y)
    | "≠" => pure (x != y)
    | "<" => pure (x < y)
    | "≤" => pure (x ≤ y)
    | ">" => pure (x > y)
    | "≥" => pure (x ≥ y)
    | k => throw (.unsupported s!"relation {k}")

mutual

partial def evalExpr (ctx : EvalCtx) (locals : Array (String × Val)) : TExpr → EvalM Val
  | .lit t ty => do tick; litVal t ty
  | .dec w f ty => do tick; decVal w f ty
  | .var n _ => do
    tick
    match locals.find? fun (v, _) => v == n with
    | some (_, v) => pure v
    | none => throw (.badValue s!"unbound variable {n}")
  | .cast _ d e => do tick; castTo d (← evalExpr ctx locals e)
  | .node alt args => do
    tick
    if alt.template.startsWith selfToken then
      castTo alt.result (← callDef ctx locals alt.key ctx.self args)
    else if let some (_, d) := ctx.aux.find? fun (n, _) => n == alt.key then
      castTo alt.result (← callDef ctx locals alt.key d args)
    else if let some (_, tbl) := ctx.tables.find? fun (n, _) => n == alt.key then
      let vs ← args.mapM (evalExpr ctx locals)
      let key ← vs.mapM asInt
      match tbl.find? fun (a, _) => a == key with
      | some (_, v) => castTo alt.result (.int v)
      | none =>
        modify fun s => { s with usedUnknown := true }
        pure (zeroOf alt.result)
    else if alt.result == .prop then
      -- Short-circuit exactly as Lean's `Decidable` instances do, so a false hypothesis never
      -- evaluates a conclusion that might not be defined there.
      match alt.key with
      | "∧" =>
        if isTrue (← evalExpr ctx locals args[0]!) then evalExpr ctx locals args[1]!
        else pure (ofBool false)
      | "→" =>
        if isTrue (← evalExpr ctx locals args[0]!) then evalExpr ctx locals args[1]!
        else pure (ofBool true)
      | "pairwise" =>
        let vs ← args.mapM (evalExpr ctx locals)
        pure (ofBool (vs.all fun x => x.toRat == vs[0]!.toRat))
      | key =>
        let vs ← args.mapM (evalExpr ctx locals)
        pure (ofBool (← relate key vs[0]! vs[1]!))
    else
      let vs ← args.mapM (evalExpr ctx locals)
      match vs.size with
      | 0 => throw (.unsupported s!"constant {alt.key}")
      | 1 =>
        if alt.transparent || alt.key == "neg" then unary alt.key alt.params alt.result vs[0]!
        else unary alt.key alt.params alt.result vs[0]!
      | 2 =>
        if alt.transparent then
          arith alt.key alt.result (alt.params[1]!) vs[0]! vs[1]!
        else binary alt.key alt.result vs[0]! vs[1]!
      | _ => throw (.unsupported s!"{alt.key}/{vs.size}")
  | .agg kind var lo hi dv _ hiStrict body ty => do
    tick
    if kind == .integral then throw (.notComputable ty)
    let combine := if kind == .prod then "*" else "+"
    let mut acc := if kind == .prod then oneOf ty else zeroOf ty
    let idxs ← aggIndices ctx locals lo hi dv hiStrict
    for i in idxs do
      acc ← arith combine ty ty acc (← evalExpr ctx (locals.push (var, .nat i)) body)
    return acc

/-- The values the binder ranges over. -/
partial def aggIndices (ctx : EvalCtx) (locals : Array (String × Val))
    (lo hi dv : Option TExpr) (hiStrict : Bool) : EvalM (Array Nat) := do
  if let some d := dv then
    let n ← asNat (← evalExpr ctx locals d)
    return Interp.divisors n
  match lo, hi with
  | some l, some h =>
    let a ← asNat (← evalExpr ctx locals l)
    let b ← asNat (← evalExpr ctx locals h)
    let stop := if hiStrict then b else b + 1
    if stop < a then return #[]
    -- Each step of the loop is charged, so a runaway range hits the budget.
    for _ in [0:stop - a] do tick
    return (Array.range (stop - a)).map fun i => a + i
  | _, _ => throw (.notComputable .real)

partial def callDef (ctx : EvalCtx) (locals : Array (String × Val)) (name : String)
    (d : EvalDef) (args : Array TExpr) : EvalM Val := do
  let vs ← args.mapM (evalExpr ctx locals)
  let key ← vs.mapM asInt
  if let some (_, v) := ctx.overrides.find? fun (a, _) => a == key then
    return ← castTo d.body.ty (.int v)
  let mk := memoKey name key
  if let some v := (← get).memo[mk]? then return v
  let inner := Array.zip (d.params.map (·.1)) vs
  let v ← evalExpr ctx inner d.body
  modify fun s => { s with memo := s.memo.insert mk v }
  return v

end

/-- Result of evaluating one point. -/
inductive PointResult where
  | ok (v : Val)
  /-- A data-only function was queried outside its table, so nothing is proved. -/
  | unknown
  | error (e : EvalError)
deriving Repr

/-- Evaluate a definition at one argument tuple. -/
def evalAt (ctx : EvalCtx) (args : Array Int) (budget : Nat)
    (memo : Std.HashMap String Val := {}) : PointResult × Std.HashMap String Val :=
  let vs := (Array.zip ctx.self.params args).map fun ((_, ty), a) =>
    match ty with
    | .nat => Val.nat a.toNat
    | .int => Val.int a
    | _ => Val.rat (Rat.ofInt a)
  let locals := Array.zip (ctx.self.params.map (·.1)) vs
  let start : EvalState := { steps := budget, memo }
  let (r, st) := (evalExpr ctx locals ctx.self.body).run.run start
  let res :=
    match r with
    | .error e => PointResult.error e
    | .ok v => if st.usedUnknown then .unknown else .ok v
  (res, st.memo)

end GenExpr
