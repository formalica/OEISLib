module
public import GenExpr.Typed
public meta import GenExpr.Typed
public import GenExpr.Normalize
public meta import GenExpr.Normalize
public import GenExpr.Plan
public meta import GenExpr.Plan

/-!
Type inference.

For every subexpression a small table holds the `k` cheapest typed readings **per result type**.
The table is built bottom-up, so it doubles as the feasibility analysis: a slot is empty exactly
when that type is unreachable, and "can the goal have type `T`?" is one array lookup rather than a
separate pass.

Coercion happens at *use* sites, in `Table.atMost`, and only for readings whose top node may be
cast — leaves and opaque results. An arithmetic operator is instead re-selected at the context
type, which is why `(n-2) * 2^(2n-1)` at `ℚ` comes out as `((n : ℚ) - 2) * 2 ^ (2*(n : ℤ) - 1)`
rather than with a cast wrapped around a truncated subtraction.

Narrowing (`ℤ → ℕ`, `⌊·⌋₊`) is offered only at the root, and only after the exact readings.
-/

namespace GenExpr
public section

/-- One typed reading of a subexpression. -/
structure Choice where
  cost : Nat
  computable : Bool
  expr : TExpr
  /-- The top node is an arithmetic operator, so its result must never be cast. -/
  transparentTop : Bool
deriving Inhabited

/-- The `k` cheapest readings at each rung of the numeric tower. -/
structure Table where
  slots : Array (List Choice) := Array.replicate 5 []
deriving Inhabited

namespace Table

private def best (k : Nat) (xs : List Choice) : List Choice :=
  let sorted := xs.toArray.qsort fun a b =>
    a.cost < b.cost || (a.cost == b.cost && a.expr.size < b.expr.size)
  let deduped := sorted.foldl (fun acc c =>
    if acc.any (fun d => d.expr == c.expr) then acc else acc.push c) #[]
  deduped.toList.take k

def get (t : Table) (ty : Ty) : List Choice :=
  if ty.isNumeric then t.slots[ty.level]!.toArray.toList else []

def add (k : Nat) (t : Table) (ty : Ty) (c : Choice) : Table :=
  if !ty.isNumeric then t
  else { slots := t.slots.modify ty.level fun l => best k (c :: l) }

def isEmpty (t : Table) : Bool := t.slots.all List.isEmpty

def types (t : Table) : List Ty :=
  [Ty.nat, .int, .rat, .real, .complex].filter fun ty => !(t.get ty).isEmpty

def merge (k : Nat) (a b : Table) : Table :=
  { slots := (Array.zip a.slots b.slots).map fun (x, y) => best k (x ++ y) }

/-- Readings usable where a value of type `want` is expected. A reading at a lower type is lifted
by a cast, unless its top node is an arithmetic operator. -/
def atMost (t : Table) (want : Ty) (k : Nat) : List Choice :=
  if !want.isNumeric then [] else
  let lifted := (List.range want.level).flatMap fun lvl =>
    (t.slots[lvl]!).filterMap fun c =>
      if c.transparentTop || c.expr.isLiteral then none
      else
        let src := Ty.ofLevel lvl
        some { cost := c.cost + (want.level - lvl) + 1
               computable := c.computable && want.isComputable
               expr := .cast src want c.expr
               transparentTop := false }
  best k (t.slots[want.level]! ++ lifted)

end Table

structure ICtx where
  reg : Registry
  /-- Parameters and aggregator binders in scope. -/
  vars : Array (String × Ty) := #[]
  k : Nat := 4
deriving Inhabited

namespace ICtx

def varTy? (ctx : ICtx) (n : String) : Option Ty :=
  (ctx.vars.find? fun (v, _) => v == n).map (·.2)

def bind (ctx : ICtx) (n : String) (t : Ty) : ICtx := { ctx with vars := ctx.vars.push (n, t) }

end ICtx

/-- Bounded cartesian product: the `k` cheapest combinations, never the whole product. -/
private def kbest (k : Nat) : List (List Choice) → List (Array Choice)
  | [] => [#[]]
  | xs :: rest =>
    let tails := kbest k rest
    let combos := (xs.take k).flatMap fun x => tails.map fun t => (#[x] ++ t)
    let total (c : Array Choice) : Nat := c.foldl (fun acc x => acc + x.cost) 0
    ((combos.toArray.qsort fun a b => total a < total b).toList).take k

/-- Apply every alternative of a symbol to the argument tables. -/
def applyAlts (k : Nat) (alts : Array Alt) (argTabs : Array Table) : Table := Id.run do
  let mut out : Table := {}
  for alt in alts do
    if alt.params.size != argTabs.size then continue
    let perArg := (Array.zip alt.params argTabs).toList.map fun (p, t) => t.atMost p k
    if perArg.any List.isEmpty then continue
    for combo in kbest k perArg do
      out := out.add k alt.result
        { cost := alt.cost + combo.foldl (fun c x => c + x.cost) 0
          computable := alt.computable && combo.all (·.computable)
          expr := .node alt (combo.map (·.expr))
          transparentTop := alt.transparent }
  return out

/-- Numerals elaborate at any numeric type, so they are produced directly in every slot rather
than cast into place. -/
private def literalTable (k : Nat) (text : String) (tys : List Ty) : Table :=
  tys.foldl (fun t ty =>
    t.add k ty { cost := ty.level, computable := ty.isComputable,
                 expr := .lit text ty, transparentTop := false }) {}

mutual

partial def infer (ctx : ICtx) (e : Ast) : Table :=
  match e with
  | .num v _ => literalTable ctx.k (toString v) [.nat, .int, .rat, .real, .complex]
  | .dec w f _ =>
    [Ty.rat, .real, .complex].foldl (fun t ty =>
      t.add ctx.k ty { cost := ty.level, computable := ty.isComputable,
                       expr := .dec w f ty, transparentTop := false }) {}
  | .ident n _ =>
    match ctx.varTy? n with
    | some ty =>
      Table.add ctx.k {} ty
        { cost := 0, computable := ty.isComputable, expr := .var n ty, transparentTop := false }
    | none => applyAlts ctx.k (ctx.reg.find n 0) #[]
  | .app h args _ => applyAlts ctx.k (ctx.reg.find h args.size) (args.map (infer ctx))
  | .bin op l r _ => applyAlts ctx.k (ctx.reg.find op.key 2) #[infer ctx l, infer ctx r]
  | .un .neg x _ => applyAlts ctx.k (ctx.reg.find "neg" 1) #[infer ctx x]
  | .un .abs x _ => applyAlts ctx.k (ctx.reg.find "abs" 1) #[infer ctx x]
  | .fact cnt x _ => inferFact ctx cnt (infer ctx x)
  | .agg kind var lo hi loS hiS dv body _ => inferAgg ctx kind var lo hi loS hiS dv body
  | .rel .. => {}

/-- `n!!` is the double factorial, or two factorials; both readings are offered, the first more
cheaply. Longer runs can only be iterated factorials. -/
partial def inferFact (ctx : ICtx) (cnt : Nat) (arg : Table) : Table := Id.run do
  let single := ctx.reg.find "!" 1
  let mut iterated := arg
  for _ in [0:cnt] do
    iterated := applyAlts ctx.k single #[iterated]
  if cnt == 2 then
    let dbl := applyAlts ctx.k (ctx.reg.find "!!" 1) #[arg]
    -- The iterated reading is the fallback, so it costs more.
    let bumped : Table :=
      { slots := iterated.slots.map fun l => l.map fun c => { c with cost := c.cost + 2 } }
    return dbl.merge ctx.k bumped
  return iterated

partial def inferAgg (ctx : ICtx) (kind : AggKind) (var : String) (lo hi : Option Ast)
    (loStrict hiStrict : Bool) (dv : Option Ast) (body : Ast) : Table := Id.run do
  -- An integral ranges over the reals; every other binder is a natural index.
  let binderTy := if kind == .integral then Ty.real else Ty.nat
  let boundAt (a : Option Ast) : Option (List Choice) :=
    a.map fun x => (infer ctx x).atMost binderTy ctx.k
  let loCs := boundAt lo
  let hiCs := boundAt hi
  let dvCs := boundAt dv
  if [loCs, hiCs, dvCs].any (fun c => match c with | some l => l.isEmpty | none => false) then
    return {}
  let pick (c : Option (List Choice)) : Option Choice := c.bind List.head?
  let loC := pick loCs
  let hiC := pick hiCs
  let dvC := pick dvCs
  let boundCost := (#[loC, hiC, dvC].filterMap id).foldl (fun acc c => acc + c.cost) 0
  let bodyTab := infer (ctx.bind var binderTy) body
  let finite := hiC.isSome || dvC.isSome
  let allowed : List Ty :=
    match kind with
    | .integral => [.real, .complex]
    | _ => if finite then [.nat, .int, .rat, .real, .complex] else [.real, .complex]
  let mut out : Table := {}
  for ty in allowed do
    for c in bodyTab.get ty do
      let evaluable := finite && kind != .integral && ty.isComputable && c.computable
      out := out.add ctx.k ty
        { cost := c.cost + boundCost + ty.level + (if evaluable then 0 else 4)
          computable := evaluable
          expr := .agg kind var (loC.map (·.expr)) (hiC.map (·.expr)) (dvC.map (·.expr))
            loStrict hiStrict c.expr ty
          transparentTop := false }
  return out

end

/-! ## Goals -/

/-- A complete typing of a goal. -/
structure Typing where
  name : String
  params : Array (String × Ty)
  ret : Ty
  expr : TExpr
  cost : Nat
  computable : Bool
  /-- Auxiliary definitions the body calls, in dependency order. -/
  aux : Array (String × Array (String × Ty) × TExpr) := #[]
  /-- Set when the body had to be produced at a wider type and narrowed at the root. -/
  narrowedFrom : Option Ty := none
deriving Inhabited

namespace Typing

def fnTy (t : Typing) : FnTy := { args := t.params.map (·.2) |>.toList, ret := t.ret }

def imports (t : Typing) : Array String := t.expr.imports

end Typing

/-- The alternative that stands for a recursive call to the goal being defined. -/
def selfAlt (name : String) (args : List Ty) (ret : Ty) : Alt :=
  { key := name
    template := "«self»" ++ String.join ((List.range args.length).map fun i => s!" \{{i}}")
    params := args.toArray, result := ret, prec := 1023
    argPrec := Array.replicate args.length 1024 }

/-- Alternatives for a name defined elsewhere in the same input, one per result type its body can
have under the given parameter types. -/
def auxAlts (reg : Registry) (k : Nat) (d : Definition) (paramTys : Array Ty) : Array Alt :=
  Id.run do
    if paramTys.size != d.params.size then return #[]
    let ctx : ICtx := { reg, k, vars := Array.zip d.params paramTys }
    let tab := infer ctx d.body
    let mut out : Array Alt := #[]
    for ty in tab.types do
      out := out.push
        { key := d.name
          template := d.name ++ String.join ((List.range paramTys.size).map fun i => s!" \{{i}}")
          params := paramTys, result := ty
          computable := (tab.get ty).any (·.computable)
          prec := 1023, argPrec := Array.replicate paramTys.size 1024 }
    return out

/-- Cheapest evaluable body of an auxiliary definition, for the interpreter to call. -/
def auxEvalDef (reg : Registry) (k : Nat) (d : Definition) (paramTys : Array Ty) :
    Option (Array (String × Ty) × TExpr) :=
  if paramTys.size != d.params.size then none
  else
    let ctx : ICtx := { reg, k, vars := Array.zip d.params paramTys }
    let tab := infer ctx d.body
    let cands := (tab.types.map fun ty => tab.get ty).flatten.filter (·.computable)
    match (cands.toArray.qsort fun a b => a.cost < b.cost)[0]? with
    | some c => some (Array.zip d.params paramTys, normalizeNat c.expr)
    | none => none

/-- Type one goal at one requested signature, cheapest reading first. -/
def typeGoal (reg : Registry) (k : Nat) (g : Goal) (want : FnTy) : List Typing := Id.run do
  if want.args.length != g.main.params.size then return []
  let paramTys := want.args.toArray
  -- Aux definitions and the recursive self-reference are ordinary catalogue entries.
  let mut reg := reg
  let mut auxDefs : Array (String × Array (String × Ty) × TExpr) := #[]
  for d in g.aux do
    reg := { alts := reg.alts ++ auxAlts reg k d paramTys }
    if let some (ps, body) := auxEvalDef reg k d paramTys then
      auxDefs := auxDefs.push (d.name, ps, body)
  if g.main.recursive then
    reg := reg.add (selfAlt g.main.name want.args want.ret)
  let ctx : ICtx := { reg, k, vars := Array.zip g.main.params paramTys }
  let tab := infer ctx g.main.body
  let params := Array.zip g.main.params paramTys
  let mk (c : Choice) (from? : Option Ty) : Typing :=
    { name := g.main.name, params, ret := want.ret, expr := normalizeNat c.expr
      cost := c.cost + g.cost
      computable := c.computable, aux := auxDefs, narrowedFrom := from? }
  let direct := (tab.get want.ret).map (mk · none)
  -- Narrowed readings are always offered, not just as a fallback: a formula may typecheck at the
  -- requested type and still be wrong there, as when a closed form passes through negative
  -- intermediate values. They cost enough to be tried after every direct reading.
  let mut narrowed : List Typing := []
  for alt in Builtins.narrowings do
    if alt.result != want.ret then continue
    for c in tab.atMost alt.params[0]! k do
      if c.expr.ty != alt.params[0]! then continue
      narrowed := narrowed ++ [mk { c with
        cost := c.cost + 40 + alt.cost
        computable := c.computable && alt.computable
        expr := .node alt #[c.expr] } (some alt.params[0]!)]
  return ((direct ++ narrowed).toArray.qsort fun a b => a.cost < b.cost).toList

/-! ## Statements -/

private def propChoice (cost : Nat) (e : TExpr) : Choice :=
  { cost, computable := e.computable, expr := e, transparentTop := false }

/-- The `k` cheapest readings of `l op r`, each side at the same type. -/
private def relReadings (ctx : ICtx) (op : RelOp) (l r : Ast) : List Choice := Id.run do
  let lt := infer ctx l
  let rt := infer ctx r
  let mut out : List Choice := []
  for t in (Builtins.relSymbol op).2 do
    for combo in kbest ctx.k [lt.atMost t ctx.k, rt.atMost t ctx.k] do
      out := out ++ [propChoice (combo[0]!.cost + combo[1]!.cost + t.level)
        (.node (Builtins.relAlt op t) #[combo[0]!.expr, combo[1]!.expr])]
  return ((out.toArray.qsort fun a b => a.cost < b.cost).toList).take ctx.k

/-- The `k` cheapest conjunctions, one reading per conjunct. -/
private def conjoin (k : Nat) (parts : List (List Choice)) : List Choice :=
  (kbest k parts).filterMap fun combo =>
    combo[0]?.map fun first =>
      let e := combo[1:].toArray.foldl (fun acc c => TExpr.node Builtins.andAlt #[acc, c.expr])
        first.expr
      propChoice (combo.foldl (fun s c => s + c.cost) 0) e

/-- Members at least this big are not worth repeating, so an all-equal chain of them is written
with `List.Pairwise` instead. -/
private def bigMember : Nat := 5

/-- Readings of a relation chain. `a < b < c` is `a < b ∧ b < c`; an equality chain repeats its
smallest member, `a(n) = n^2 = n*n` becoming `a n = n ^ 2 ∧ a n = n * n`, unless every member is
big, in which case all of them are listed once under `List.Pairwise`. -/
def inferProp (ctx : ICtx) : Ast → List Choice
  | .rel h rest _ =>
    let items := #[h] ++ rest.map (·.2)
    let ops := rest.map (·.1)
    if ops.all (· == .eq) && items.size > 2 then
      if items.all (astSize · ≥ bigMember) then
        let tabs := items.map (infer ctx)
        let byTy := [Ty.nat, .int, .rat, .real, .complex].flatMap fun t =>
          (kbest ctx.k (tabs.toList.map (·.atMost t ctx.k))).map fun combo =>
            propChoice (combo.foldl (fun s c => s + c.cost) t.level)
              (.node (Builtins.pairwiseAlt t items.size) (combo.map (·.expr)))
        ((byTy.toArray.qsort fun a b => a.cost < b.cost).toList).take ctx.k
      else
        let pivot := (List.range items.size).foldl (fun best i =>
          if astSize items[i]! < astSize items[best]! then i else best) 0
        let pairs := (List.range items.size).filter (· != pivot) |>.map fun i =>
          if i < pivot then relReadings ctx .eq items[i]! items[pivot]!
          else relReadings ctx .eq items[pivot]! items[i]!
        conjoin ctx.k pairs
    else
      conjoin ctx.k ((List.range ops.size).map fun i => relReadings ctx ops[i]! items[i]! items[i+1]!)
  | _ => []

/-- A guard such as `n > 1`, as a hypothesis on the bound variable. -/
private def guardExpr (reg : Registry) (g : Guard) (t : Ty) : Option TExpr :=
  if !t.isNumeric || (t == .nat && g.bound < 0) then none
  else
    let lit : TExpr :=
      if g.bound ≥ 0 then .lit (toString g.bound) t
      else match (reg.find "neg" 1).find? (·.params[0]? == some t) with
        | some neg => .node neg #[.lit (toString (-g.bound)) t]
        | none => .lit (toString g.bound) t
    some (.node (Builtins.relAlt g.op t) #[.var g.var t, lit])

/-- Type one statement with its variables at `want.args`, cheapest reading first. Guards become
hypotheses, so `a(n) > 0 for n > 1` reads `∀ n : ℕ, n > 1 → a n > 0`. -/
def typeProp (reg : Registry) (k : Nat) (g : PropGoal) (want : FnTy) : List Typing := Id.run do
  if want.args.length != g.vars.size then return []
  let params := Array.zip g.vars want.args.toArray
  let ctx : ICtx := { reg, k, vars := params }
  let hyps := g.guards.filterMap fun gd =>
    (params.find? (·.1 == gd.var)).bind fun (_, t) => guardExpr reg gd t
  return (inferProp ctx g.rel).map fun c =>
    let body := hyps.foldr (fun h acc => TExpr.node Builtins.impAlt #[h, acc]) c.expr
    { name := "statement", params, ret := .prop, expr := body, cost := c.cost + g.cost
      computable := body.computable }

end
end GenExpr
