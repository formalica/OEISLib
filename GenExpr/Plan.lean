import GenExpr.Frontend.Raw.Segmenter

/-!
Scope resolution: turning chosen fragments into definitions the typer can work on.

Each fragment is classified by shape — definition, proposition, domain guard, stated value, or a
bare expression — and the definitions are then linked into a dependency graph. Asking for `a` in

    b(n) = n^2+1; a(n) = b(b(b(n)))

yields `a` as the goal with `b` as an auxiliary definition, in dependency order. Self-reference is
recursion and is kept; mutual recursion is rejected with a reason rather than silently dropped.

Nothing here looks at types: this stage only decides *what* is being defined, and out of *which*
parts.
-/

namespace GenExpr

open GenExpr.Raw

structure PlanConfig where
  /-- Preferred names for the result, most preferred first. -/
  names : Array String := #[]
  /-- Whether a definition whose head is not in `names` may still be the goal. -/
  allowOtherHeads : Bool := true
  /-- Name given to a goal built from an anonymous expression. -/
  defaultName : String := "f"
  /-- How many parameters the result should take. -/
  arity : Nat := 1
deriving Inhabited

/-- What a fragment says. -/
inductive FragKind where
  /-- `f(x…) = rhs`. An equality chain contributes one of these per right-hand side. -/
  | definition (head : String) (params : Array String) (rhs : Ast)
  /-- A relation that does not define anything: a candidate proposition. -/
  | relation (e : Ast)
  /-- `n > 1`, `n >= 2`: restricts the domain of a neighbouring definition. -/
  | guard (var : String) (op : RelOp) (bound : Int)
  /-- `a(0) = 1`: a single value stated in the text. -/
  | pointValue (head : String) (args : Array Int) (value : Ast)
  /-- A bare expression, which becomes a function of its unbound variables. -/
  | bare (e : Ast)
deriving Repr, Inhabited

/-- One candidate body for one name. Several readings of the same fragment produce several of
these; the typer ranks them. -/
structure Definition where
  name : String
  params : Array String
  body : Ast
  span : Span
  cost : Nat
  recursive : Bool
deriving Inhabited

structure Guard where
  var : String
  op : RelOp
  bound : Int
  span : Span
deriving Inhabited, Repr

/-- A goal is a definition plus everything needed to elaborate it. -/
structure Goal where
  main : Definition
  /-- Auxiliary definitions in dependency order: each depends only on earlier ones. -/
  aux : Array Definition
  guards : Array Guard
  cost : Nat
  /-- How well the goal matches what was asked for: the position of its name among the requested
  ones, then other definitions, then anonymous expressions. -/
  rank : Nat
  /-- Source order, so that equal candidates keep the order they were written in. -/
  order : Nat
deriving Inhabited

namespace Goal

/-- Byte ranges of every part of the input this goal is built from, in source order. -/
def spans (g : Goal) : Array Span :=
  (((g.aux.map (·.span)).push g.main.span ++ g.guards.map (·.span)).qsort
    fun a b => a.start < b.start)

end Goal

structure PlanResult where
  kinds : Array (Span × Nat × FragKind)
  goals : Array Goal
  rejected : Array (Span × Reject)
deriving Inhabited

namespace PlanResult

/-- Values the text states outright, such as `a(0) = 1`. They are candidate base cases. -/
def pointValues (p : PlanResult) : Array (String × Array Int × Ast) :=
  p.kinds.filterMap fun (_, _, k) =>
    match k with
    | .pointValue name args value => some (name, args, value)
    | _ => none

/-- Relations that define nothing; these are the candidates when a `Prop` is wanted. -/
def relations (p : PlanResult) : Array (Span × Ast) :=
  p.kinds.filterMap fun (sp, _, k) =>
    match k with
    | .relation e => some (sp, e)
    | _ => none

end PlanResult

/-! ## Fragment classification -/

/-- `f(x, y)` or `c`, with all arguments plain names. -/
private def definitionPattern? : Ast → Option (String × Array String)
  | .ident name _ => some (name, #[])
  | .app name args _ =>
    if args.all (fun a => a matches .ident ..) then
      some (name, args.filterMap fun | .ident v _ => some v | _ => none)
    else none
  | _ => none

/-- `a(0)`, `T(1, 2)`: all arguments literal. -/
private def pointPattern? : Ast → Option (String × Array Int)
  | .app name args _ =>
    let vals := args.filterMap intLit?
    if vals.size == args.size && !args.isEmpty then some (name, vals) else none
  | _ => none

private def isOrderRel : RelOp → Bool
  | .lt | .le | .gt | .ge => true
  | _ => false

private def flipRel : RelOp → RelOp
  | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le | r => r

/-- `n > 1` or `1 < n`, in either orientation. -/
private def guardOf : Ast → Option (String × RelOp × Int)
  | .rel h rest _ =>
    if rest.size != 1 then none
    else
      let (op, r) := rest[0]!
      if !isOrderRel op then none
      else
        match h, intLit? r with
        | .ident v _, some k => some (v, op, k)
        | _, _ =>
          match intLit? h, r with
          | some k, .ident v _ => some (v, flipRel op, k)
          | _, _ => none
  | _ => none

def classifyAst (e : Ast) : Array FragKind :=
  match e with
  | .rel h rest _ =>
    if rest.all (·.1 == .eq) then
      match definitionPattern? h with
      | some (name, params) => rest.map fun (_, rhs) => .definition name params rhs
      | none =>
        match pointPattern? h with
        | some (name, args) =>
          if rest.size == 1 then #[.pointValue name args rest[0]!.2] else #[.relation e]
        | none => #[.relation e]
    else
      match guardOf e with
      | some (v, op, k) => #[.guard v op k]
      | none => #[.relation e]
  | _ => #[.bare e]

/-! ## Definition graph -/

private def mkDefinition (name : String) (params : Array String) (body : Ast) (span : Span)
    (cost : Nat) : Definition :=
  { name, params, body, span, cost, recursive := (referencedNames body).contains name }

/-- Cheapest definition for each referenced name, in dependency order, excluding the goal itself
(a self-reference is recursion, not a dependency). -/
private def auxClosure (defs : Array Definition) (main : Definition) :
    Except Reject (Array Definition) := Id.run do
  let pick (n : String) : Option Definition :=
    ((defs.filter fun d => d.name == n).qsort fun a b => a.cost < b.cost)[0]?
  let isDefined (n : String) : Bool := defs.any fun d => d.name == n
  let mut needed : Array String := #[]
  let mut queue : Array String :=
    (referencedNames main.body).filter fun n => n != main.name && isDefined n
  let mut fuel := defs.size + 1
  while !queue.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let mut next : Array String := #[]
    for n in queue do
      if needed.contains n then continue
      needed := needed.push n
      let some d := pick n | return .error (.hole n)
      if (referencedNames d.body).contains main.name then
        return .error (.mutualRecursion [main.name, n])
      for m in referencedNames d.body do
        if m != n && m != main.name && isDefined m && !needed.contains m then
          next := next.push m
    queue := next
  let mut ordered : Array Definition := #[]
  let mut rounds := needed.size + 1
  while ordered.size < needed.size && rounds > 0 do
    rounds := rounds - 1
    let before := ordered.size
    for n in needed do
      if ordered.any fun d => d.name == n then continue
      let some d := pick n | return .error (.hole n)
      let deps := (referencedNames d.body).filter fun m => m != n && needed.contains m
      if deps.all fun m => ordered.any fun e => e.name == m then
        ordered := ordered.push d
    if ordered.size == before then return .error (.mutualRecursion needed.toList)
  return .ok ordered

/-! ## Planning -/

/-- Classify every reading of every chosen fragment, then build one goal per candidate main
definition, cheapest first. -/
def plan (sc : Scan) (cfg : PlanConfig) : PlanResult := Id.run do
  let mut kinds : Array (Span × Nat × FragKind) := #[]
  for seg in sc.chosen do
    for r in seg.alts do
      for k in classifyAst r.ast do
        kinds := kinds.push (seg.span, r.cost, k)

  let mut defs : Array Definition := #[]
  let mut guards : Array Guard := #[]
  for (span, cost, k) in kinds do
    match k with
    | .definition name params rhs => defs := defs.push (mkDefinition name params rhs span cost)
    | .guard var op bound => guards := guards.push { var, op, bound, span }
    | _ => pure ()

  -- An expression that states no equation becomes a function of the names it leaves unbound.
  -- Not, however, when the text plainly sets out to define what was asked for: then a leftover
  -- fragment of a line we failed to read must not stand in for it.
  let textDefines := cfg.names.any fun n => sc.cls.prescan.heads.contains n
  let mut anon : Array Definition := #[]
  if !textDefines then
    for (span, cost, k) in kinds do
      if let .bare e := k then
        let free := (nameInfo sc.cls #[] e).unbound
        if free.size == cfg.arity then
          let name := cfg.names[0]?.getD cfg.defaultName
          anon := anon.push (mkDefinition name free e span (cost + 1))

  -- Rank: requested names in order, then any other definition, then anonymous expressions.
  let ranked : Array (Nat × Definition) :=
    defs.map (fun d =>
      match cfg.names.findIdx? (· == d.name) with
      | some i => (i, d)
      | none => (if cfg.allowOtherHeads then 100 else 1000, d))
      ++ anon.map (fun d => (200, d))

  let mut goals : Array Goal := #[]
  let mut rejected : Array (Span × Reject) := #[]
  let mut order := 0
  for (rank, d) in ranked do
    order := order + 1
    if rank ≥ 1000 then continue
    if d.params.size != cfg.arity then
      rejected := rejected.push (d.span, .notDefinitionForm)
      continue
    match auxClosure defs d with
    | .error e => rejected := rejected.push (d.span, e)
    | .ok aux =>
      let gs := guards.filter fun g => d.params.contains g.var
      goals := goals.push
        { main := d, aux, guards := gs, rank, order
          cost := aux.foldl (fun c a => c + a.cost) d.cost }

  -- Only report what no chosen fragment already explains.
  let covered (sp : Span) : Bool :=
    sc.chosen.any fun g => g.span.start ≤ sp.start && sp.stop ≤ g.span.stop
  for seg in sc.all do
    if covered seg.span then continue
    for reason in seg.reasons do
      if reason != .bareAtom then rejected := rejected.push (seg.span, reason)

  let sorted := goals.qsort fun a b =>
    a.rank < b.rank ||
      (a.rank == b.rank && (a.cost < b.cost || (a.cost == b.cost && a.order < b.order)))
  return { kinds, goals := sorted, rejected }

/-! ## Propositions -/

/-- A statement to check: a relation chain over its free variables, under the guards on them. -/
structure PropGoal where
  rel : Ast
  /-- Free variables in order of first occurrence; they become the `∀` binders. -/
  vars : Array String
  guards : Array Guard
  span : Span
  cost : Nat
deriving Inhabited

namespace PropGoal

def spans (g : PropGoal) : Array Span :=
  ((g.guards.map (·.span)).push g.span).qsort fun a b => a.start < b.start

end PropGoal

/-- Statements the input makes, one group per fragment, readings cheapest first. A chain that
defines something (`a(n) = n^2 = n*n`) is a statement too, but only once every name it applies
is `known`: a theorem cannot have a hole, so `a` must already be a function the caller supplied. -/
def planProps (sc : Scan) (arity : Nat) (known : String → Bool) :
    Array (Array PropGoal) × Array (Span × Reject) := Id.run do
  let mut guards : Array Guard := #[]
  for seg in sc.chosen do
    for r in seg.alts do
      if let some (var, op, bound) := guardOf r.ast then
        guards := guards.push { var, op, bound, span := seg.span }
  let mut groups : Array (Array PropGoal) := #[]
  let mut rejected : Array (Span × Reject) := #[]
  for seg in sc.chosen do
    let mut group : Array PropGoal := #[]
    let mut why : Option Reject := none
    for r in seg.alts.toArray.qsort (fun a b => a.cost < b.cost) do
      unless r.ast matches .rel .. do continue
      if (guardOf r.ast).isSome then continue
      match (appliedHeads r.ast).find? (!known ·) with
      | some h =>
        why := some (.hole h)
        continue
      | none => pure ()
      let vars := (nameInfo sc.cls #[] r.ast).unbound
      if vars.size != arity then
        why := some (.tooManyFreeVars vars.toList)
        continue
      group := group.push
        { rel := r.ast, vars, guards := guards.filter (vars.contains ·.var), span := seg.span
          cost := r.cost }
    if !group.isEmpty then groups := groups.push group
    else if let some w := why then rejected := rejected.push (seg.span, w)
  -- Fragments that never made it into the cover still explain what went wrong.
  for seg in sc.all do
    if sc.chosen.any fun g => g.span.start ≤ seg.span.start && seg.span.stop ≤ g.span.stop then
      continue
    for reason in seg.reasons do
      if reason != .bareAtom then rejected := rejected.push (seg.span, reason)
  return (groups, rejected)

end GenExpr
