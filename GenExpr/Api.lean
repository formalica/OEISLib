module
public import GenExpr.LeanEngine
public meta import GenExpr.LeanEngine

/-!
The public entry point.

`analyze` runs the whole pipeline — scan, segment, plan, type, render, check against values — and
is pure: it checks values with the interpreter and needs no Lean environment. `run` is the same
pipeline in `IO`, checking with whichever engine `Request.verify.engine` names, Lean included.
Both are `analyzeWith` over a different `Checker`, so they cannot diverge on anything but how a
reading is checked.

Nothing here mentions OEIS. A caller that has sequences supplies them as `custom` alternatives or
as `tables` of known points.
-/

namespace GenExpr
public section

open GenExpr.Raw

structure Request where
  input : String
  /-- Names to prefer for the result, most preferred first. -/
  names : Array String := #[]
  /-- Signatures to try, in order; the first that yields a verified reading wins. -/
  types : Array FnTy := #[{ args := [.nat], ret := .nat }]
  /-- Known values, in the order verification should use them. -/
  values : Array (Array Int × Int) := #[]
  /-- Extra catalogue entries. These compete with the built-ins rather than replacing them. -/
  custom : Array Alt := #[]
  /-- Catalogue keys to drop, so a caller can override a built-in outright. -/
  removeBuiltins : Array String := #[]
  /-- Functions known only by data points; a call outside the table proves nothing. -/
  tables : Array (String × Array (Array Int × Int)) := #[]
  verify : VerifyConfig := {}
  /-- Readings kept per result type at each node. -/
  beam : Nat := 4
  /-- Keep every reading that verifies rather than stopping at the first. -/
  allResults : Bool := false
  style : RenderStyle := {}
deriving Inhabited

/-- One formalization. `report.accepted` says whether it was verified against the values;
a non-computable reading is returned unverified, flagged by `computable := false`. -/
structure Item where
  name : String
  ty : FnTy
  /-- The body alone, with `«self»` for recursion. This is what a database should store: it can
  be re-rendered under any name. -/
  body : String
  /-- A ready-to-paste declaration. -/
  decl : String
  /-- Auxiliary declarations, in dependency order. -/
  aux : Array String
  imports : Array String
  /-- Exactly the parts of the input this was built from. -/
  spans : Array Span
  text : String
  computable : Bool
  /-- Values supplied as base cases, which the declaration lists explicitly. -/
  baseCases : Array (Array Int × Int)
  report : VerifyReport
  cost : Nat
deriving Inhabited

structure Result where
  items : Array Item := #[]
  /-- Everything tried and rejected, with the reason. -/
  rejected : Array (Span × Reject) := #[]
deriving Inhabited

/-- How readings are checked. `check` runs a reading against points; `typecheck` only
elaborates, answering with the recursion rung that elaborated, or `none` when no type checker
is available. -/
structure Checker (m : Type → Type) where
  check : VerifyConfig → Typing → Array (Array Int × Int) → Array Guard → m VerifyReport
  typecheck : Typing → m (Except Reject (Option RecForm))

/-- A function known only by its values still needs a catalogue entry so that the parser treats
it as a call and the typer knows its shape. -/
private def tableAlt (name : String) (tbl : Array (Array Int × Int)) : Alt :=
  let arity := (tbl[0]?.map fun (a, _) => a.size).getD 1
  let ret := if tbl.any (fun (_, v) => v < 0) then Ty.int else Ty.nat
  { key := name
    template := name ++ String.join ((List.range arity).map fun i => s!" \{{i}}")
    params := Array.replicate arity .nat, result := ret, prec := 1023
    argPrec := Array.replicate arity 1024 }

private def spanText (inp : Input) (sp : Span) : String :=
  let bytes := inp.bytes
  let idx (b : Nat) : Nat := (bytes.findIdx? (· == b)).getD 0
  inp.extract (idx sp.start) (idx sp.stop)

private def joinSpans (inp : Input) (spans : Array Span) : String :=
  String.intercalate " … " (spans.toList.map (spanText inp))

/-- Try the readings of one goal: the first computable one that verifies, or — with nothing to
check against, or nothing that can be run — the cheapest one that type checks, unverified. -/
private def choose [Monad m] (chk : Checker m) (cfg : VerifyConfig) (ts : List Typing)
    (points : Array (Array Int × Int)) (guards : Array Guard) (span : Span) :
    m (Option (Typing × VerifyReport) × Array (Span × Reject)) := do
  let mut rejected : Array (Span × Reject) := #[]
  if !points.isEmpty then
    for t in ts.filter (·.computable) do
      let r ← chk.check cfg t points guards
      if r.accepted then return (some (t, r), rejected)
      if let some why := r.reason then rejected := rejected.push (span, why)
  if points.isEmpty || ts.all (!·.computable) then
    for t in ts do
      match ← chk.typecheck t with
      | .error why => rejected := rejected.push (span, why)
      | .ok form =>
        let reason := if points.isEmpty then none else some Reject.notComputable
        return (some (t, { accepted := false, reason, recForm := form }), rejected)
  return (none, rejected)

private def mkItem (st : RenderStyle) (inp : Input) (t : Typing) (rep : VerifyReport)
    (spans : Array Span) : Item :=
  let isProp := t.ret == .prop
  { name := t.name, ty := t.fnTy
    body := if isProp then renderStatement st t else renderBody st t
    decl := renderDef st t t.name rep.patched (rep.recForm.getD (recFormOf t))
    aux := t.aux.map fun (n, ps, b) => renderAux st n ps b
    imports := typingImports t
    spans, text := joinSpans inp spans
    computable := t.computable
    baseCases := rep.patched
    report := rep, cost := t.cost }

/-- The pipeline, parameterised by how readings are checked. -/
def analyzeWith [Monad m] (chk : Checker m) (req : Request) : m Result := do
  let reg :=
    (Builtins.standard.merge (req.custom ++ req.tables.map fun (n, t) => tableAlt n t)
      req.removeBuiltins)
  let cls : Classifier := { functions := reg.names ++ req.names, values := reg.constants }
  let sc := scan cls { maxFreeVars := req.types.foldl (fun m t => max m t.arity) 1 } req.input
  let mut items : Array Item := #[]
  let mut rejected : Array (Span × Reject) := #[]
  let mut plannedArities : Array Nat := #[]
  for want in req.types do
    if !items.isEmpty && !req.allResults then break
    let arity := want.arity
    if want.ret == .prop then
      -- Each statement in the input is checked on its own and returned on its own.
      let (groups, rej) := planProps sc arity reg.names.contains
      rejected := rejected ++ rej
      -- A statement holds or not at each point: expected `1`, and nothing to patch.
      let points := req.values.map fun (args, _) => (args, (1 : Int))
      let cfg := { req.verify with allowedFailures := 0 }
      for group in groups do
        let ts := group.toList.flatMap fun g => typeProp reg req.beam g want
        let ts := (ts.toArray.qsort fun a b => a.cost < b.cost).toList
        let span := group[0]!.span
        if ts.isEmpty then
          rejected := rejected.push (span, .typeUnachievable .prop)
          continue
        let (chosen, rej) ← choose chk cfg ts points #[] span
        rejected := rejected ++ rej
        if let some (t, rep) := chosen then
          let g := (group.find? fun g => g.vars.size == t.params.size).getD group[0]!
          items := items.push (mkItem req.style sc.input t rep g.spans)
      continue
    let p := plan sc { names := req.names, arity }
    if !plannedArities.contains arity then
      plannedArities := plannedArities.push arity
      rejected := rejected ++ p.rejected
    for g in p.goals do
      if !items.isEmpty && !req.allResults then break
      let ts := typeGoal reg req.beam g want
      if ts.isEmpty then
        rejected := rejected.push (g.main.span, .typeUnachievable want.ret)
        continue
      let (chosen, rej) ← choose chk req.verify ts req.values g.guards g.main.span
      rejected := rejected ++ rej
      if let some (t, rep) := chosen then
        items := items.push (mkItem req.style sc.input t rep g.spans)
  return { items, rejected }

/-- Run the whole pipeline, checking values with the interpreter. Pure. -/
def analyze (req : Request) : Result :=
  analyzeWith (m := Id)
    { check := fun cfg t points guards => verify cfg t points guards req.tables
      typecheck := fun _ => .ok none }
    req

/-- Run the whole pipeline with the engine `req.verify.engine` names. The Lean engines need a
session, which caches environments across requests. -/
def run (session : LeanEngine.Session) (req : Request) : IO Result :=
  if !req.verify.engine.usesLean then pure (analyze req)
  else
    analyzeWith
      { check := fun cfg t points guards => session.check cfg t points guards req.tables
        typecheck := fun t => do
          if !(session.cfg.elabNoncomputable || t.computable) then return .ok none
          return (← session.typecheck t req.tables).map some }
      req

end
end GenExpr
