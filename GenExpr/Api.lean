import GenExpr.LeanEngine

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

/-- How readings are checked. `check` runs against the values; `typecheck` only elaborates and
answers `none` when the reading is fine or when no type checker is available. -/
structure Checker (m : Type → Type) where
  check : Goal → Typing → m VerifyReport
  typecheck : Typing → m (Option Reject)

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
      let mut chosen : Option (Typing × VerifyReport) := none
      if !req.values.isEmpty then
        for t in ts.filter (·.computable) do
          let r ← chk.check g t
          if r.accepted then
            chosen := some (t, r)
            break
          if let some why := r.reason then rejected := rejected.push (g.main.span, why)
      -- With nothing to check against — no values, or no reading that can be run — the
      -- cheapest reading that type checks stands, unverified.
      if chosen.isNone && (req.values.isEmpty || ts.all (!·.computable)) then
        for t in ts do
          match ← chk.typecheck t with
          | some why => rejected := rejected.push (g.main.span, why)
          | none =>
            let reason := if req.values.isEmpty then none else some Reject.notComputable
            chosen := some (t, { accepted := false, reason })
            break
      if let some (t, rep) := chosen then
        let spans := g.spans
        items := items.push
          { name := t.name, ty := t.fnTy
            body := renderBody req.style t
            decl := renderDef req.style t t.name rep.patched
            aux := t.aux.map fun (n, ps, b) => renderAux req.style n ps b
            imports := typingImports t
            spans, text := joinSpans sc.input spans
            computable := t.computable
            baseCases := rep.patched
            report := rep, cost := t.cost }
  return { items, rejected }

/-- Run the whole pipeline, checking values with the interpreter. Pure. -/
def analyze (req : Request) : Result :=
  analyzeWith (m := Id)
    { check := fun g t => verify req.verify t req.values g.guards req.tables
      typecheck := fun _ => none }
    req

/-- Run the whole pipeline with the engine `req.verify.engine` names. The Lean engines need a
session, which caches environments across requests. -/
def run (session : LeanEngine.Session) (req : Request) : IO Result :=
  if !req.verify.engine.usesLean then pure (analyze req)
  else
    analyzeWith
      { check := fun g t => session.check req.verify t req.values g.guards req.tables
        typecheck := fun t =>
          if session.cfg.elabNoncomputable || t.computable then session.typecheck t req.tables
          else pure none }
      req

end GenExpr
