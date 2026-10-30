module
public import GenExprTests
public meta import GenExprTests
public import GenExprTests.Cases
public meta import GenExprTests.Cases

/-!
Entry point of `lake exe genexpr-test`.

The `#guard` suites already fail `lake build`; this runner shows the acceptance corpus as one
table and is the only place the Lean engines run, since they need Mathlib loaded at run time.

    lake exe genexpr-test [--engine internal|lean|internalThenLean|crossCheck]
                          [--elab-noncomputable] [--timeout MS] [--filter SUBSTRING] [--list]
    lake exe genexpr-test --check-imports [--filter SUBSTRING]

`--elab-noncomputable` also type checks readings that cannot be run (`∑'`, `∫`, `Real.sin`); it
needs the analysis imports, which roughly doubles the environment's memory.

`--check-imports` elaborates every catalogue alternative, and every declaration the corpus
produces, under exactly the imports it declares. Each import set runs in a child process, since
an imported environment is never freed.
-/

open GenExpr GenExprTests
public section

structure Opts where
  filter : Option String := none
  list : Bool := false
  engine : Engine := .internal
  elabNoncomputable : Bool := false
  checkImports : Bool := false
  timeoutMs : Nat := 2000

def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--filter" :: p :: rest, o => parseArgs rest { o with filter := some p }
  | "--list" :: rest, o => parseArgs rest { o with list := true }
  | "--check-imports" :: rest, o => parseArgs rest { o with checkImports := true }
  | "--elab-noncomputable" :: rest, o => parseArgs rest { o with elabNoncomputable := true }
  | "--timeout" :: ms :: rest, o =>
    match ms.toNat? with
    | some n => parseArgs rest { o with timeoutMs := n }
    | none => .error s!"--timeout expects milliseconds, got '{ms}'"
  | "--engine" :: e :: rest, o =>
    match Engine.ofString? e with
    | some engine => parseArgs rest { o with engine }
    | none => .error s!"unknown engine '{e}'"
  | a :: _, _ => .error s!"unknown argument '{a}'"

private def selects (filter : Option String) (c : Cases.Case) : Bool :=
  match filter with
  | some p => (c.name.splitOn p).length > 1 || (c.input.splitOn p).length > 1
  | none => true

def runCorpus (o : Opts) (selected : Array Cases.Case) : IO UInt32 := do
  let session ← LeanEngine.Session.create
    { elabNoncomputable := o.elabNoncomputable, pointTimeoutMs := o.timeoutMs
      baseImports := if o.elabNoncomputable then Builtins.allImports
                     else Builtins.computableImports }
  IO.println s!"engine: {o.engine.name}"
  let mut results : Array GenExprTests.Result := #[]
  for c in selected do
    if c.leanOnly && !o.engine.usesLean then
      IO.println s!"skip {c.name} (needs a Lean engine)"
      continue
    let t0 ← IO.monoMsNow
    let r ← Cases.runCaseWith session o.engine c
    let dt := (← IO.monoMsNow) - t0
    IO.println s!"{if r.isEmpty then "ok  " else "FAIL"} {c.name}  ({dt} ms)"
    results := results.push r
  if o.engine.usesLean then IO.println s!"lean: {← session.stats.get}"
  report "corpus" results

/-- Groups `(imports, label, block)` triples by import set, preserving first-seen order. -/
private def groupByImports (xs : Array (Array String × String × String)) :
    Array (Array String × Array (String × String)) :=
  xs.foldl (init := #[]) fun acc (im, label, block) =>
    match acc.findIdx? (·.1 == im) with
    | some j => acc.modify j fun (i, es) => (i, es.push (label, block))
    | none => acc.push (im, #[(label, block)])

private def checkGroups (suite : String)
    (groups : Array (Array String × Array (String × String))) : IO UInt32 := do
  let exe ← IO.appPath
  let mut results : Array GenExprTests.Result := #[]
  for (imports, entries) in groups do
    let t0 ← IO.monoMsNow
    let replies ← LeanEngine.elabIsolated exe imports (entries.map (·.2))
    IO.println s!"-- {imports.size} import(s), {entries.size} declaration(s), {(← IO.monoMsNow) - t0} ms"
    for ((label, _), reply) in entries.zip replies do
      IO.println s!"{if reply.isNone then "ok  " else "FAIL"} {label}"
      results := results.push <| match reply with
        | none => #[]
        | some e => #[{ test := label, detail := s!"imports {imports}\n  {e}" }]
  report suite results

/-- Each corpus declaration, with the auxiliaries and table stubs it needs, under exactly the
imports `Item.imports` reports. -/
private def corpusBlocks (selected : Array Cases.Case) : Array (Array String × String × String) :=
  selected.foldl (init := #[]) fun acc c =>
    match (analyze (Cases.request c .internal)).items[0]? with
    | none => acc
    | some item =>
      let stubs := c.tables.map fun (n, rows) => LeanEngine.renderStub n rows 0
      let ns := s!"Corpus{acc.size}"
      let block := s!"namespace {ns}\n\n" ++
        String.intercalate "\n\n" (stubs ++ item.aux ++ #[item.decl]).toList ++ s!"\n\nend {ns}"
      acc.push (item.imports, c.name, block)

def checkImports (selected : Array Cases.Case) : IO UInt32 := do
  let alts := Builtins.standard.alts ++ Builtins.narrowings
  let groups := LeanEngine.catalogueProbes alts
  IO.println s!"catalogue: {alts.size} alternative(s) in {groups.size} import set(s)"
  let a ← checkGroups "catalogue imports" groups
  let corpus := groupByImports (corpusBlocks selected)
  IO.println s!"corpus: {corpus.size} import set(s)"
  let b ← checkGroups "corpus imports" corpus
  return if a == 0 && b == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  let code ← match args with
    | ["--elab-child", path] => LeanEngine.childMain path
    | _ =>
      match parseArgs args {} with
      | .error e =>
        IO.eprintln e
        pure 2
      | .ok o =>
        let selected := Cases.corpus.filter (selects o.filter)
        if o.list then
          for c in selected do IO.println s!"{c.name}  <-  {c.input}"
          pure 0
        else if o.checkImports then checkImports selected
        else runCorpus o selected
  -- A Lean evaluation that timed out was abandoned, not stopped, and its thread would keep the
  -- process alive after `main` returns.
  IO.Process.exit code.toUInt8
end
