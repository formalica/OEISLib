module
public import Lean
public meta import Lean
public import GenExpr.Verify
public meta import GenExpr.Verify
public import GenExpr.Render
public meta import GenExpr.Render

/-!
Verification by Lean itself.

The candidate is rendered exactly as it will be emitted, elaborated in an in-memory environment,
and evaluated through a small probe declaration — no files are written. Mathlib is loaded at run
time with `importModules`, never imported by this library, so `GenExpr` keeps building without it.

Three facts about the runtime shape the design:

* **imports are expensive and never freed.** Importing a handful of modules takes seconds;
  importing all of Mathlib took minutes and gigabytes, and an environment imported with
  initializers enabled stays in memory for the life of the process. So one shared environment
  is imported up front (`baseImports`) and reused for every candidate it covers. Checking that
  declared imports are *sufficient* needs a fresh environment per import set, which is why
  `checkImportsIsolated` does it in child processes;
* **running code cannot be interrupted.** A runaway evaluation is abandoned after its timeout,
  and its thread keeps the process alive, so callers must end with `IO.Process.exit`;
* **`enableInitializersExecution` is cleared by every import**, so it is re-armed each time.

The verification policy itself is `GenExpr.runPolicy`, shared with the interpreter.
-/

namespace GenExpr.LeanEngine
public section

open Lean

structure Config where
  /-- Imported once into the shared environment. The default covers every computable reading;
  use `Builtins.allImports` together with `elabNoncomputable`. -/
  baseImports : Array String := Builtins.computableImports
  pointTimeoutMs : Nat := 2000
  maxHeartbeats : Nat := 400000
  /-- Elaborate readings that cannot be evaluated, as a type check. Their analysis imports are
  heavy, so this is off unless asked for. -/
  elabNoncomputable : Bool := false
  style : RenderStyle := {}
deriving Inhabited

structure Stats where
  imports : Nat := 0
  importMs : Nat := 0
  elaborations : Nat := 0
  elabMs : Nat := 0
  evaluations : Nat := 0
  timeouts : Nat := 0
deriving Inhabited

instance : ToString Stats where
  toString s :=
    s!"{s.imports} import(s) in {s.importMs} ms, {s.elaborations} elaboration(s) in " ++
      s!"{s.elabMs} ms, {s.evaluations} evaluation(s), {s.timeouts} timeout(s)"

structure Session where
  cfg : Config
  envs : IO.Ref (Array (Array String × Environment))
  stats : IO.Ref Stats
  counter : IO.Ref Nat

/-! ## Unsafe primitives -/

private unsafe def enableInitUnsafe : IO Unit := do
  enableInitializersExecution

@[implemented_by enableInitUnsafe]
private opaque enableInit : IO Unit

private unsafe def loadProbeUnsafe (env : Environment) (opts : Options) (n : Name) :
    Except String (Array Int → String) :=
  env.evalConst (Array Int → String) opts n (checkMeta := false)

@[implemented_by loadProbeUnsafe]
private opaque loadProbe (env : Environment) (opts : Options) (n : Name) :
    Except String (Array Int → String)

/-! ## Session -/

/-- Library directories of the workspace and its packages; used when `LEAN_PATH` is unset. -/
private def workspaceLibDirs : IO (List System.FilePath) := do
  let mut out : List System.FilePath := []
  let own : System.FilePath := ".lake" / "build" / "lib" / "lean"
  if ← own.isDir then out := out ++ [own]
  let pkgs : System.FilePath := ".lake" / "packages"
  if ← pkgs.isDir then
    for e in ← pkgs.readDir do
      let d := e.path / ".lake" / "build" / "lib" / "lean"
      if ← d.isDir then out := out ++ [d]
  return out

def Session.create (cfg : Config := {}) : IO Session := do
  let extra ← if (← IO.getEnv "LEAN_PATH").isSome then pure [] else workspaceLibDirs
  initSearchPath (← findSysroot) extra
  return { cfg, envs := ← IO.mkRef #[], stats := ← IO.mkRef {}, counter := ← IO.mkRef 0 }

private def sortDedup (xs : Array String) : Array String :=
  (xs.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]).qsort (· < ·)

/-- An environment containing at least `needed`, built once per import set. -/
def Session.envFor (s : Session) (needed : Array String) : IO Environment := do
  let want := sortDedup (s.cfg.baseImports ++ needed)
  let hit := (← s.envs.get).find? fun (got, _) => want.all got.contains
  if let some (_, env) := hit then return env
  let t0 ← IO.monoMsNow
  enableInit
  let env ← importModules (want.map fun m => { module := m.toName }) {} (trustLevel := 1024)
    (loadExts := true)
  let dt := (← IO.monoMsNow) - t0
  s.envs.modify (·.push (want, env))
  s.stats.modify fun st => { st with imports := st.imports + 1, importMs := st.importMs + dt }
  return env

private def oneLine (s : String) : String :=
  let flat := String.intercalate " " ((s.splitOn "\n").map (·.trimAscii.toString))
  if flat.length > 400 then (flat.take 400).toString ++ "…" else flat

/-- Elaborate `src` on top of the environment for `imports`; the first error, if any. -/
def Session.elaborate (s : Session) (imports : Array String) (src : String) :
    IO (Except String Environment) := do
  let env ← match ← (s.envFor imports).toBaseIO with
    | .ok e => pure e
    | .error e => return .error s!"import failed: {oneLine (toString e)}"
  let opts := maxHeartbeats.set Options.empty s.cfg.maxHeartbeats
  let t0 ← IO.monoMsNow
  let (env', msgs) ← Elab.process src env opts
  let dt := (← IO.monoMsNow) - t0
  s.stats.modify fun st => { st with elaborations := st.elaborations + 1, elabMs := st.elabMs + dt }
  if msgs.hasErrors then
    let errs := msgs.toList.filter (·.severity == .error)
    let texts ← errs.mapM (·.toString)
    return .error (oneLine (texts.headD "elaboration failed"))
  return .ok env'

/-! ## Rendering a probe -/

/-- Shape of the stub for a function known only by values; must agree with `GenExpr.analyze`. -/
private def tableRet (rows : Array (Array Int × Int)) : Ty :=
  if rows.any (fun (_, v) => v < 0) then .int else .nat

/-- A stub returning the table's values and `junk` everywhere else. Two stubs with different
junk values tell a point that used the table from one that strayed outside it. Written with core
`Nat`/`Int` rather than `ℕ`/`ℤ`, so it needs no import of its own. -/
def renderStub (name : String) (rows : Array (Array Int × Int)) (junk : Int) : String :=
  let arity := (rows[0]?.map (·.1.size)).getD 1
  let ret := if tableRet rows == .nat then "Nat" else "Int"
  let xs := (List.range arity).map fun i => s!"x{i}"
  let binders := String.join (xs.map fun x => s!" ({x} : Nat)")
  let key := "[" ++ String.intercalate ", " (xs.map fun x => s!"Int.ofNat {x}") ++ "]"
  let entries := String.intercalate ", " (rows.toList.map fun (a, v) =>
    "([" ++ String.intercalate ", " (a.toList.map fun x => s!"({x} : Int)") ++ s!"], ({v} : Int))")
  let conv := if ret == "Nat" then "v.toNat" else "v"
  let junkLit := if junk < 0 then s!"({junk})" else toString junk
  s!"def {name}{binders} : {ret} :=\n" ++
    s!"  match ([{entries}] : List (List Int × Int)).lookup {key} with\n" ++
    s!"  | some v => {conv}\n  | none => {junkLit}"

/-- Every name the term calls, so that only the tables it uses get a stub. -/
private def calledKeys (t : Typing) : Array String :=
  (t.expr.alts ++ (t.aux.map fun (_, _, b) => b.alts).flatten).map (·.key)

private def probeArg (i : Nat) : Ty → Option String
  | .nat => some s!"(args[{i}]!).toNat"
  | .int => some s!"args[{i}]!"
  | _ => none

/-- Source defining the candidate as emitted, its auxiliaries and stubs, inside namespace `ns`.
With `withProbe`, also a `probe : Array Int → String` that evaluates it; a statement is then
written as a reducible predicate so that `decide` can see through it. -/
def snippet (st : RenderStyle) (t : Typing) (patched : Array (Array Int × Int))
    (tables : Array (String × Array (Array Int × Int))) (ns : String) (junk : Int)
    (withProbe : Bool) (form : RecForm := recFormOf t) : String :=
  let used := calledKeys t
  let stubs := (tables.filter fun (n, _) => used.contains n).map fun (n, rows) =>
    renderStub n rows junk
  let aux := t.aux.map fun (n, ps, b) => renderAux st n ps b
  let isProp := t.ret == .prop
  let main :=
    if isProp && withProbe then
      let bs := String.join (t.params.toList.map fun (n, ty) => s!" ({n} : {ty.render})")
      s!"abbrev {t.name}{bs} : Prop :=\n  {renderBody st t}"
    else renderDef st t t.name patched form junk
  let call (args : Array String) : String :=
    let app := String.intercalate " " (t.name :: args.toList)
    if isProp then s!"if decide ({app}) then (1 : Int) else 0" else app
  let probe :=
    match (t.params.mapIdx fun i (_, ty) => probeArg i ty).mapM id with
    | some args =>
      if withProbe then #[s!"def probe (args : Array Int) : String :=\n  toString ({call args})"]
      else #[]
    | none => #[]
  s!"namespace {ns}\n\n" ++ String.intercalate "\n\n" (stubs ++ aux ++ #[main] ++ probe).toList ++
    s!"\n\nend {ns}\n"

private def junkValues : Array Int := #[0, 1234567891]

private def freshNamespace (s : Session) : IO String := do
  let k ← s.counter.modifyGet fun c => (c, c + 1)
  return s!"GenExprProbe{k}"

/-! ## Evaluation -/

/-- Run `f args` on its own thread, giving up after the configured timeout. A runaway thread
cannot be stopped, only abandoned. -/
private def evalWithTimeout (s : Session) (f : Array Int → String) (args : Array Int) :
    IO (Option String) := do
  let work ← IO.asTask (prio := .dedicated) (IO.lazyPure fun _ => f args)
  let deadline := (← IO.monoMsNow) + s.cfg.pointTimeoutMs
  repeat
    if ← IO.hasFinished work then break
    if (← IO.monoMsNow) ≥ deadline then
      s.stats.modify fun st => { st with timeouts := st.timeouts + 1 }
      return none
    IO.sleep 1
  s.stats.modify fun st => { st with evaluations := st.evaluations + 1 }
  match work.get with
  | .ok v => return some v
  | .error e => return some s!"<error: {e}>"

/-- Compiled probes for one set of base cases, together with the environment that owns them. -/
private structure Compiled where
  probes : Array (Array Int → String)
  env : Environment
  form : RecForm

/-- What the evaluator learned about the declaration: whether any rendering elaborated, and
which rung of the recursion ladder it was. -/
structure Elaboration where
  elaborated : Option Bool := none
  form : Option RecForm := none

/-- A point evaluator for `runPolicy`. The declaration is re-elaborated whenever the set of base
cases grows, climbing the recursion ladder until a rung elaborates. -/
def Session.evaluator (s : Session) (t : Typing) (tables : Array (String × Array (Array Int × Int))) :
    IO ((Array (Array Int × Int) → Array Int → IO Outcome) × IO.Ref Elaboration) := do
  let cache : IO.Ref (Option (Array (Array Int × Int) × Except Reject Compiled)) ← IO.mkRef none
  let info : IO.Ref Elaboration ← IO.mkRef {}
  let recursive := usesSelf t.expr
  let imports := typingImports t
  let usesTables := tables.any fun (n, _) => (calledKeys t).contains n
  -- A junk arm or exhausted fuel must not pass for a value, so recursion gets two renderings too.
  let junks := if usesTables || recursive then junkValues else #[0]
  let build (patched : Array (Array Int × Int)) : IO (Except Reject Compiled) := do
    let mut lastError := ""
    for form in (recFormOf t).ladder do
      let ns ← freshNamespace s
      let src := String.intercalate "\n" (junks.toList.mapIdx fun j junk =>
        snippet s.cfg.style t patched tables s!"{ns}_{j}" junk true form)
      match ← s.elaborate imports src with
      | .error msg => lastError := msg
      | .ok env =>
        info.modify ({ · with elaborated := some true, form := some form })
        let mut probes := #[]
        for j in [0:junks.size] do
          match loadProbe env {} s!"{ns}_{j}.probe".toName with
          | .ok f => probes := probes.push f
          | .error e => return .error (.elabError s!"cannot evaluate: {oneLine e}")
        return .ok { probes, env, form }
    if (← info.get).elaborated.isNone then info.modify ({ · with elaborated := some false })
    return .error (.elabError lastError)
  let eval (patched : Array (Array Int × Int)) (args : Array Int) : IO Outcome := do
    let compiled ← match ← cache.get with
      | some (key, c) => if key == patched then pure c else do
          let c ← build patched
          cache.set (some (patched, c))
          pure c
      | none => do
          let c ← build patched
          cache.set (some (patched, c))
          pure c
    match compiled with
    | .error rj =>
      -- More base cases can make a structural recursion elaborate; nothing else can.
      return if recursive then .error rj else .fatal rj
    | .ok c =>
      let mut results : Array String := #[]
      for f in c.probes do
        match ← evalWithTimeout s f args with
        | some v => results := results.push v
        | none => return .timeout
      if results.any (· != results[0]!) then
        -- With recursion the junk may be a missing base case, which a patch can supply.
        return if recursive then .undetermined else .unknown
      return .value results[0]!
  return (eval, info)

/-- Elaborate the emitted declaration without evaluating it, climbing the recursion ladder.
Returns the rung that elaborated, or why none did. -/
def Session.typecheck (s : Session) (t : Typing) (tables : Array (String × Array (Array Int × Int)))
    (patched : Array (Array Int × Int) := #[]) : IO (Except Reject RecForm) := do
  let mut lastError := ""
  for form in (recFormOf t).ladder do
    let ns ← freshNamespace s
    match ← s.elaborate (typingImports t) (snippet s.cfg.style t patched tables ns 0 false form) with
    | .ok _ => return .ok form
    | .error msg => lastError := msg
  return .error (.elabError lastError)

/-! ## Engines -/

/-- Check one typing with Lean alone: the policy runs over values Lean computes. -/
def Session.verifyLean (s : Session) (cfg : VerifyConfig) (t : Typing)
    (points : Array (Array Int × Int)) (guards : Array Guard)
    (tables : Array (String × Array (Array Int × Int))) : IO VerifyReport := do
  if !t.computable then
    if !s.cfg.elabNoncomputable then return { accepted := false, reason := some .notComputable }
    return match ← s.typecheck t tables with
      | .ok form => { accepted := false, reason := some .notComputable, elaborated := some true
                      recForm := some form }
      | .error rj => { accepted := false, reason := some rj, elaborated := some false }
  let bound := (t.params[0]?.map (·.1)).bind (guardLowerBound guards)
  let (eval, info) ← s.evaluator t tables
  let r ← runPolicy cfg points bound eval
  let e ← info.get
  return { r with leanChecked := (r.statuses.filter (·.isGood)).size
                  elaborated := e.elaborated, recForm := e.form }

/-- Confirm an interpreter verdict with Lean. Only points the interpreter already settled are
evaluated, so a slow Lean evaluation can only time out, never run unbounded on a point that was
never going to finish. -/
def Session.confirm (s : Session) (t : Typing) (r : VerifyReport)
    (points : Array (Array Int × Int)) (tables : Array (String × Array (Array Int × Int))) :
    IO VerifyReport := do
  if !r.accepted then return r
  let (eval, info) ← s.evaluator t tables
  let mut checked := 0
  let mut i := 0
  for (args, expected) in points do
    if r.statuses[i]?.any (·.isGood) then
      match ← eval r.patched args with
      | .value v =>
        if v == toString expected then checked := checked + 1
        else
          return { r with accepted := false, leanChecked := checked, elaborated := some true
                          recForm := (← info.get).form
                          reason := some (.engineDisagreement i (toString expected) v) }
      | .unknown | .undetermined => pure ()
      -- Later points are larger and only slower; one abandoned thread is enough.
      | .timeout => break
      | .error rj | .fatal rj =>
        return { r with accepted := false, leanChecked := checked
                        elaborated := (← info.get).elaborated, reason := some rj }
    i := i + 1
  let e ← info.get
  return { r with leanChecked := checked, elaborated := e.elaborated, recForm := e.form }

private def statusText : PointStatus → String
  | .pass => "ok" | .patched => "base case" | .fail g => g | .unknown => "unknown"
  | .timeout => "timeout"

private def isFail : PointStatus → Bool
  | .fail _ => true
  | _ => false

/-- Run both engines independently and accept only if they agree. Timeouts and unknowns may
differ — the interpreter memoises and Lean does not — but a value one engine accepts and the
other rejects is a semantic drift between them, and is reported as such. -/
def Session.crossCheck (s : Session) (cfg : VerifyConfig) (t : Typing)
    (points : Array (Array Int × Int)) (guards : Array Guard)
    (tables : Array (String × Array (Array Int × Int))) : IO VerifyReport := do
  let ri := verify cfg t points guards tables
  let rl ← s.verifyLean cfg t points guards tables
  if !t.computable then return rl
  let n := min ri.statuses.size rl.statuses.size
  for i in [0:n] do
    let a := ri.statuses[i]!
    let b := rl.statuses[i]!
    if (a.isGood && isFail b) || (isFail a && b.isGood) then
      return { rl with accepted := false
                       reason := some (.engineDisagreement i (statusText a) (statusText b)) }
  if ri.patched != rl.patched && ri.accepted && rl.accepted then
    return { rl with accepted := false
                     reason := some (.engineDisagreement ri.patched.size "base cases differ" "") }
  if ri.accepted && rl.accepted then return rl
  return { rl with accepted := false, reason := if rl.accepted then ri.reason else rl.reason }

/-- Check one typing with the configured engine. -/
def Session.check (s : Session) (cfg : VerifyConfig) (t : Typing)
    (points : Array (Array Int × Int)) (guards : Array Guard)
    (tables : Array (String × Array (Array Int × Int))) : IO VerifyReport :=
  match cfg.engine with
  | .internal => pure (verify cfg t points guards tables)
  | .lean => s.verifyLean cfg t points guards tables
  | .internalThenLean => s.confirm t (verify cfg t points guards tables) points tables
  | .crossCheck => s.crossCheck cfg t points guards tables

/-! ## Isolated elaboration

Whether a declaration's imports are *sufficient* can only be seen in an environment built from
those imports alone. Environments are never freed, so each import set is checked in a child
process, which gives its memory back when it exits. -/

private def blockSep : String := "-- @@block"

/-- Entry point of a child: elaborate each block of the request file against exactly the imports
on its first line, printing `OK` or `ERR <message>` per block. -/
def childMain (path : String) : IO UInt32 := do
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let imports := ((lines.headD "").splitOn " ").filter (· != "") |>.toArray
  let blocks := (String.intercalate "\n" (lines.drop 1)).splitOn blockSep
  let s ← Session.create { baseImports := imports }
  for b in blocks do
    match ← s.elaborate #[] b with
    | .ok _ => IO.println "OK"
    | .error e => IO.println s!"ERR {e}"
  return 0

/-- Elaborate each block against exactly `imports`, in a child process running `exe`, which must
dispatch `--elab-child PATH` to `childMain`. One result per block: `none` if it elaborated. -/
def elabIsolated (exe : System.FilePath) (imports : Array String) (blocks : Array String) :
    IO (Array (Option String)) := do
  let path : System.FilePath := ".lake" / "build" / s!"genexpr-child-{← IO.monoNanosNow}.txt"
  IO.FS.writeFile path
    (String.intercalate " " imports.toList ++ "\n" ++
      String.intercalate s!"\n{blockSep}\n" blocks.toList)
  let out ← IO.Process.output { cmd := exe.toString, args := #["--elab-child", path.toString] }
  IO.FS.removeFile path
  let replies := (out.stdout.splitOn "\n").filter fun l => l == "OK" || l.startsWith "ERR "
  if replies.length != blocks.size then
    let why := s!"child exited with {out.exitCode}: {oneLine out.stderr}"
    return blocks.map fun _ => some why
  return replies.toArray.map fun l => if l == "OK" then none else some (l.drop 4).toString

private def fillTemplate (template : String) (args : List String) : String := Id.run do
  let mut out := template
  for (a, i) in args.zip (List.range args.length) do
    out := out.replace s!"\{{i}}" a
  return out

/-- One declaration per catalogue alternative, applying it to variables of its parameter types,
grouped by the imports the alternative and its types declare. Elaborating each group under
exactly those imports checks that the catalogue's import lists are sufficient. -/
def catalogueProbes (alts : Array Alt) : Array (Array String × Array (String × String)) :=
  Id.run do
    let mut groups : Array (Array String × Array (String × String)) := #[]
    for (alt, i) in alts.zip (Array.range alts.size) do
      let tys := alt.params.push alt.result
      let imports := sortDedup (alt.imports ++ (tys.map Builtins.typeImports).flatten)
      let xs := (List.range alt.params.size).map fun j => s!"x{j}"
      let binders := String.join ((xs.zip alt.params.toList).map fun (x, ty) =>
        s!" ({x} : {ty.render})")
      let kw := if alt.computable then "def" else "noncomputable def"
      let block := s!"{kw} probe{i}{binders} : {alt.result.render} :=\n  " ++
        fillTemplate alt.template (xs.map fun x => s!"({x})")
      let sig := String.intercalate " → " (tys.toList.map Ty.render)
      let entry := (s!"{alt.key} as {alt.template} : {sig}", block)
      match groups.findIdx? (·.1 == imports) with
      | some j => groups := groups.modify j fun (im, es) => (im, es.push entry)
      | none => groups := groups.push (imports, #[entry])
    return groups

end
end GenExpr.LeanEngine
