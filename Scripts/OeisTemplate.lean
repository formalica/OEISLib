import SQLite
import Scripts.OeisIngest.Db
import Scripts.OeisTemplate.Base
import Scripts.Templates.Registry

/-!
Generic template runner: applies a named template to families of OEIS sequences and records the
result in `formalization_item`.

    lake exe oeis-template <template> --all
    lake exe oeis-template <template> --bucket A147
    lake exe oeis-template <template> --seq A147999 [--seq ...]
                           [--db PATH] [--force] [--dry-run] [--limit N] [--<template flag>=V]

The runner owns selection, loading (from the database, never from `oeisdata/`), the transaction
and reporting. A template only maps a loaded sequence to candidates; `Oeis.Template.publish`
checks every candidate's original text against the stored sections before anything is written.
Without `--force`, sequences that already have items from this template are skipped.
-/

namespace Oeis.Template.Runner

open SQLite

structure Config where
  tpl : Option String := none
  dbPath : System.FilePath := "Metadata/oeis.db"
  seqs : Array String := #[]
  buckets : Array String := #[]
  all : Bool := false
  force : Bool := false
  dryRun : Bool := false
  limit : Option Nat := none
  extras : List String := []

def parseArgs (args : List String) : Except String Config := go args {}
where
  go : List String → Config → Except String Config
    | [], cfg =>
      match cfg.tpl with
      | none => .error "missing template name: `lake exe oeis-template <template> ...`"
      | some _ =>
        if cfg.all || !cfg.seqs.isEmpty || !cfg.buckets.isEmpty then .ok cfg
        else .error "nothing selected: pass --all, --bucket A147 or --seq A147999"
    | "--db" :: v :: rest, cfg => go rest { cfg with dbPath := v }
    | "--seq" :: v :: rest, cfg => go rest { cfg with seqs := cfg.seqs.push v }
    | "--bucket" :: v :: rest, cfg => go rest { cfg with buckets := cfg.buckets.push v }
    | "--all" :: rest, cfg => go rest { cfg with all := true }
    | "--force" :: rest, cfg => go rest { cfg with force := true }
    | "--dry-run" :: rest, cfg => go rest { cfg with dryRun := true }
    | "--limit" :: v :: rest, cfg =>
      match v.toNat? with
      | some n => go rest { cfg with limit := some n }
      | none => .error s!"--limit expects a number, got '{v}'"
    | arg :: rest, cfg =>
      if arg.startsWith "-" then go rest { cfg with extras := cfg.extras ++ [arg] }
      else
        match cfg.tpl with
        | none => go rest { cfg with tpl := some arg }
        | some _ => .error s!"unexpected positional argument '{arg}' (only one template at a time)"

/-- Names of the sequences a template's `selectWhere` picks, restricted to `--bucket`s. -/
private def discover (db : SQLite) (tpl : Template) (cfg : Config) : IO (Array String) := do
  let buckets :=
    if cfg.buckets.isEmpty then ""
    else " AND (" ++ " OR ".intercalate (cfg.buckets.toList.map fun b => s!"name LIKE '{b}%'") ++ ")"
  let stmt ← db.prepare
    ("SELECT name FROM sequence WHERE (" ++ tpl.selectWhere ++ ")" ++ buckets ++ " ORDER BY name")
  let mut out := #[]
  while ← stmt.step do
    out := out.push (← stmt.columnText 0)
  return out

private def hasItems (db : SQLite) (name producer : String) : IO Bool := do
  let stmt ← db.prepare
    "SELECT 1 FROM formalization_item WHERE oeis_name = ?1 AND producer = ?2 LIMIT 1"
  stmt.bindText 1 name
  stmt.bindText 2 producer
  stmt.step

private def checkFlags (tpl : Template) (extras : List String) : Except String Unit :=
  extras.forM fun e =>
    let key := (e.splitOn "=").head!
    if tpl.flags.contains key then .ok ()
    else .error s!"template '{tpl.name}' does not accept '{e}' \
      (accepted: {", ".intercalate tpl.flags.toList})"

def run (cfg : Config) : IO UInt32 := do
  let tplName := cfg.tpl.getD ""
  let some tpl := findTemplate? tplName
    | IO.eprintln s!"error: unknown template '{tplName}'"
      IO.eprintln "available templates:"
      for t in templates do
        IO.eprintln s!"  {t.name}  — {t.descr}"
      return 1
  if let .error msg := checkFlags tpl cfg.extras then
    IO.eprintln s!"error: {msg}"
    return 1
  unless ← cfg.dbPath.pathExists do
    IO.eprintln s!"error: database not found: {cfg.dbPath} (run `lake exe oeis-ingest` first)"
    return 1
  let db ← Db.openDb cfg.dbPath
  let producer := s!"template:{tpl.name}"
  let mut names : Array String := #[]
  if cfg.all || !cfg.buckets.isEmpty then
    names := names ++ (← discover db tpl cfg)
  for n in cfg.seqs do
    unless names.contains n do names := names.push n
  let selected := match cfg.limit with | some n => names.take n | none => names
  IO.println s!"Template '{tpl.name}': {selected.size} of {names.size} selected sequence(s)\
    {if cfg.dryRun then ", DRY RUN" else ""}"
  unless cfg.dryRun do db.exec "BEGIN;"
  let mut nOk := 0
  let mut nSkip := 0
  let mut nFail := 0
  for name in selected do
    let some src ← loadSource db name
      | IO.eprintln s!"[{name}] FAILED: no such sequence in the database"
        nFail := nFail + 1
        continue
    if !cfg.force && !cfg.dryRun && (← hasItems db name producer) then
      nSkip := nSkip + 1
      continue
    match tpl.formalize cfg.extras src with
    | .skip msg =>
      nSkip := nSkip + 1
      IO.println s!"[{name}] skipped: {msg}"
    | .fail msg =>
      nFail := nFail + 1
      IO.eprintln s!"[{name}] FAILED: {msg}"
    | .items cs =>
      let report ← publish db src producer cfg.dryRun cs
      if cfg.dryRun then
        for (c, start, stop) in report.accepted do
          IO.println s!"[{name}] {c.render start stop}"
      let langs := ", ".intercalate (report.accepted.map fun (c, _, _) => c.language).toList
      if report.rejected.isEmpty then
        nOk := nOk + 1
        IO.println s!"[{name}] ok: {report.accepted.size} item(s) ({langs})"
      else
        nFail := nFail + 1
        IO.eprintln s!"[{name}] FAILED: {report.rejected.size} candidate(s) not backed by the \
          stored text; {report.accepted.size} item(s) accepted"
        for why in report.rejected do IO.eprintln s!"    {why}"
  unless cfg.dryRun do db.exec "COMMIT;"
  IO.println s!"Done. ok={nOk} skipped={nSkip} failed={nFail}"
  return if nFail == 0 then 0 else 1

end Oeis.Template.Runner

def main (args : List String) : IO UInt32 := do
  match Oeis.Template.Runner.parseArgs args with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln "usage: lake exe oeis-template <template> (--all | [--bucket A147]... [--seq A147999]...)"
    IO.eprintln "       [--db PATH] [--force] [--dry-run] [--limit N] [--<template flag>=V]"
    return 1
  | .ok cfg => Oeis.Template.Runner.run cfg
