module
public import Scripts.OeisIngest.Db

/-!
Ingest step: walk `oeisdata/seq`, parse every `.seq` file and populate the
`sequence` / `formula` tables of the metadata database.

    lake exe oeis-ingest [--seq-dir DIR] [--db PATH] [--limit N]
-/

namespace Oeis.Ingest
public section

structure Config where
  seqDir : System.FilePath := "oeisdata/seq"
  dbPath : System.FilePath := "Metadata/oeis.db"
  limit : Option Nat := none

def parseArgs : List String → Except String Config
  | args => go args {}
where
  go : List String → Config → Except String Config
    | [], cfg => .ok cfg
    | "--seq-dir" :: v :: rest, cfg => go rest { cfg with seqDir := v }
    | "--db" :: v :: rest, cfg => go rest { cfg with dbPath := v }
    | "--limit" :: v :: rest, cfg =>
      match v.toNat? with
      | some n => go rest { cfg with limit := some n }
      | none => .error s!"--limit expects a natural number, got '{v}'"
    | arg :: _, _ => .error s!"unrecognized argument '{arg}'"

/-- All `.seq` files under `seqDir`, sorted by name (`A000/A000001.seq`, ...). -/
def collectSeqFiles (seqDir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  let buckets ← seqDir.readDir
  for bucket in buckets.qsort (fun a b => a.fileName < b.fileName) do
    if ← bucket.path.isDir then
      let files ← bucket.path.readDir
      for file in files.qsort (fun a b => a.fileName < b.fileName) do
        if file.path.extension == some "seq" then
          out := out.push file.path
  return out

structure Stats where
  ingested : Nat := 0
  formulas : Nat := 0
  skipped : Nat := 0
  failed : Nat := 0

/-- Number of sequences written per SQLite transaction. -/
def commitEvery : Nat := 2000

def run (cfg : Config) : IO Stats := do
  unless ← cfg.seqDir.pathExists do
    throw <| IO.userError s!"sequence directory not found: {cfg.seqDir}"
  IO.println s!"Scanning {cfg.seqDir} ..."
  let files ← collectSeqFiles cfg.seqDir
  let files := match cfg.limit with
    | some n => files.take n
    | none => files
  IO.println s!"Found {files.size} .seq files"

  let db ← Db.openDb cfg.dbPath
  let stmts ← Db.prepareStmts db
  let mut stats : Stats := {}
  let mut pending := 0
  db.exec "BEGIN"
  for path in files do
    let fallbackName := (path.fileStem.getD "").trimAscii.toString
    let contents? ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
    match contents? with
    | none =>
      stats := { stats with failed := stats.failed + 1 }
    | some contents =>
      match parseSeqFile path.toString fallbackName contents with
      | none => stats := { stats with skipped := stats.skipped + 1 }
      | some entry =>
        Db.upsertEntry stmts entry
        stats := { stats with
          ingested := stats.ingested + 1
          formulas := stats.formulas + entry.formulas.size }
        pending := pending + 1
        if pending ≥ commitEvery then
          db.exec "COMMIT"
          db.exec "BEGIN"
          pending := 0
          IO.println s!"  {stats.ingested} sequences, {stats.formulas} formulas ..."
  db.exec "COMMIT"
  return stats

end
end Oeis.Ingest

def main (args : List String) : IO UInt32 := do
  match Oeis.Ingest.parseArgs args with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln "usage: lake exe oeis-ingest [--seq-dir DIR] [--db PATH] [--limit N]"
    return 1
  | .ok cfg =>
    let stats ← Oeis.Ingest.run cfg
    IO.println s!"Done. ingested={stats.ingested} formulas={stats.formulas} \
      skipped={stats.skipped} failed={stats.failed} db={cfg.dbPath}"
    return 0
