module
import SQLite
public import SQLite.LowLevel
public import Scripts.OeisGen.Render

/-!
Generates the per-sequence `Defs.lean` / `Data.lean` skeletons from `Metadata/oeis.db`.

    lake exe oeis-gen --all
    lake exe oeis-gen --bucket A000
    lake exe oeis-gen --seq A000001 --seq A000045 --force
-/

namespace Oeis.Gen
public section

open SQLite

structure Config where
  dbPath : System.FilePath := "Metadata/oeis.db"
  outDir : System.FilePath := "OEISLib"
  seqs : Array String := #[]
  buckets : Array String := #[]
  all : Bool := false
  force : Bool := false

def parseArgs (args : List String) : Except String Config := go args {}
where
  go : List String → Config → Except String Config
    | [], cfg =>
      if cfg.all || !cfg.seqs.isEmpty || !cfg.buckets.isEmpty then .ok cfg
      else .error "nothing selected: pass --all, --bucket A000 or --seq A000001"
    | "--db" :: v :: rest, cfg => go rest { cfg with dbPath := v }
    | "--out" :: v :: rest, cfg => go rest { cfg with outDir := v }
    | "--seq" :: v :: rest, cfg => go rest { cfg with seqs := cfg.seqs.push v }
    | "--bucket" :: v :: rest, cfg => go rest { cfg with buckets := cfg.buckets.push v }
    | "--all" :: rest, cfg => go rest { cfg with all := true }
    | "--force" :: rest, cfg => go rest { cfg with force := true }
    | arg :: _, _ => .error s!"unrecognized argument '{arg}'"

/-- Splits the JSON array text stored in the DB back into its elements. -/
private def parseJsonArray (s : String) : Array String := Id.run do
  let body := (s.trimAscii.toString.dropPrefix "[").toString.dropSuffix "]" |>.toString
  let mut out := #[]
  for piece in body.splitOn "," do
    let t := piece.trimAscii.toString
    let t := if t.startsWith "\"" && t.endsWith "\"" then (t.drop 1).toString.dropEnd 1 |>.toString
             else t
    if !t.isEmpty then out := out.push t
  return out

private def selectSql : String :=
  "SELECT name, title, \"offset\", keywords, data FROM sequence"

private def rowToSeqInfo (stmt : Stmt) : IO SeqInfo := do
  let name ← stmt.columnText 0
  let title ← stmt.columnText 1
  let offset ← stmt.columnInt64 2
  let keywords := parseJsonArray (← stmt.columnText 3)
  let terms := parseJsonArray (← stmt.columnText 4)
  let isFlat := keywords.contains "tabl" || keywords.contains "tabf"
  return { name, title, offset := offset.toInt, terms, isFlat }

private def drain (stmt : Stmt) : IO (Array SeqInfo) := do
  let mut out := #[]
  while ← stmt.step do
    out := out.push (← rowToSeqInfo stmt)
  return out

def fetchSequences (db : SQLite) (cfg : Config) : IO (Array SeqInfo) := do
  if cfg.all then
    return ← drain (← db.prepare (selectSql ++ " ORDER BY name"))
  let mut out := #[]
  for bucket in cfg.buckets do
    let stmt ← db.prepare (selectSql ++ " WHERE name LIKE ?1 ORDER BY name")
    stmt.bindText 1 (bucket ++ "%")
    out := out ++ (← drain stmt)
  for name in cfg.seqs do
    let stmt ← db.prepare (selectSql ++ " WHERE name = ?1")
    stmt.bindText 1 name
    let rows ← drain stmt
    if rows.isEmpty then
      IO.eprintln s!"warning: no such sequence in the database: {name}"
    out := out ++ rows
  return out

private def writeIfAllowed (path : System.FilePath) (contents : String) (force : Bool) :
    IO Bool := do
  if !force && (← path.pathExists) then
    return false
  IO.FS.writeFile path contents
  return true

/-- Rebuilds `<out>/<bucket>/{Defs,Data}.lean` and `<out>/{Defs,Data}.lean` from what is on disk. -/
def writeAggregators (cfg : Config) : IO Nat := do
  let libName := cfg.outDir.fileName.getD "OEISLib"
  let mut buckets := #[]
  for entry in (← cfg.outDir.readDir) do
    let bucket := entry.fileName
    if !(bucket.startsWith "A" && bucket.length == 4 && (← entry.path.isDir)) then
      continue
    let mut seqs := #[]
    for sub in (← entry.path.readDir) do
      if (← sub.path.isDir) && (← (sub.path / "Defs.lean").pathExists) then
        seqs := seqs.push sub.fileName
    if seqs.isEmpty then
      continue
    seqs := seqs.qsort (· < ·)
    for kind in ["Defs", "Data"] do
      let imports := seqs.toList.map fun s =>
        "import " ++ libName ++ "." ++ bucket ++ "." ++ s ++ "." ++ kind ++ "\n"
      IO.FS.writeFile (entry.path / (kind ++ ".lean")) (String.join imports)
    buckets := buckets.push bucket
  buckets := buckets.qsort (· < ·)
  for kind in ["Defs", "Data"] do
    let imports := buckets.toList.map fun b =>
      "import " ++ libName ++ "." ++ b ++ "." ++ kind ++ "\n"
    IO.FS.writeFile (cfg.outDir / (kind ++ ".lean")) (String.join imports)
  return buckets.size

def run (cfg : Config) : IO Unit := do
  unless ← cfg.dbPath.pathExists do
    throw <| IO.userError s!"database not found: {cfg.dbPath} (run `lake exe oeis-ingest` first)"
  let libName := cfg.outDir.fileName.getD "OEISLib"
  let db ← SQLite.«open» cfg.dbPath
  let seqs ← fetchSequences db cfg
  IO.println s!"Generating {seqs.size} sequences into {cfg.outDir} ..."
  let mut written := 0
  let mut skipped := 0
  for s in seqs do
    let dir := cfg.outDir / s.bucket / s.name
    IO.FS.createDirAll dir
    if ← writeIfAllowed (dir / "Defs.lean") (renderDefs s) cfg.force then
      written := written + 1 else skipped := skipped + 1
    if ← writeIfAllowed (dir / "Data.lean") (renderData libName s) cfg.force then
      written := written + 1 else skipped := skipped + 1
  let buckets ← writeAggregators cfg
  IO.println s!"Done. files written={written} kept={skipped} buckets={buckets}"

end
end Oeis.Gen

def main (args : List String) : IO UInt32 := do
  match Oeis.Gen.parseArgs args with
  | .error msg =>
    IO.eprintln s!"error: {msg}"
    IO.eprintln "usage: lake exe oeis-gen [--db PATH] [--out DIR] [--all] \
      [--bucket A000]... [--seq A000001]... [--force]"
    return 1
  | .ok cfg =>
    Oeis.Gen.run cfg
    return 0
