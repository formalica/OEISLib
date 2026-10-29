import SQLite
import Scripts.OeisIngest.Db
import Scripts.OeisTemplate.Base

/-!
Integration test for the template base interface and the schema migration, on throwaway
databases:

    lake exe oeis-template-test
-/

open SQLite Oeis Oeis.Template

private def check (ok : Bool) (what : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"FAILED: {what}"

private def scalar (db : SQLite) (sql : String) : IO Int := do
  let s ← db.prepare sql
  unless ← s.step do throw <| IO.userError s!"no row: {sql}"
  return (← s.columnInt64 0).toInt

private def text (db : SQLite) (sql : String) : IO String := do
  let s ← db.prepare sql
  unless ← s.step do throw <| IO.userError s!"no row: {sql}"
  s.columnText 0

private def columns (db : SQLite) (table : String) : IO (Array String) := do
  let s ← db.prepare s!"PRAGMA table_info({table})"
  let mut out := #[]
  while ← s.step do out := out.push (← s.columnText 1)
  return out

private def cand (language originalText : String) (kind : LeanKind := .computable) : Candidate :=
  { language, originalText, leanKind := kind, leanType := "Nat → Nat", leanCode := "fun n => n",
    verifiedUpto := 3 }

/-- A formula containing JSON metacharacters, to exercise the round trip through the database. -/
private def tricky : String := "a(n) = \"x\" \\ n"

private def seed (db : SQLite) : IO SeqSource := do
  let s ← db.prepare "INSERT INTO sequence (name, title, \"offset\", data, formula_lines, comment_lines)
    VALUES ('A000001', 'Number of groups of order n.', 0, '[1,1,1]', ?1, '[]')"
  s.bindText 1 (Json.strArray #["a(n) = n + 1.", tricky, "c(n) =", "  3*n"])
  s.exec
  db.exec "INSERT INTO program (oeis_name, language, block_index, source_tag, text, hash)
    VALUES ('A000001', 'pari', 0, 'o', 'a(n)=n+1', 'HASH');"
  let some src ← loadSource db "A000001" | throw <| IO.userError "seed sequence not loadable"
  return src

private def testPublish (dir : System.FilePath) : IO Unit := do
  let db ← Db.openDb (dir / "publish.db")
  let src ← seed db
  check (src.formulaLines.size == 4 && src.formulaLines[1]! == tricky) "JSON round trip"
  check (src.programs.size == 1 && src.terms == #["1", "1", "1"]) "program and terms loaded"
  let producer := "template:test"
  -- one backed candidate per section kind, plus two that must be refused
  let good := #[cand Section.maindef "Number of groups of order n.",
                cand Section.maindef "Number of groups of order n." .prop,
                cand Section.formula "c(n) =\n  3*n",
                cand Section.formula tricky,
                cand "pari" "a(n)=n+1"]
  let bad := #[cand Section.formula "c(n) = 3*n", cand "pari" "not in the block"]
  let r ← publish db src producer false (good ++ bad)
  check (r.accepted.size == 5 && r.rejected.size == 2) "accepts backed candidates, rejects the rest"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item") == 5) "five rows written"
  check ((← text db "SELECT original_text FROM formalization_item WHERE language = 'formula'
    AND span_start = 14") == tricky) "span points at the quoted text"
  check ((← text db "SELECT source_hash FROM formalization_item WHERE language = 'pari'") == "HASH")
    "program items keep program.hash as source_hash"
  check ((← scalar db "SELECT COUNT(*) FROM sequence s JOIN formalization_item f
    ON f.id = s.main_item_id WHERE f.lean_kind = 'computable' AND f.language = 'maindef'") == 1)
    "main_item_id points at the computable maindef"
  -- re-publishing is idempotent
  let _ ← publish db src producer false good
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item") == 5) "upsert does not duplicate"
  -- a dry run writes nothing, not even deletions
  let _ ← publish db src producer true #[cand Section.maindef "Number of groups of order n."]
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item") == 5) "dry run leaves the table alone"
  -- other producers are never touched; this producer's stale rows are dropped
  db.exec "INSERT INTO formalization_item (oeis_name, producer, language, formula_hash)
    VALUES ('A000001', 'llm', 'pari', 'deadbeef');"
  let _ ← publish db src producer false #[cand Section.maindef "Number of groups of order n."]
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item WHERE producer = 'llm'") == 1)
    "other producers untouched"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item WHERE producer = 'template:test'") == 1)
    "stale items of the producer removed"

private def testMigration (dir : System.FilePath) : IO Unit := do
  let path := dir / "legacy.db"
  let legacy ← SQLite.«open» path
  legacy.exec "CREATE TABLE sequence (
      name TEXT PRIMARY KEY, title TEXT NOT NULL DEFAULT '', \"offset\" INTEGER NOT NULL DEFAULT 0,
      offset_first_big INTEGER, keywords TEXT NOT NULL DEFAULT '[]', data TEXT NOT NULL DEFAULT '[]',
      data_count INTEGER NOT NULL DEFAULT 0, main_definition_hash TEXT,
      formalized_formula_hashes TEXT NOT NULL DEFAULT '[]',
      unformalized_formula_hashes TEXT NOT NULL DEFAULT '[]',
      all_unformalized_formulas_text TEXT NOT NULL DEFAULT '[]',
      status TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN', source_file TEXT NOT NULL DEFAULT '',
      updated_at TEXT);
    CREATE TABLE program (oeis_name TEXT NOT NULL, language TEXT NOT NULL, block_index INTEGER NOT NULL,
      source_tag TEXT NOT NULL, text TEXT NOT NULL, hash TEXT NOT NULL,
      line_count INTEGER NOT NULL DEFAULT 0, status TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN',
      PRIMARY KEY (oeis_name, language, block_index));
    CREATE TABLE formalization_item (
      id INTEGER PRIMARY KEY AUTOINCREMENT, batch_id INTEGER NOT NULL, oeis_name TEXT NOT NULL,
      language TEXT NOT NULL DEFAULT 'maple', source_hash TEXT NOT NULL DEFAULT '',
      formula_hash TEXT NOT NULL, original_text TEXT NOT NULL DEFAULT '', span_start INTEGER,
      span_end INTEGER, computable INTEGER NOT NULL DEFAULT 1, arg_kind TEXT NOT NULL DEFAULT '',
      lean_code TEXT NOT NULL DEFAULT '', lean_file TEXT NOT NULL DEFAULT '',
      check_file TEXT NOT NULL DEFAULT '', depends_on TEXT NOT NULL DEFAULT '[]',
      status TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN', failure_kind TEXT NOT NULL DEFAULT '',
      failure_points TEXT NOT NULL DEFAULT '[]', compiler_output TEXT NOT NULL DEFAULT '',
      verified_upto INTEGER NOT NULL DEFAULT 0, attempt INTEGER NOT NULL DEFAULT 1,
      notes TEXT NOT NULL DEFAULT '', created_at TEXT, updated_at TEXT,
      UNIQUE (batch_id, oeis_name, formula_hash));
    INSERT INTO sequence (name, all_unformalized_formulas_text) VALUES ('A1', '[\"f\"]');
    INSERT INTO program (oeis_name, language, block_index, source_tag, text, hash)
      VALUES ('A1', 'maple', 2, 'p', 'x', 'H');
    INSERT INTO formalization_item (batch_id, oeis_name, source_hash, formula_hash, computable, lean_code)
      VALUES (7, 'A1', 'H', 'F', 0, 'def formula := 1');"
  for _ in [0:2] do   -- the second pass checks idempotence
    let db ← Db.openDb path
    let cols ← columns db "sequence"
    check (cols.contains "formula_lines" && cols.contains "comment_lines" && cols.contains "main_item_id"
      && !cols.contains "all_unformalized_formulas_text") "sequence columns migrated"
    check ((← text db "SELECT formula_lines FROM sequence WHERE name = 'A1'") == "[\"f\"]")
      "formula lines survive the column rename"
    check ((← text db "SELECT producer || '/' || lean_kind || '/' || block_index || '/' || batch_id
      FROM formalization_item") == "llm/noncomputable/2/7") "legacy item keeps its data"
    check ((← text db "SELECT lean_code FROM formalization_item") == "def formula := 1") "lean_code kept"

def main : IO UInt32 := do
  IO.FS.withTempDir fun dir => do
    testPublish dir
    testMigration dir
  IO.println "oeis-template-test: all checks passed"
  return 0
