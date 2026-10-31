module
import SQLite
public import Scripts.OeisIngest.Db
public import Scripts.OeisTemplate.Base

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
  { sources := #[{ language, originalText }], leanKind := kind, leanType := "Nat → Nat",
    leanCode := "fun n => n", verifiedUpto := 3 }

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
  -- one formalization stated in two places, listed in the "wrong" order
  let both : Candidate :=
    { cand "pari" "a(n)=n+1" with
      sources := #[{ language := "pari", originalText := "a(n)=n+1" },
                   { language := Section.formula, originalText := tricky }] }
  let r ← publish db src producer false (good ++ #[both] ++ bad)
  check (r.accepted.size == 6 && r.rejected.size == 2) "accepts backed candidates, rejects the rest"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item") == 6) "six items written"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_source") == 7) "seven source rows written"
  check ((← text db "SELECT original_text FROM formalization_source WHERE language = 'formula'
    AND span_start = 14 LIMIT 1") == tricky) "span points at the quoted text"
  check ((← text db "SELECT source_hash FROM formalization_source WHERE language = 'pari' LIMIT 1")
    == "HASH") "program sources keep program.hash as source_hash"
  check ((← scalar db "SELECT COUNT(*) FROM sequence s JOIN formalization_item f
    ON f.id = s.main_item_id JOIN formalization_source o ON o.item_id = f.id AND o.ord = 0
    WHERE f.lean_kind = 'computable' AND o.language = 'maindef'") == 1)
    "main_item_id points at the computable item whose first source is the title"
  -- the two-source item: canonical order, hash of the joined texts
  check ((← text db "SELECT group_concat(language, ',') FROM (SELECT language FROM formalization_source
    WHERE item_id = (SELECT item_id FROM formalization_source GROUP BY item_id HAVING COUNT(*) = 2)
    ORDER BY ord)") == "formula,pari") "sources are stored in canonical order"
  check ((← text db "SELECT formula_hash FROM formalization_item WHERE id =
    (SELECT item_id FROM formalization_source GROUP BY item_id HAVING COUNT(*) = 2)")
    == formulaHash (tricky ++ "\n" ++ "a(n)=n+1")) "item hash is the hash of its joined texts"
  -- re-publishing is idempotent
  let _ ← publish db src producer false (good ++ #[both])
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item") == 6) "upsert does not duplicate"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_source") == 7)
    "upsert does not duplicate sources"
  -- a dry run writes nothing, not even deletions
  let _ ← publish db src producer true #[cand Section.maindef "Number of groups of order n."]
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item") == 6) "dry run leaves the table alone"
  -- other producers are never touched; this producer's stale rows are dropped with their sources
  db.exec "INSERT INTO formalization_item (oeis_name, producer, formula_hash)
    VALUES ('A000001', 'llm', 'deadbeef');
    INSERT INTO formalization_source (item_id, ord, language, original_text)
    VALUES (last_insert_rowid(), 0, 'pari', 'x');"
  let _ ← publish db src producer false #[cand Section.maindef "Number of groups of order n."]
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item WHERE producer = 'llm'") == 1)
    "other producers untouched"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_item WHERE producer = 'template:test'") == 1)
    "stale items of the producer removed"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_source") == 2)
    "sources of removed items are removed too"

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
      id INTEGER PRIMARY KEY AUTOINCREMENT, oeis_name TEXT NOT NULL,
      producer TEXT NOT NULL DEFAULT 'llm', producer_params TEXT NOT NULL DEFAULT '{}',
      batch_id INTEGER, language TEXT NOT NULL DEFAULT 'maple',
      block_index INTEGER NOT NULL DEFAULT 0, source_hash TEXT NOT NULL DEFAULT '',
      formula_hash TEXT NOT NULL, original_text TEXT NOT NULL DEFAULT '', span_start INTEGER,
      span_end INTEGER, lean_kind TEXT NOT NULL DEFAULT 'computable',
      arg_kind TEXT NOT NULL DEFAULT '', lean_type TEXT NOT NULL DEFAULT '',
      lean_code TEXT NOT NULL DEFAULT '', imports TEXT NOT NULL DEFAULT '[]',
      aux_code TEXT NOT NULL DEFAULT '', eq_statement TEXT NOT NULL DEFAULT '',
      eq_proof TEXT NOT NULL DEFAULT '', data_eq_proof TEXT, data_eq_aux TEXT,
      lean_file TEXT NOT NULL DEFAULT '', check_file TEXT NOT NULL DEFAULT '',
      depends_on TEXT NOT NULL DEFAULT '[]', status TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN',
      failure_kind TEXT NOT NULL DEFAULT '', failure_points TEXT NOT NULL DEFAULT '[]',
      compiler_output TEXT NOT NULL DEFAULT '', verified_upto INTEGER NOT NULL DEFAULT 0,
      verified_ranges TEXT NOT NULL DEFAULT '[]', attempt INTEGER NOT NULL DEFAULT 1,
      notes TEXT NOT NULL DEFAULT '', created_at TEXT, updated_at TEXT,
      UNIQUE (oeis_name, language, formula_hash, producer, lean_kind));
    CREATE INDEX formalization_item_status_idx ON formalization_item (language, status);
    CREATE INDEX formalization_item_source_idx ON formalization_item (oeis_name, source_hash);
    INSERT INTO sequence (name, all_unformalized_formulas_text) VALUES ('A1', '[\"f\"]');
    INSERT INTO program (oeis_name, language, block_index, source_tag, text, hash)
      VALUES ('A1', 'maple', 2, 'p', 'x', 'H');
    INSERT INTO formalization_item (oeis_name, producer, batch_id, language, block_index,
        source_hash, formula_hash, original_text, span_start, span_end, lean_code)
      VALUES ('A1', 'llm', 7, 'maple', 2, 'H', 'blake', 'x', 0, 1, 'def formula := 1');
    INSERT INTO formalization_item (oeis_name, producer, language, source_hash, formula_hash,
        original_text, span_start, span_end)
      VALUES ('A1', 'template:t', 'formula', 'S', 'keepme', 'y', 4, 5);"
  for _ in [0:2] do   -- the second pass checks idempotence
    let db ← Db.openDb path
    let cols ← columns db "sequence"
    check (cols.contains "formula_lines" && cols.contains "comment_lines" && cols.contains "main_item_id"
      && !cols.contains "all_unformalized_formulas_text") "sequence columns migrated"
    check ((← text db "SELECT formula_lines FROM sequence WHERE name = 'A1'") == "[\"f\"]")
      "formula lines survive the column rename"
    let itemCols ← columns db "formalization_item"
    check (!itemCols.contains "original_text" && !itemCols.contains "language") "text columns moved out"
    check ((← scalar db "SELECT COUNT(*) FROM formalization_item") == 2) "both items kept"
    check ((← text db "SELECT s.language || '/' || s.block_index || '/' || s.source_hash || '/' ||
      s.original_text || '/' || s.span_start || '-' || s.span_end || '/' || s.ord
      FROM formalization_source s JOIN formalization_item i ON i.id = s.item_id
      WHERE i.producer = 'llm'") == "maple/2/H/x/0-1/0") "legacy item keeps its text as source 0"
    check ((← text db "SELECT lean_code FROM formalization_item WHERE producer = 'llm'")
      == "def formula := 1") "lean_code kept"
    check ((← text db "SELECT formula_hash FROM formalization_item WHERE producer = 'llm'")
      == formulaHash "x") "an LLM hash becomes the hash of its text"
    check ((← text db "SELECT formula_hash FROM formalization_item WHERE producer = 'template:t'")
      == "keepme") "template hashes are kept"
  let db ← Db.openDb path
  db.exec "DELETE FROM formalization_item WHERE producer = 'template:t';"
  check ((← scalar db "SELECT COUNT(*) FROM formalization_source") == 1)
    "deleting an item deletes its sources"

public def main : IO UInt32 := do
  IO.FS.withTempDir fun dir => do
    testPublish dir
    testMigration dir
  IO.println "oeis-template-test: all checks passed"
  return 0
