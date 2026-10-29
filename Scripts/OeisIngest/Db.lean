import SQLite
import Scripts.OeisIngest.Parse

/-!
SQLite schema and upsert logic for the OEIS metadata database.

Columns that later stages fill in (`formalized_formula`, `status`,
`main_definition_hash`, ...) are created here but left empty / `STATUS_UNKNOWN`.
Re-running the ingest refreshes only the OEIS-derived columns, so formalization
results written by other scripts survive.
-/

namespace Oeis.Db

open SQLite

/-- Status of a formula that has not been looked at by any formalization step yet. -/
def statusUnknown : String := "STATUS_UNKNOWN"

def schemaSql : String :=
  "CREATE TABLE IF NOT EXISTS sequence (
     name                           TEXT PRIMARY KEY,
     title                          TEXT NOT NULL DEFAULT '',
     \"offset\"                       INTEGER NOT NULL DEFAULT 0,
     offset_first_big               INTEGER,
     keywords                       TEXT NOT NULL DEFAULT '[]',
     data                           TEXT NOT NULL DEFAULT '[]',
     data_count                     INTEGER NOT NULL DEFAULT 0,
     main_definition_hash           TEXT,
     formalized_formula_hashes      TEXT NOT NULL DEFAULT '[]',
     unformalized_formula_hashes    TEXT NOT NULL DEFAULT '[]',
     formula_lines                  TEXT NOT NULL DEFAULT '[]',
     comment_lines                  TEXT NOT NULL DEFAULT '[]',
     main_item_id                   INTEGER,
     status                         TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN',
     source_file                    TEXT NOT NULL DEFAULT '',
     updated_at                     TEXT
   );

   CREATE TABLE IF NOT EXISTS formula (
     hash                  TEXT NOT NULL,
     oeis_name             TEXT NOT NULL,
     human_written_formula TEXT NOT NULL,
     formalized_formula    TEXT NOT NULL DEFAULT '',
     type                  TEXT NOT NULL DEFAULT '',
     status                TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN',
     verification_values   TEXT NOT NULL DEFAULT '[]',
     disproved_values      TEXT NOT NULL DEFAULT '[]',
     additional_conditions TEXT NOT NULL DEFAULT '[]',
     source_tag            TEXT NOT NULL DEFAULT 'F',
     line_index            INTEGER,
     PRIMARY KEY (oeis_name, hash)
   );

   CREATE TABLE IF NOT EXISTS program (
     oeis_name   TEXT NOT NULL,
     language    TEXT NOT NULL,
     block_index INTEGER NOT NULL,
     source_tag  TEXT NOT NULL,
     text        TEXT NOT NULL,
     hash        TEXT NOT NULL,
     line_count  INTEGER NOT NULL DEFAULT 0,
     status      TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN',
     PRIMARY KEY (oeis_name, language, block_index)
   );

   CREATE INDEX IF NOT EXISTS program_language_idx ON program (language);
   CREATE INDEX IF NOT EXISTS program_hash_idx ON program (hash);
   CREATE INDEX IF NOT EXISTS program_status_idx ON program (language, status);

   CREATE TABLE IF NOT EXISTS formalization_batch (
     id           INTEGER PRIMARY KEY AUTOINCREMENT,
     language     TEXT NOT NULL DEFAULT 'maple',
     model        TEXT NOT NULL DEFAULT '',
     status       TEXT NOT NULL DEFAULT 'BATCH_PENDING',
     oeis_names   TEXT NOT NULL DEFAULT '[]',
     attempts     INTEGER NOT NULL DEFAULT 0,
     max_attempts INTEGER NOT NULL DEFAULT 1,
     chat_history TEXT NOT NULL DEFAULT '[]',
     skill_text   TEXT NOT NULL DEFAULT '',
     last_error   TEXT NOT NULL DEFAULT '',
     usage        TEXT NOT NULL DEFAULT '{}',
     created_at   TEXT,
     updated_at   TEXT
   );

   CREATE INDEX IF NOT EXISTS formalization_batch_status_idx
     ON formalization_batch (language, status);

   CREATE TABLE IF NOT EXISTS formalization_item (
     id              INTEGER PRIMARY KEY AUTOINCREMENT,
     oeis_name       TEXT NOT NULL,
     producer        TEXT NOT NULL DEFAULT 'llm',
     producer_params TEXT NOT NULL DEFAULT '{}',
     batch_id        INTEGER,
     language        TEXT NOT NULL DEFAULT 'maple',
     block_index     INTEGER NOT NULL DEFAULT 0,
     source_hash     TEXT NOT NULL DEFAULT '',
     formula_hash    TEXT NOT NULL,
     original_text   TEXT NOT NULL DEFAULT '',
     span_start      INTEGER,
     span_end        INTEGER,
     lean_kind       TEXT NOT NULL DEFAULT 'computable',
     arg_kind        TEXT NOT NULL DEFAULT '',
     lean_type       TEXT NOT NULL DEFAULT '',
     lean_code       TEXT NOT NULL DEFAULT '',
     imports         TEXT NOT NULL DEFAULT '[]',
     aux_code        TEXT NOT NULL DEFAULT '',
     eq_statement    TEXT NOT NULL DEFAULT '',
     eq_proof        TEXT NOT NULL DEFAULT '',
     data_eq_proof   TEXT,
     data_eq_aux     TEXT,
     lean_file       TEXT NOT NULL DEFAULT '',
     check_file      TEXT NOT NULL DEFAULT '',
     depends_on      TEXT NOT NULL DEFAULT '[]',
     status          TEXT NOT NULL DEFAULT 'STATUS_UNKNOWN',
     failure_kind    TEXT NOT NULL DEFAULT '',
     failure_points  TEXT NOT NULL DEFAULT '[]',
     compiler_output TEXT NOT NULL DEFAULT '',
     verified_upto   INTEGER NOT NULL DEFAULT 0,
     verified_ranges TEXT NOT NULL DEFAULT '[]',
     attempt         INTEGER NOT NULL DEFAULT 1,
     notes           TEXT NOT NULL DEFAULT '',
     created_at      TEXT,
     updated_at      TEXT,
     UNIQUE (oeis_name, language, formula_hash, producer, lean_kind)
   );

   CREATE INDEX IF NOT EXISTS formalization_item_batch_idx ON formalization_item (batch_id);
   CREATE INDEX IF NOT EXISTS formalization_item_seq_idx ON formalization_item (oeis_name);
   CREATE INDEX IF NOT EXISTS formalization_item_status_idx
     ON formalization_item (language, status);

   CREATE TABLE IF NOT EXISTS skill_suggestion (
     id         INTEGER PRIMARY KEY AUTOINCREMENT,
     batch_id   INTEGER,
     language   TEXT NOT NULL DEFAULT 'maple',
     kind       TEXT NOT NULL DEFAULT 'note',
     text       TEXT NOT NULL,
     applied    INTEGER NOT NULL DEFAULT 0,
     created_at TEXT
   );

   CREATE TABLE IF NOT EXISTS program_gap (
     id          INTEGER PRIMARY KEY AUTOINCREMENT,
     batch_id    INTEGER,
     oeis_name   TEXT NOT NULL,
     language    TEXT NOT NULL DEFAULT 'maple',
     source_hash TEXT NOT NULL DEFAULT '',
     span_start  INTEGER NOT NULL,
     span_end    INTEGER NOT NULL,
     text        TEXT NOT NULL DEFAULT '',
     status      TEXT NOT NULL DEFAULT 'STATUS_UNFORMALIZED',
     reason      TEXT NOT NULL DEFAULT '',
     created_at  TEXT,
     updated_at  TEXT,
     UNIQUE (oeis_name, language, source_hash, span_start, span_end)
   );

   CREATE INDEX IF NOT EXISTS program_gap_seq_idx ON program_gap (oeis_name, language);
   CREATE INDEX IF NOT EXISTS program_gap_status_idx ON program_gap (language, status);

   CREATE INDEX IF NOT EXISTS formula_hash_idx ON formula (hash);
   CREATE INDEX IF NOT EXISTS formula_status_idx ON formula (status);
   CREATE INDEX IF NOT EXISTS sequence_status_idx ON sequence (status);"

private def sequenceUpsertSql : String :=
  "INSERT INTO sequence
     (name, title, \"offset\", offset_first_big, keywords, data, data_count,
      unformalized_formula_hashes, formula_lines, comment_lines, source_file, updated_at)
   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, datetime('now'))
   ON CONFLICT(name) DO UPDATE SET
     title = excluded.title,
     \"offset\" = excluded.\"offset\",
     offset_first_big = excluded.offset_first_big,
     keywords = excluded.keywords,
     data = excluded.data,
     data_count = excluded.data_count,
     unformalized_formula_hashes = excluded.unformalized_formula_hashes,
     formula_lines = excluded.formula_lines,
     comment_lines = excluded.comment_lines,
     source_file = excluded.source_file,
     updated_at = excluded.updated_at;"

private def formulaUpsertSql : String :=
  "INSERT INTO formula (hash, oeis_name, human_written_formula, source_tag, line_index)
   VALUES (?1, ?2, ?3, ?4, ?5)
   ON CONFLICT(oeis_name, hash) DO UPDATE SET
     human_written_formula = excluded.human_written_formula,
     source_tag = excluded.source_tag,
     line_index = excluded.line_index;"

private def programUpsertSql : String :=
  "INSERT INTO program (oeis_name, language, block_index, source_tag, text, hash, line_count)
   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)
   ON CONFLICT(oeis_name, language, block_index) DO UPDATE SET
     source_tag = excluded.source_tag,
     text = excluded.text,
     hash = excluded.hash,
     line_count = excluded.line_count;"

/-- Prepared statements reused for every sequence. -/
structure Stmts where
  sequence : Stmt
  formula : Stmt
  program : Stmt

private def tableColumns (db : SQLite) (table : String) : IO (Array String) := do
  let stmt ← db.prepare s!"PRAGMA table_info({table})"
  let mut cols := #[]
  while ← stmt.step do
    cols := cols.push (← stmt.columnText 1)
  return cols

/-- Moves a database created by an older schema to the current one. Idempotent; mirrored by
`_migrate` in `Scripts/formalize/db.py`. -/
def migrate (db : SQLite) : IO Unit := do
  let seqCols ← tableColumns db "sequence"
  if seqCols.contains "all_unformalized_formulas_text" && !seqCols.contains "formula_lines" then
    db.exec "ALTER TABLE sequence RENAME COLUMN all_unformalized_formulas_text TO formula_lines;"
  unless seqCols.contains "comment_lines" do
    db.exec "ALTER TABLE sequence ADD COLUMN comment_lines TEXT NOT NULL DEFAULT '[]';"
  unless seqCols.contains "main_item_id" do
    db.exec "ALTER TABLE sequence ADD COLUMN main_item_id INTEGER;"
  -- `formalization_item` gained a producer; SQLite cannot drop `batch_id NOT NULL`, so rebuild.
  let itemCols ← tableColumns db "formalization_item"
  unless itemCols.contains "producer" do
    db.exec ("BEGIN;
      ALTER TABLE formalization_item RENAME TO formalization_item_old;
      DROP INDEX IF EXISTS formalization_item_batch_idx;
      DROP INDEX IF EXISTS formalization_item_seq_idx;
      DROP INDEX IF EXISTS formalization_item_status_idx;" ++ schemaSql ++ "
      INSERT OR REPLACE INTO formalization_item
        (id, oeis_name, producer, batch_id, language, block_index, source_hash, formula_hash,
         original_text, span_start, span_end, lean_kind, arg_kind, lean_code, lean_file,
         check_file, depends_on, status, failure_kind, failure_points, compiler_output,
         verified_upto, attempt, notes, created_at, updated_at)
      SELECT o.id, o.oeis_name, 'llm', o.batch_id, o.language,
             COALESCE((SELECT p.block_index FROM program p
                       WHERE p.oeis_name = o.oeis_name AND p.hash = o.source_hash LIMIT 1), 0),
             o.source_hash, o.formula_hash, o.original_text, o.span_start, o.span_end,
             CASE o.computable WHEN 0 THEN 'noncomputable' ELSE 'computable' END,
             o.arg_kind, o.lean_code, o.lean_file, o.check_file, o.depends_on, o.status,
             o.failure_kind, o.failure_points, o.compiler_output, o.verified_upto, o.attempt,
             o.notes, o.created_at, o.updated_at
      FROM formalization_item_old o ORDER BY o.id;
      DROP TABLE formalization_item_old;
      COMMIT;")
  db.exec "CREATE INDEX IF NOT EXISTS formalization_item_producer_idx
             ON formalization_item (producer, language, status);
           CREATE INDEX IF NOT EXISTS formalization_item_source_idx
             ON formalization_item (oeis_name, source_hash);"

def openDb (path : System.FilePath) : IO SQLite := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let db ← SQLite.«open» path (busyTimeoutMs := 5000)
  db.exec "PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL;"
  db.exec schemaSql
  migrate db
  return db

def prepareStmts (db : SQLite) : IO Stmts := do
  return { sequence := ← db.prepare sequenceUpsertSql
           formula := ← db.prepare formulaUpsertSql
           program := ← db.prepare programUpsertSql }

private def bindOptInt (stmt : Stmt) (index : Int32) : Option Int → IO Unit
  | none => stmt.bindNull index
  | some v => stmt.bindInt64 index (Int64.ofInt v)

/-- Writes one sequence and all of its `%F` formulas. Caller owns the transaction. -/
def upsertEntry (stmts : Stmts) (e : Entry) : IO Unit := do
  let hashes := e.formulas.map formulaHash
  let s := stmts.sequence
  s.reset
  s.bindText 1 e.name
  s.bindText 2 e.title
  s.bindInt64 3 (Int64.ofInt e.offset)
  bindOptInt s 4 e.offsetFirstBig
  s.bindText 5 (Json.strArray e.keywords)
  s.bindText 6 (Json.termArray e.terms)
  s.bindInt64 7 (Int64.ofNat e.terms.size)
  s.bindText 8 (Json.strArray hashes)
  s.bindText 9 (Json.strArray e.formulas)
  s.bindText 10 (Json.strArray e.comments)
  s.bindText 11 e.sourceFile
  s.exec

  let f := stmts.formula
  let mut i : Nat := 0
  for (text, hash) in e.formulas.zip hashes do
    f.reset
    f.bindText 1 hash
    f.bindText 2 e.name
    f.bindText 3 text
    f.bindText 4 "F"
    f.bindInt64 5 (Int64.ofNat i)
    f.exec
    i := i + 1

  let p := stmts.program
  for prog in e.programs do
    p.reset
    p.bindText 1 e.name
    p.bindText 2 prog.language
    p.bindInt64 3 (Int64.ofNat prog.blockIndex)
    p.bindText 4 prog.sourceTag
    p.bindText 5 prog.text
    p.bindText 6 (formulaHash prog.text)
    p.bindInt64 7 (Int64.ofNat (prog.text.splitOn "\n").length)
    p.exec

end Oeis.Db
