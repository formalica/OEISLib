"""SQLite access for the formalization pipeline.

The schema itself is owned by `Scripts/OeisIngest/Db.lean`; this module only reads and writes.
`ensure_schema` exists so the Python side still works against a database created before the
formalization tables were added.
"""

from __future__ import annotations

import json
import sqlite3
from dataclasses import dataclass
from pathlib import Path

from .models import BATCH_PENDING

MIGRATION_SQL = """
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
"""


@dataclass
class ProgramRow:
    oeis_name: str
    block_index: int
    text: str
    source_hash: str
    title: str
    offset: int
    terms: list[str]
    keywords: list[str]


def connect(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path, timeout=30.0)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode = WAL;")
    conn.executescript(MIGRATION_SQL)
    _migrate(conn)
    conn.commit()
    return conn


def _columns(conn: sqlite3.Connection, table: str) -> set[str]:
    return {row[1] for row in conn.execute(f"PRAGMA table_info({table})")}


def _migrate(conn: sqlite3.Connection) -> None:
    """Mirror of `migrate` in `Scripts/OeisIngest/Db.lean`; keep the two in step."""
    if "producer" not in _columns(conn, "formalization_item"):
        _rebuild_item_table(conn)
    conn.executescript(
        """
CREATE INDEX IF NOT EXISTS formalization_item_producer_idx
  ON formalization_item (producer, language, status);
CREATE INDEX IF NOT EXISTS formalization_item_source_idx
  ON formalization_item (oeis_name, source_hash);
"""
    )


def _rebuild_item_table(conn: sqlite3.Connection) -> None:
    drops = "".join(
        f"DROP INDEX IF EXISTS formalization_item_{n}_idx;" for n in ("batch", "seq", "status")
    )
    conn.executescript(
        "BEGIN;ALTER TABLE formalization_item RENAME TO formalization_item_old;"
        + drops
        + MIGRATION_SQL
        + """
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
COMMIT;"""
    )


def _row_to_program(row: sqlite3.Row) -> ProgramRow:
    return ProgramRow(
        oeis_name=row["oeis_name"],
        block_index=row["block_index"],
        text=row["text"],
        source_hash=row["hash"],
        title=row["title"],
        offset=row["offset"],
        terms=json.loads(row["data"], parse_int=str),
        keywords=json.loads(row["keywords"]),
    )


def select_programs(
    conn: sqlite3.Connection,
    language: str,
    limit: int,
    buckets: list[str] | None = None,
    seqs: list[str] | None = None,
    include_attempted: bool = False,
) -> list[ProgramRow]:
    """Program blocks that still need formalizing.

    `tabl` / `tabf` sequences are two-argument and out of scope for now.
    """
    where = [
        "p.language = ?",
        "s.data_count > 0",
        "s.keywords NOT LIKE '%\"tabl\"%'",
        "s.keywords NOT LIKE '%\"tabf\"%'",
    ]
    params: list[object] = [language]
    if not include_attempted:
        where.append(
            "NOT EXISTS (SELECT 1 FROM formalization_item fi "
            "WHERE fi.oeis_name = p.oeis_name AND fi.source_hash = p.hash)"
        )
    if seqs:
        where.append("p.oeis_name IN (%s)" % ",".join("?" * len(seqs)))
        params.extend(seqs)
    if buckets:
        where.append(
            "(%s)" % " OR ".join(["substr(p.oeis_name, 1, 4) = ?"] * len(buckets))
        )
        params.extend(buckets)
    sql = f"""
        SELECT p.oeis_name, p.block_index, p.text, p.hash,
               s.title, s."offset", s.data, s.keywords
        FROM program p JOIN sequence s ON s.name = p.oeis_name
        WHERE {' AND '.join(where)}
        ORDER BY p.oeis_name, p.block_index
        LIMIT ?
    """
    params.append(limit)
    return [_row_to_program(r) for r in conn.execute(sql, params)]


def sequence_info(conn: sqlite3.Connection, names: list[str]) -> dict[str, sqlite3.Row]:
    if not names:
        return {}
    sql = 'SELECT name, title, "offset", data, keywords FROM sequence WHERE name IN (%s)' % (
        ",".join("?" * len(names))
    )
    return {r["name"]: r for r in conn.execute(sql, names)}


def verified_definitions(
    conn: sqlite3.Connection, names: list[str], per_sequence: int
) -> dict[str, list[str]]:
    """Lean bodies already verified for the given sequences, newest first."""
    if not names or per_sequence <= 0:
        return {}
    sql = """SELECT oeis_name, lean_code FROM formalization_item
             WHERE producer = 'llm' AND status = 'STATUS_VERIFIED' AND lean_code <> ''
               AND oeis_name IN (%s)
             ORDER BY oeis_name, verified_upto DESC, id DESC""" % (",".join("?" * len(names)))
    out: dict[str, list[str]] = {}
    for row in conn.execute(sql, names):
        bodies = out.setdefault(row["oeis_name"], [])
        if len(bodies) < per_sequence and row["lean_code"] not in bodies:
            bodies.append(row["lean_code"])
    return out


def create_batch(
    conn: sqlite3.Connection, language: str, model: str, names: list[str],
    max_attempts: int, skill_text: str,
) -> int:
    cur = conn.execute(
        """INSERT INTO formalization_batch
             (language, model, status, oeis_names, max_attempts, skill_text,
              created_at, updated_at)
           VALUES (?, ?, ?, ?, ?, ?, datetime('now'), datetime('now'))""",
        (language, model, BATCH_PENDING, json.dumps(names), max_attempts, skill_text),
    )
    conn.commit()
    return int(cur.lastrowid)


def update_batch(conn: sqlite3.Connection, batch_id: int, **fields: object) -> None:
    if not fields:
        return
    assignments = ", ".join(f"{k} = ?" for k in fields)
    conn.execute(
        f"UPDATE formalization_batch SET {assignments}, updated_at = datetime('now') WHERE id = ?",
        (*fields.values(), batch_id),
    )
    conn.commit()


def load_batch(conn: sqlite3.Connection, batch_id: int) -> sqlite3.Row | None:
    return conn.execute(
        "SELECT * FROM formalization_batch WHERE id = ?", (batch_id,)
    ).fetchone()


def upsert_item(conn: sqlite3.Connection, batch_id: int, **fields: object) -> None:
    fields.setdefault("producer", "llm")
    fields.setdefault("lean_kind", "computable")
    if "block_index" not in fields:
        block = conn.execute(
            "SELECT block_index FROM program WHERE oeis_name = ? AND hash = ? LIMIT 1",
            (fields.get("oeis_name"), fields.get("source_hash")),
        ).fetchone()
        fields["block_index"] = block[0] if block else 0
    cols = ["batch_id", *fields.keys()]
    values = [batch_id, *fields.values()]
    updates = ", ".join(f"{k} = excluded.{k}" for k in ["batch_id", *fields])
    conn.execute(
        f"""INSERT INTO formalization_item ({', '.join(cols)}, created_at, updated_at)
            VALUES ({', '.join('?' * len(cols))}, datetime('now'), datetime('now'))
            ON CONFLICT(oeis_name, language, formula_hash, producer, lean_kind)
            DO UPDATE SET {updates}, updated_at = datetime('now')""",
        values,
    )
    conn.commit()


def batch_items(conn: sqlite3.Connection, batch_id: int) -> list[sqlite3.Row]:
    return list(
        conn.execute(
            "SELECT * FROM formalization_item WHERE batch_id = ? ORDER BY oeis_name", (batch_id,)
        )
    )


def sequence_programs(
    conn: sqlite3.Connection, oeis_name: str, language: str | None = None
) -> list[sqlite3.Row]:
    sql = "SELECT * FROM program WHERE oeis_name = ?"
    params: list[object] = [oeis_name]
    if language:
        sql += " AND language = ?"
        params.append(language)
    return list(conn.execute(sql + " ORDER BY language, block_index", params))


def sequence_items(conn: sqlite3.Connection, oeis_name: str) -> list[sqlite3.Row]:
    return list(
        conn.execute(
            """SELECT * FROM formalization_item WHERE oeis_name = ?
               ORDER BY source_hash, span_start, id""",
            (oeis_name,),
        )
    )


def replace_gaps(
    conn: sqlite3.Connection,
    batch_id: int,
    oeis_name: str,
    language: str,
    source_hash: str,
    rows: list[tuple[int, int, str, str, str]],
) -> None:
    """Rewrites the recorded gaps of one program block; `rows` are
    `(span_start, span_end, text, status, reason)`."""
    conn.execute(
        "DELETE FROM program_gap WHERE oeis_name = ? AND language = ? AND source_hash = ?",
        (oeis_name, language, source_hash),
    )
    conn.executemany(
        """INSERT INTO program_gap
             (batch_id, oeis_name, language, source_hash, span_start, span_end,
              text, status, reason, created_at, updated_at)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, datetime('now'), datetime('now'))""",
        [(batch_id, oeis_name, language, source_hash, *row) for row in rows],
    )
    conn.commit()


def sequence_gaps(conn: sqlite3.Connection, oeis_name: str) -> list[sqlite3.Row]:
    return list(
        conn.execute(
            "SELECT * FROM program_gap WHERE oeis_name = ? ORDER BY source_hash, span_start",
            (oeis_name,),
        )
    )


def batch_gaps(conn: sqlite3.Connection, batch_id: int) -> list[sqlite3.Row]:
    return list(
        conn.execute(
            "SELECT * FROM program_gap WHERE batch_id = ? ORDER BY oeis_name, span_start",
            (batch_id,),
        )
    )


def clear_batch_items(conn: sqlite3.Connection, batch_id: int) -> None:
    conn.execute("DELETE FROM formalization_item WHERE batch_id = ?", (batch_id,))
    conn.commit()


def add_skill_suggestions(
    conn: sqlite3.Connection, batch_id: int, language: str, kind: str, texts: list[str]
) -> None:
    conn.executemany(
        """INSERT INTO skill_suggestion (batch_id, language, kind, text, created_at)
           VALUES (?, ?, ?, ?, datetime('now'))""",
        [(batch_id, language, kind, t) for t in texts],
    )
    conn.commit()


def stats(conn: sqlite3.Connection, language: str) -> list[sqlite3.Row]:
    return list(
        conn.execute(
            """SELECT status, COUNT(*) AS n FROM formalization_item
               WHERE language = ? GROUP BY status ORDER BY n DESC""",
            (language,),
        )
    )


def gap_stats(conn: sqlite3.Connection, language: str) -> list[sqlite3.Row]:
    return list(
        conn.execute(
            """SELECT status, COUNT(*) AS n FROM program_gap
               WHERE language = ? GROUP BY status ORDER BY n DESC""",
            (language,),
        )
    )
