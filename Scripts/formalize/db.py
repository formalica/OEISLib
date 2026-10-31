"""SQLite access for the formalization pipeline.

The schema is owned by `Scripts/OeisIngest/Db.lean` (`oeis-ingest`, `oeis-template` and `oeis-gen`
create and migrate it); this module only reads and writes, and refuses a database that has not
been migrated yet.
"""

from __future__ import annotations

import json
import sqlite3
from dataclasses import dataclass
from pathlib import Path

from .hashing import formula_hash
from .models import BATCH_PENDING


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


@dataclass
class SourceRow:
    """One original text of an item: where it sits and what it says."""

    language: str
    block_index: int
    source_hash: str
    original_text: str
    span_start: int | None = None
    span_end: int | None = None


def connect(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path, timeout=30.0)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode = WAL;")
    conn.execute("PRAGMA foreign_keys = ON;")
    tables = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type = 'table'")}
    if "formalization_source" not in tables:
        raise RuntimeError(
            f"{db_path} has an outdated schema (no `formalization_source` table); run "
            "`.lake/build/bin/oeis-template <template> --seq A000001 --dry-run` once to migrate it"
        )
    return conn


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
            "NOT EXISTS (SELECT 1 FROM formalization_source fs "
            "JOIN formalization_item fi ON fi.id = fs.item_id "
            "WHERE fi.oeis_name = p.oeis_name AND fs.source_hash = p.hash)"
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


_SECTION_RANK = {"maindef": 0, "formula": 1, "comment": 2}


def canonical_sources(sources: list[SourceRow]) -> list[SourceRow]:
    """Title, formulas, comments, then programs; the order `publish` in Lean stores them in."""
    return sorted(
        sources,
        key=lambda s: (
            _SECTION_RANK.get(s.language, 3),
            s.language,
            s.block_index,
            s.span_start or 0,
        ),
    )


def upsert_item(
    conn: sqlite3.Connection, batch_id: int, sources: list[SourceRow], **fields: object
) -> str:
    """Writes one item and replaces its sources; returns its `formula_hash`, the hash of its
    original texts joined with a newline."""
    ordered = canonical_sources(sources)
    hash_ = formula_hash([s.original_text for s in ordered])
    fields.setdefault("producer", "llm")
    fields.setdefault("lean_kind", "computable")
    fields["formula_hash"] = hash_
    cols = ["batch_id", *fields.keys()]
    values = [batch_id, *fields.values()]
    updates = ", ".join(f"{k} = excluded.{k}" for k in ["batch_id", *fields])
    conn.execute(
        f"""INSERT INTO formalization_item ({', '.join(cols)}, created_at, updated_at)
            VALUES ({', '.join('?' * len(cols))}, datetime('now'), datetime('now'))
            ON CONFLICT(oeis_name, producer, formula_hash, lean_kind)
            DO UPDATE SET {updates}, updated_at = datetime('now')""",
        values,
    )
    item_id = conn.execute(
        """SELECT id FROM formalization_item
           WHERE oeis_name = ? AND producer = ? AND formula_hash = ? AND lean_kind = ?""",
        (fields["oeis_name"], fields["producer"], hash_, fields["lean_kind"]),
    ).fetchone()[0]
    conn.execute("DELETE FROM formalization_source WHERE item_id = ?", (item_id,))
    conn.executemany(
        """INSERT INTO formalization_source
             (item_id, ord, language, block_index, source_hash, original_text,
              span_start, span_end)
           VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
        [
            (item_id, n, s.language, s.block_index, s.source_hash, s.original_text,
             s.span_start, s.span_end)
            for n, s in enumerate(ordered)
        ],
    )
    conn.commit()
    return hash_


def batch_items(conn: sqlite3.Connection, batch_id: int) -> list[sqlite3.Row]:
    return list(
        conn.execute(
            "SELECT * FROM formalization_item WHERE batch_id = ? ORDER BY oeis_name", (batch_id,)
        )
    )


def item_sources(
    conn: sqlite3.Connection, item_ids: list[int]
) -> dict[int, list[sqlite3.Row]]:
    """Every source of the given items, in canonical order."""
    out: dict[int, list[sqlite3.Row]] = {i: [] for i in item_ids}
    if not item_ids:
        return out
    sql = "SELECT * FROM formalization_source WHERE item_id IN (%s) ORDER BY item_id, ord" % (
        ",".join("?" * len(item_ids))
    )
    for row in conn.execute(sql, item_ids):
        out[row["item_id"]].append(row)
    return out


def sequence_programs(
    conn: sqlite3.Connection, oeis_name: str, language: str | None = None
) -> list[sqlite3.Row]:
    sql = "SELECT * FROM program WHERE oeis_name = ?"
    params: list[object] = [oeis_name]
    if language:
        sql += " AND language = ?"
        params.append(language)
    return list(conn.execute(sql + " ORDER BY language, block_index", params))


def sequence_spans(conn: sqlite3.Connection, oeis_name: str) -> list[sqlite3.Row]:
    """Every source of every item of the sequence, with the item's hash and status."""
    return list(
        conn.execute(
            """SELECT i.id AS item_id, i.formula_hash, i.status, s.*
               FROM formalization_item i JOIN formalization_source s ON s.item_id = i.id
               WHERE i.oeis_name = ?
               ORDER BY s.source_hash, s.span_start, i.id""",
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
            """SELECT i.status, COUNT(*) AS n FROM formalization_item i
               WHERE EXISTS (SELECT 1 FROM formalization_source s
                             WHERE s.item_id = i.id AND s.language = ?)
               GROUP BY i.status ORDER BY n DESC""",
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
