"""Skill loading, function-table filtering and batch prompt assembly."""

from __future__ import annotations

import re
from pathlib import Path

from .db import ProgramRow
from .render import SeqInfo, arg_type_str, referenced_sequences
from .spans import MIN_MARKER

TABLE_BEGIN = "<!-- BEGIN FUNCTION TABLE -->"
TABLE_END = "<!-- END FUNCTION TABLE -->"

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")

#: How many already-formalized definitions of a referenced sequence to show.
ALT_DEFS_PER_DEP = 3



class Skill:
    def __init__(self, path: Path) -> None:
        self.path = path
        raw = path.read_text(encoding="utf-8")
        if TABLE_BEGIN not in raw or TABLE_END not in raw:
            raise ValueError(f"{path} is missing the function table markers")
        head, rest = raw.split(TABLE_BEGIN, 1)
        table, tail = rest.split(TABLE_END, 1)
        self.head = head.rstrip()
        self.tail = tail.strip()
        lines = [ln for ln in table.strip().splitlines() if ln.strip()]
        self.table_header = lines[:2]
        self.table_rows = lines[2:]

    @staticmethod
    def _row_keys(row: str) -> list[str]:
        first = row.split("|")[1] if row.count("|") >= 2 else ""
        return [k.strip().strip("`") for k in first.split(",") if k.strip()]

    def render(self, corpus: str) -> str:
        """Skill text with only the table rows whose functions occur in `corpus`."""
        present = {m.lower() for m in IDENT.findall(corpus)}
        lowered = corpus.lower()
        kept = []
        for row in self.table_rows:
            keys = self._row_keys(row)
            if not keys or any(k == "*" for k in keys):
                kept.append(row)
                continue
            # Identifier keys match whole tokens; operator keys like `!` match as substrings.
            if any(
                k.lower() in present if IDENT.fullmatch(k) else k.lower() in lowered
                for k in keys
            ):
                kept.append(row)
        table = "\n".join([*self.table_header, *kept]) if kept else "*(no entries apply)*"
        return f"{self.head}\n\n{table}\n\n{self.tail}\n"


def _terms_preview(terms: list[str], offset: int, count: int) -> str:
    shown = terms[:count]
    body = ", ".join(shown)
    return f"a({offset})..a({offset + len(shown) - 1}) = {body}"


def sequence_block(seq: SeqInfo, program: str, dep_seqs: dict[str, SeqInfo],
                   terms: int, dep_defs: dict[str, list[str]] | None = None) -> str:
    lines = [
        f"### {seq.name}",
        f"- title: {seq.title}",
        f"- OEIS offset: {seq.offset}",
        f"- main definition: `{seq.name} : {seq.main_arg_type} → {seq.ret_type}`",
        f"- required retType for `formula`: `{seq.ret_type}`",
        "- allowed arg_kind: "
        + ", ".join(f"`{k}` (`{arg_type_str(k, seq.offset)}`)" for k in seq.allowed_arg_kinds),
        f"- known terms: {_terms_preview(seq.terms, seq.offset, terms)}",
    ]
    deps = [d for d in referenced_sequences(program, seq.name) if d in dep_seqs]
    if deps:
        lines.append("- sequences referenced by this program:")
        for name in deps:
            dep = dep_seqs[name]
            lines.append(f"  - `{name}` — {dep.title}")
            lines.append(
                f"    offset {dep.offset}; "
                f"`{name} : {dep.main_arg_type} → {dep.ret_type}`, "
                f"`{name}.fn : Nat → {dep.ret_type}`, "
                f"`{name}.fz : Int → {dep.ret_type}`"
            )
            lines.append(
                f"    terms: {_terms_preview(dep.terms, dep.offset, min(terms, 12))}"
            )
            for body in (dep_defs or {}).get(name, [])[:ALT_DEFS_PER_DEP]:
                lines.append("    already formalized alternative definition:")
                lines.append("    ```lean")
                lines.extend(f"    {ln}" for ln in body.strip().splitlines())
                lines.append("    ```")
    lines += ["- Maple block:", "```maple", program, "```"]
    return "\n".join(lines)


def batch_prompt(
    batch_id: int,
    rows: list[ProgramRow],
    seq_infos: dict[str, SeqInfo],
    dep_seqs: dict[str, SeqInfo],
    terms: int,
    dep_defs: dict[str, list[str]] | None = None,
) -> str:
    blocks = [
        sequence_block(seq_infos[row.oeis_name], row.text, dep_seqs, terms, dep_defs)
        for row in rows
    ]
    header = (
        f"## Batch {batch_id} — {len(rows)} Maple block(s)\n\n"
        "A block often concatenates several independent programs — a direct definition, an "
        "`# Alternative:` variant, a driver loop. **Return one item per independent program, "
        "for every block below.** Skipping one is a defect: the part you leave out is "
        "recorded as unformalized.\n\n"
        "You do not copy a program back. You delimit it with two anchors:\n\n"
        "- `start_marker` — the first characters of the program, verbatim.\n"
        "- `end_marker` — the last characters of the program, verbatim, **including the "
        "trailing comment and author credit** (`# _R. J. Mathar_, Nov 15 2014`) when the "
        "program has one, so that no orphan credit line is left behind.\n\n"
        f"Both anchors must be at least {MIN_MARKER} characters, copied character for "
        "character (whitespace included), and long enough to be unique inside that block — "
        "15 to 60 characters is the usual range. `start_marker` must appear before "
        "`end_marker`, and the spans of two items of the same sequence must not overlap.\n\n"
        "List anything you deliberately do not translate under `skipped`, with a reason.\n"
    )
    return header + "\n\n".join(blocks)


def repair_prompt(failures: list[str]) -> str:
    body = "\n\n".join(f"- {f}" for f in failures)
    return (
        "The following items were rejected. Return the **complete** list again "
        "(including the items that already succeeded, unchanged), with these problems fixed.\n\n"
        f"{body}\n"
    )
