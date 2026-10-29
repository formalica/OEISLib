"""Terminal rendering for the `show` subcommand."""

from __future__ import annotations

import json
import os
import sqlite3
import sys
from dataclasses import dataclass

from .models import STATUS_GAP_TRIVIAL, STATUS_VERIFIED

RESET = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"

#: Reserved for stretches nothing formalized.
RED = "\033[38;5;196m"

#: One per formalized program, in assignment order. Red is deliberately absent.
PALETTE = [
    "\033[38;5;46m",
    "\033[38;5;39m",
    "\033[38;5;226m",
    "\033[38;5;213m",
    "\033[38;5;51m",
    "\033[38;5;208m",
    "\033[38;5;120m",
    "\033[38;5;147m",
    "\033[38;5;178m",
    "\033[38;5;87m",
]


def want_color(mode: str) -> bool:
    if mode == "always":
        return True
    if mode == "never":
        return False
    return sys.stdout.isatty() and os.environ.get("TERM", "") not in ("", "dumb")


class Painter:
    def __init__(self, enabled: bool) -> None:
        self.enabled = enabled

    def __call__(self, text: str, code: str) -> str:
        return f"{code}{text}{RESET}" if self.enabled and text else text


@dataclass
class Region:
    start: int
    end: int
    color: str
    label: str


def _regions(block: str, items: list[sqlite3.Row], gaps: list[sqlite3.Row]) -> list[Region]:
    regions: list[Region] = []
    for n, item in enumerate(items):
        start, end = item["span_start"], item["span_end"]
        if start is None or end is None or end <= start:
            continue
        regions.append(
            Region(
                max(0, start),
                min(len(block), end),
                PALETTE[n % len(PALETTE)],
                f"{item['formula_hash']} {item['status']}",
            )
        )
    for gap in gaps:
        label = "unformalized"
        if gap["status"] == STATUS_GAP_TRIVIAL:
            label = "unformalized (no program here)"
        if gap["reason"]:
            label += f" — {gap['reason']}"
        regions.append(
            Region(max(0, gap["span_start"]), min(len(block), gap["span_end"]), RED, label)
        )
    return sorted(regions, key=lambda r: (r.start, r.end))


def paint_block(block: str, regions: list[Region], paint: Painter) -> str:
    out: list[str] = []
    cursor = 0
    for region in regions:
        if region.start > cursor:
            out.append(paint(block[cursor : region.start], DIM))
        if region.end > region.start:
            out.append(paint(block[region.start : region.end], region.color))
        cursor = max(cursor, region.end)
    if cursor < len(block):
        out.append(paint(block[cursor:], DIM))
    return "".join(out)


def show_sequence(
    programs: list[sqlite3.Row],
    items: list[sqlite3.Row],
    gaps: list[sqlite3.Row],
    oeis_name: str,
    paint: Painter,
) -> None:
    """Prints every program block of one sequence, coloured by what formalized it."""
    print(paint(f"{oeis_name} — {len(programs)} program block(s)", BOLD))
    for program in programs:
        source_hash = program["hash"]
        block = program["text"]
        block_items = [i for i in items if i["source_hash"] == source_hash]
        block_gaps = [g for g in gaps if g["source_hash"] == source_hash]
        regions = _regions(block, block_items, block_gaps)
        if not regions:
            # Never sent to a model: the whole block is unformalized.
            regions = [Region(0, len(block), RED, "never processed")]

        print()
        print(
            paint(
                f"── %{program['source_tag']} {program['language']} "
                f"block {program['block_index']} ({source_hash}, {len(block)} chars)",
                BOLD,
            )
        )
        print(paint_block(block, regions, paint))
        print()
        for region in regions:
            swatch = paint("███", region.color)
            print(f"  {swatch} [{region.start:>5}:{region.end:<5}] {region.label}")
        unclaimed = [g for g in block_gaps if g["status"] != STATUS_GAP_TRIVIAL]
        covered = sum(r.end - r.start for r in regions if r.color != RED)
        pct = 100.0 * covered / len(block) if block else 0.0
        print(f"  coverage: {pct:.0f}% formalized, {len(unclaimed)} real gap(s)")


def _usage_summary(blob: str) -> str:
    try:
        usage = json.loads(blob or "{}")
    except json.JSONDecodeError:
        return blob
    keys = ("requests", "input_tokens", "output_tokens", "output_reasoning_tokens", "cost")
    parts = [f"{k}={usage[k]}" for k in keys if k in usage]
    return ", ".join(parts) or blob


def _part_text(part: object) -> tuple[str, str]:
    """`(kind, text)` for one pydantic-ai message part, without importing its classes."""
    kind = type(part).__name__
    for attr in ("content", "args", "tool_name", "thinking"):
        value = getattr(part, attr, None)
        if value:
            if not isinstance(value, str):
                value = json.dumps(value, default=str)
            return kind, value
    return kind, ""


def show_history(history: list, paint: Painter, limit: int) -> None:
    """Prints what the model actually replied, turn by turn."""
    if not history:
        print("  (no stored conversation)")
        return
    for n, message in enumerate(history):
        role = type(message).__name__
        print(paint(f"  [{n}] {role}", BOLD))
        for part in getattr(message, "parts", []):
            kind, text = _part_text(part)
            body = text if len(text) <= limit else text[:limit] + f" … (+{len(text) - limit})"
            print(f"    {kind}: " + body.replace("\n", "\n      "))


def show_batch(
    batch: sqlite3.Row,
    items: list[sqlite3.Row],
    gaps: list[sqlite3.Row],
    history: list,
    paint: Painter,
    limit: int,
) -> None:
    print(paint(f"batch {batch['id']}", BOLD))
    for key in ("language", "model", "status", "oeis_names", "attempts", "max_attempts",
                "created_at", "updated_at"):
        print(f"{key:>16}: {batch[key]}")
    print(f"{'usage':>16}: {_usage_summary(batch['usage'])}")
    print(f"{'skill_text':>16}: {len(batch['skill_text'])} chars")
    if batch["last_error"]:
        print(f"{'last_error':>16}: " + batch["last_error"].replace("\n", "\n" + " " * 18))

    print(paint(f"\nitems ({len(items)})", BOLD))
    for item in items:
        colour = "\033[38;5;46m" if item["status"] == STATUS_VERIFIED else RED
        head = (
            f"  {item['oeis_name']} {item['formula_hash']} "
            f"[{item['span_start']}:{item['span_end']}] {item['arg_kind']}"
            f"{'' if item['lean_kind'] != 'noncomputable' else ' non-computable'}"
        )
        print(paint(head, colour) + f"  {item['status']}")
        if item["depends_on"] not in ("", "[]"):
            print(f"      depends_on: {item['depends_on']}")
        if item["verified_upto"]:
            print(f"      verified terms: {item['verified_upto']}")
        if item["notes"]:
            print(f"      note: {item['notes']}")
        if item["original_text"]:
            print("      original:")
            print("        " + item["original_text"][:limit].replace("\n", "\n        "))
        if item["lean_code"]:
            print("      lean_code:")
            print("        " + item["lean_code"][:limit].replace("\n", "\n        "))
        if item["failure_points"] not in ("", "[]"):
            print(f"      failure points: {item['failure_points']}")
        if item["compiler_output"]:
            print("      output:")
            print("        " + item["compiler_output"][:limit].replace("\n", "\n        "))

    print(paint(f"\nunformalized ({len(gaps)})", BOLD))
    for gap in gaps:
        tag = "trivial" if gap["status"] == STATUS_GAP_TRIVIAL else "REAL GAP"
        line = f"  {gap['oeis_name']} [{gap['span_start']}:{gap['span_end']}] {tag}"
        print(paint(line, RED if tag == "REAL GAP" else DIM))
        if gap["reason"]:
            print(f"      model reason: {gap['reason']}")
        print("      " + gap["text"][:limit].replace("\n", "\n      "))

    print(paint("\nconversation", BOLD))
    show_history(history, paint, limit)
