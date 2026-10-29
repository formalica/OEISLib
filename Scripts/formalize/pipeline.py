"""Batch orchestration: prompt → structured output → Lean files → `lake build` → database."""

from __future__ import annotations

import json
import shutil
import sqlite3
from dataclasses import dataclass
from pathlib import Path

from . import db as dbm
from . import lean
from .agent import build_agent, build_learning_agent, dump_history, load_history
from .config import CHECK_LIB, Config
from .models import (
    BATCH_FAILED,
    BATCH_OK,
    BATCH_PARTIAL,
    BATCH_PENDING,
    BATCH_RUNNING,
    STATUS_COMPILE_ERROR,
    STATUS_DEP_RANGE,
    STATUS_EVAL_MISMATCH,
    STATUS_GAP_TRIVIAL,
    STATUS_NONCOMPUTABLE,
    STATUS_REJECTED,
    STATUS_UNFORMALIZED,
    STATUS_VERIFIED,
    BatchResult,
    FormalizedProgram,
)
from .prompt import ALT_DEFS_PER_DEP, Skill, batch_prompt, repair_prompt, snippet_hash
from .render import (
    RenderedItem,
    SeqInfo,
    check_file_text,
    checkable_terms,
    equiv_file_text,
    referenced_sequences,
    validate_lean_code,
)
from .spans import Markers, Span, gaps, is_trivial, resolve

#: How much of a gap to quote back to the model.
GAP_PREVIEW = 400


@dataclass
class Rejection:
    oeis_name: str
    snippet: str
    reason: str

    def render(self) -> str:
        head = self.snippet.strip().splitlines()
        preview = head[0][:120] if head else "(empty)"
        return f"{self.oeis_name}, program starting `{preview}`: {self.reason}"


@dataclass
class Gap:
    """A stretch of a program block that no accepted item claimed."""

    oeis_name: str
    span: Span
    text: str
    reason: str = ""

    @property
    def trivial(self) -> bool:
        return is_trivial(self.text)

    @property
    def status(self) -> str:
        return STATUS_GAP_TRIVIAL if self.trivial else STATUS_UNFORMALIZED

    def render(self) -> str:
        return (
            f"{self.oeis_name}: characters {self.span.start}-{self.span.end} of the block were "
            "left unformalized. Either return an item covering this program, or list it under "
            f"`skipped` with a reason:\n```\n{self.text[:GAP_PREVIEW]}\n```"
        )


def seq_info_from_row(row: sqlite3.Row) -> SeqInfo:
    return SeqInfo(
        name=row["name"],
        title=row["title"],
        offset=int(row["offset"]),
        terms=json.loads(row["data"], parse_int=str),
    )


def defs_exists(cfg: Config, name: str) -> bool:
    return (cfg.loeis_dir / name[:4] / name / "Defs.lean").is_file()


def data_exists(cfg: Config, name: str) -> bool:
    return (cfg.loeis_dir / name[:4] / name / "Data.lean").is_file()


def collect_dep_infos(
    conn: sqlite3.Connection, cfg: Config, rows: list[dbm.ProgramRow]
) -> dict[str, SeqInfo]:
    wanted: set[str] = set()
    for row in rows:
        wanted.update(referenced_sequences(row.text, row.oeis_name))
    wanted = {n for n in wanted if defs_exists(cfg, n) and data_exists(cfg, n)}
    infos = dbm.sequence_info(conn, sorted(wanted))
    return {name: seq_info_from_row(r) for name, r in infos.items()}


def group_batches(rows: list[dbm.ProgramRow], batch_size: int) -> list[list[dbm.ProgramRow]]:
    """A batch holds at most one block per sequence, so the model never sees the same
    sequence twice in one prompt."""
    batches: list[list[dbm.ProgramRow]] = []
    seen: list[set[str]] = []
    for row in rows:
        placed = False
        for batch, names in zip(batches, seen):
            if len(batch) < batch_size and row.oeis_name not in names:
                batch.append(row)
                names.add(row.oeis_name)
                placed = True
                break
        if not placed:
            batches.append([row])
            seen.append({row.oeis_name})
    return batches


def _validate(
    result: BatchResult,
    rows: list[dbm.ProgramRow],
    seq_infos: dict[str, SeqInfo],
    dep_seqs: dict[str, SeqInfo],
) -> tuple[list[RenderedItem], list[Rejection], list[Gap]]:
    by_name = {row.oeis_name: row for row in rows}
    accepted: list[RenderedItem] = []
    rejected: list[Rejection] = []
    found: list[Gap] = []

    grouped: dict[str, list[FormalizedProgram]] = {}
    for item in result.items:
        if item.oeis_name not in by_name:
            rejected.append(
                Rejection(item.oeis_name, item.start_marker,
                          "this sequence is not part of the batch")
            )
            continue
        grouped.setdefault(item.oeis_name, []).append(item)

    # `skipped` does not claim territory — it only explains the gap it falls into.
    skip_reasons: dict[str, list[tuple[int, str]]] = {}
    for skip in result.skipped:
        row = by_name.get(skip.oeis_name)
        if row is None or not skip.start_marker.strip():
            continue
        at = row.text.find(skip.start_marker)
        if at != -1:
            skip_reasons.setdefault(skip.oeis_name, []).append((at, skip.reason))

    for name, row in by_name.items():
        items = grouped.get(name, [])
        block = row.text
        seq = seq_infos[name]
        spans, reasons = resolve(
            block, [Markers(i.start_marker, i.end_marker) for i in items]
        )
        claimed: list[Span] = []
        for item, span, reason in zip(items, spans, reasons):
            if span is None:
                rejected.append(Rejection(name, item.start_marker, reason or "unresolvable"))
                continue
            original_text = span.text(block)
            if item.arg_kind not in seq.allowed_arg_kinds:
                rejected.append(
                    Rejection(name, item.start_marker,
                              f"arg_kind `{item.arg_kind}` is not allowed for offset "
                              f"{seq.offset}; use one of "
                              + ", ".join(f"`{k}`" for k in seq.allowed_arg_kinds))
                )
                continue
            shape_error = validate_lean_code(item.lean_code)
            if shape_error:
                rejected.append(Rejection(name, item.start_marker, shape_error))
                continue
            if name in referenced_sequences(item.lean_code, ""):
                rejected.append(
                    Rejection(name, item.start_marker,
                              f"`lean_code` refers to `{name}` itself; `formula` is the "
                              "definition, so write the recursion out instead")
                )
                continue
            deps = referenced_sequences(item.lean_code, name)
            unknown = [d for d in deps if d not in dep_seqs]
            if unknown:
                rejected.append(
                    Rejection(name, item.start_marker,
                              "references " + ", ".join(f"`{d}`" for d in unknown)
                              + " which has no usable Lean definition; inline the value or "
                                "restructure the definition")
                )
                continue
            claimed.append(span)
            accepted.append(
                RenderedItem(
                    seq=seq,
                    formula_hash=snippet_hash(original_text),
                    original_text=original_text,
                    lean_code=item.lean_code,
                    arg_kind=item.arg_kind,
                    computable=item.computable,
                    note=item.note,
                    deps=deps,
                    span_start=span.start,
                    span_end=span.end,
                    start_marker=item.start_marker,
                    end_marker=item.end_marker,
                )
            )
        row_gaps = gaps(block, claimed)
        for span in row_gaps:
            reason = next(
                (r for at, r in skip_reasons.get(name, []) if span.start <= at < span.end), ""
            )
            found.append(Gap(name, span, span.text(block), reason))
    return accepted, rejected, found


def _write_files(
    cfg: Config, batch_id: int, items: list[RenderedItem], dep_seqs: dict[str, SeqInfo]
) -> list[str]:
    """Writes Equiv + check modules for the computable items; returns lake targets."""
    targets: list[str] = []
    check_dir = cfg.check_dir / f"B{batch_id}"
    check_dir.mkdir(parents=True, exist_ok=True)
    for item in items:
        if not item.computable:
            continue
        seq = item.seq
        equiv_name = f"Equiv_{item.formula_hash}"
        equiv_path = cfg.loeis_dir / seq.bucket / seq.name / f"{equiv_name}.lean"
        equiv_path.parent.mkdir(parents=True, exist_ok=True)
        equiv_path.write_text(equiv_file_text(item, dep_seqs), encoding="utf-8")
        item.equiv_path = str(equiv_path.relative_to(cfg.loeis_dir.parent))
        item.equiv_module = seq.module(equiv_name)

        check_path = check_dir / f"{seq.name}_{item.formula_hash}.lean"
        check_path.write_text(
            check_file_text(item, batch_id, dep_seqs, cfg.terms), encoding="utf-8"
        )
        item.checked_terms = checkable_terms(seq, item.deps, dep_seqs, cfg.terms)
        item.check_path = str(check_path.relative_to(cfg.check_dir.parent))
        item.check_module = f"{CHECK_LIB}.B{batch_id}.{seq.name}_{item.formula_hash}"
        targets.append(item.check_module)
    return targets


def _classify(
    cfg: Config, items: list[RenderedItem], result: lean.BuildResult
) -> tuple[list[tuple[RenderedItem, str, list[str]]], list[RenderedItem]]:
    failed: list[tuple[RenderedItem, str, list[str]]] = []
    passed: list[RenderedItem] = []
    for item in items:
        if not item.computable:
            continue
        diags = result.diagnostics_for(item.equiv_path, item.check_path)
        starved = lean.dep_range_failures(result.output, item.seq.name)
        if not diags and result.timed_out:
            diags = ["build timed out; the definition is probably too slow to evaluate"]
        if starved and not diags:
            failed.append((item, STATUS_DEP_RANGE, starved))
        elif diags:
            kind = (
                STATUS_EVAL_MISMATCH
                if any("OEIS_CHECK_FAIL" in d for d in diags)
                or any(item.check_path and item.check_path in d for d in diags)
                else STATUS_COMPILE_ERROR
            )
            failed.append((item, kind, diags + starved))
        else:
            passed.append(item)
    return failed, passed


def _persist(
    conn: sqlite3.Connection,
    cfg: Config,
    batch_id: int,
    attempt: int,
    source_hash: dict[str, str],
    items: list[RenderedItem],
    statuses: dict[str, tuple[str, list[str]]],
) -> None:
    for item in items:
        status, diags = statuses.get(item.key, (STATUS_VERIFIED, []))
        offset = item.seq.offset
        points = lean.parse_failure_points(diags, offset) if diags else []
        dbm.upsert_item(
            conn,
            batch_id,
            oeis_name=item.seq.name,
            language=cfg.language,
            source_hash=source_hash.get(item.seq.name, ""),
            formula_hash=item.formula_hash,
            original_text=item.original_text,
            span_start=item.span_start,
            span_end=item.span_end,
            lean_kind="computable" if item.computable else "noncomputable",
            arg_kind=item.arg_kind,
            lean_code=item.lean_code,
            lean_file=item.equiv_path,
            check_file=item.check_path,
            depends_on=json.dumps(item.deps),
            status=status,
            failure_kind="" if status == STATUS_VERIFIED else status,
            failure_points=json.dumps(points),
            compiler_output="\n".join(diags)[:20000],
            verified_upto=item.checked_terms if status == STATUS_VERIFIED else 0,
            attempt=attempt,
            notes=item.note,
        )


def _persist_gaps(
    conn: sqlite3.Connection,
    cfg: Config,
    batch_id: int,
    source_hash: dict[str, str],
    rows: list[dbm.ProgramRow],
    found: list[Gap],
) -> None:
    """Records, per program block, everything the model left unclaimed."""
    by_seq: dict[str, list[Gap]] = {row.oeis_name: [] for row in rows}
    for gap in found:
        by_seq.setdefault(gap.oeis_name, []).append(gap)
    for name, seq_gaps in by_seq.items():
        dbm.replace_gaps(
            conn,
            batch_id,
            name,
            cfg.language,
            source_hash.get(name, ""),
            [
                (g.span.start, g.span.end, g.text, g.status, g.reason)
                for g in sorted(seq_gaps, key=lambda g: g.span.start)
            ],
        )


def _cleanup(cfg: Config, batch_id: int, drop: list[RenderedItem]) -> None:
    for item in drop:
        if item.equiv_path:
            path = cfg.loeis_dir.parent / item.equiv_path
            path.unlink(missing_ok=True)
    if not cfg.keep_check_files:
        shutil.rmtree(cfg.check_dir / f"B{batch_id}", ignore_errors=True)


def run_batch(
    conn: sqlite3.Connection,
    cfg: Config,
    rows: list[dbm.ProgramRow],
    max_attempts: int,
    batch_id: int | None = None,
    dry_run: bool = False,
    learn: bool = False,
    verbose: bool = True,
) -> str:
    seq_infos = {row.oeis_name: SeqInfo(row.oeis_name, row.title, row.offset, row.terms)
                 for row in rows}
    dep_seqs = collect_dep_infos(conn, cfg, rows)
    corpus = "\n".join(row.text for row in rows)
    skill = Skill(cfg.skill_dir / "SKILL.md").render(corpus)

    if batch_id is None and not dry_run:
        batch_id = dbm.create_batch(
            conn, cfg.language, cfg.model_name,
            sorted({r.oeis_name for r in rows}), max_attempts, skill,
        )
    prompt = batch_prompt(
        batch_id or 0, rows, seq_infos, dep_seqs, cfg.terms,
        dbm.verified_definitions(conn, sorted(dep_seqs), ALT_DEFS_PER_DEP),
    )

    if dry_run:
        print(f"===== SYSTEM/SKILL ({len(skill)} chars) =====\n{skill}")
        print(f"===== BATCH PROMPT =====\n{prompt}")
        return BATCH_PENDING

    assert batch_id is not None

    agent = build_agent(cfg, skill)
    stored = dbm.load_batch(conn, batch_id)
    history = load_history(stored["chat_history"]) if stored else []
    attempts_done = int(stored["attempts"]) if stored else 0
    dbm.update_batch(conn, batch_id, status=BATCH_RUNNING, skill_text=skill)

    source_hash = {row.oeis_name: row.source_hash for row in rows}
    status = BATCH_FAILED
    accepted: list[RenderedItem] = []
    # On a resumed batch the previous failures are the starting feedback.
    pending_feedback: list[str] = (
        [stored["last_error"]] if stored and history and stored["last_error"] else []
    )

    for attempt in range(1, max_attempts + 1):
        if history:
            user_prompt = repair_prompt(
                pending_feedback or ["(the previously reported problems are still open)"]
            )
        else:
            user_prompt = prompt
        run = agent.run_sync(user_prompt, message_history=history or None)
        history = list(run.all_messages())
        attempts_done += 1
        dbm.update_batch(
            conn, batch_id,
            attempts=attempts_done,
            chat_history=dump_history(history),
            usage=json.dumps(getattr(run.usage, "__dict__", {}), default=str),
        )

        accepted, rejected, block_gaps = _validate(run.output, rows, seq_infos, dep_seqs)
        targets = _write_files(cfg, batch_id, accepted, dep_seqs)
        build = lean.build(targets, cfg.build_timeout) if targets else lean.BuildResult(
            ok=True, timed_out=False, output=""
        )
        if not build.ok and not build.timed_out:
            unexplained = [
                i.check_module for i in accepted
                if i.computable and not build.diagnostics_for(i.equiv_path, i.check_path)
            ]
            if unexplained and len(unexplained) < len(targets):
                confirm = lean.build(unexplained, cfg.build_timeout)
                build.per_file.update(confirm.per_file)
                build.output += "\n" + confirm.output

        failed, passed = _classify(cfg, accepted, build)
        statuses: dict[str, tuple[str, list[str]]] = {
            item.key: (kind, diags) for item, kind, diags in failed
        }
        for item in accepted:
            if not item.computable:
                statuses[item.key] = (STATUS_NONCOMPUTABLE, [])
        _persist(conn, cfg, batch_id, attempts_done, source_hash, accepted, statuses)
        _persist_gaps(conn, cfg, batch_id, source_hash, rows, block_gaps)
        _cleanup(cfg, batch_id, [item for item, _, _ in failed])

        open_gaps = [g for g in block_gaps if not g.trivial and not g.reason]
        if verbose:
            noncomp = sum(1 for i in accepted if not i.computable)
            print(
                f"batch {batch_id} attempt {attempt}: {len(passed)} verified, "
                f"{noncomp} non-computable, {len(failed)} failed, {len(rejected)} rejected, "
                f"{len(open_gaps)} unformalized"
            )

        pending_feedback = [r.render() for r in rejected]
        for item, kind, diags in failed:
            joined = "\n".join(diags)[:2500]
            pending_feedback.append(
                f"{item.seq.name}, program starting "
                f"`{item.original_text.strip().splitlines()[0][:120]}`: "
                f"{'values disagree with the OEIS data' if kind == STATUS_EVAL_MISMATCH else 'Lean rejected the code'}:\n"
                f"```\n{joined}\n```"
            )
        pending_feedback += [g.render() for g in open_gaps]
        for r in rejected:
            dbm.upsert_item(
                conn, batch_id,
                oeis_name=r.oeis_name if r.oeis_name in seq_infos else rows[0].oeis_name,
                language=cfg.language,
                source_hash=source_hash.get(r.oeis_name, ""),
                formula_hash=snippet_hash(r.snippet + r.reason),
                original_text=r.snippet,
                status=STATUS_REJECTED,
                failure_kind=STATUS_REJECTED,
                compiler_output=r.reason,
                attempt=attempts_done,
            )

        if not pending_feedback:
            status = BATCH_OK if accepted else BATCH_FAILED
            break
        status = BATCH_PARTIAL if passed else BATCH_FAILED
        if attempt == max_attempts:
            break

    dbm.update_batch(
        conn, batch_id, status=status,
        last_error="" if status == BATCH_OK else "; ".join(pending_feedback)[:4000],
        chat_history=dump_history(history),
    )

    if learn and status == BATCH_OK:
        _learn(conn, cfg, batch_id, history)
    return status


def _learn(conn: sqlite3.Connection, cfg: Config, batch_id: int, history: list) -> None:
    agent = build_learning_agent(cfg)
    run = agent.run_sync(
        "Based on the batch you just formalized, what should be added to the skill document? "
        "Only genuinely new, reusable knowledge.",
        message_history=history,
    )
    if run.output.notes:
        dbm.add_skill_suggestions(conn, batch_id, cfg.language, "note", run.output.notes)
    if run.output.table_rows:
        dbm.add_skill_suggestions(conn, batch_id, cfg.language, "table_row", run.output.table_rows)


def resume_batch(
    conn: sqlite3.Connection, cfg: Config, batch_id: int, max_attempts: int, learn: bool
) -> str:
    stored = dbm.load_batch(conn, batch_id)
    if stored is None:
        raise SystemExit(f"batch {batch_id} not found")
    names = json.loads(stored["oeis_names"])
    rows = dbm.select_programs(
        conn, stored["language"], limit=len(names) * 8, seqs=names, include_attempted=True
    )
    keep: list[dbm.ProgramRow] = []
    seen: set[str] = set()
    for row in rows:
        if row.oeis_name in names and row.oeis_name not in seen:
            keep.append(row)
            seen.add(row.oeis_name)
    return run_batch(conn, cfg, keep, max_attempts, batch_id=batch_id, learn=learn)
