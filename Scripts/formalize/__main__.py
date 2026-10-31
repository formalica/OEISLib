"""Command line entry point: `python -m formalize ...`."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from . import db as dbm
from . import view
from .agent import load_history
from .config import Config
from .pipeline import defs_exists, group_batches, resume_batch, run_batch


def _common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--db", type=Path, default=None, help="path to Metadata/oeis.db")
    parser.add_argument("--language", default="maple", help="program language to formalize")
    parser.add_argument("--model", default=None, help="model name (default $OEIS_LLM_MODEL)")
    parser.add_argument("--terms", type=int, default=20, help="terms each formula is checked against")
    parser.add_argument("--timeout", type=int, default=900, help="per-batch lake build timeout (s)")
    parser.add_argument("--keep-check-files", action="store_true",
                        help="do not delete the generated Check/B<id> modules")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="oeis-formalize", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    run = sub.add_parser("run", help="formalize new program blocks")
    _common(run)
    run.add_argument("--batch-size", type=int, default=5,
                     help="program blocks per LLM call, from distinct sequences")
    run.add_argument("--batches", type=int, default=1, help="number of batches to process")
    run.add_argument("--retry", type=int, default=1,
                     help="maximum LLM attempts per batch (1 = no repair round)")
    run.add_argument("--bucket", action="append", default=None, help="restrict to a bucket, e.g. A000")
    run.add_argument("--seq", action="append", default=None, help="restrict to an A-number")
    run.add_argument("--include-attempted", action="store_true",
                     help="also pick blocks that were tried before")
    run.add_argument("--dry-run", action="store_true", help="print the prompt and exit")
    run.add_argument("--learn", action="store_true",
                     help="ask for skill improvements after a fully successful batch")

    retry = sub.add_parser("retry", help="continue a stored batch in its own conversation")
    _common(retry)
    retry.add_argument("--batch-id", type=int, required=True)
    retry.add_argument("--retry", type=int, default=1)
    retry.add_argument("--learn", action="store_true")

    show = sub.add_parser(
        "show",
        help="inspect a stored batch, or a sequence's program coverage",
    )
    _common(show)
    target = show.add_mutually_exclusive_group(required=True)
    target.add_argument("--batch-id", type=int, help="show one formalization batch")
    target.add_argument("--seq", help="show one sequence's program blocks, colour-coded")
    show.add_argument("--color", choices=("auto", "always", "never"), default="auto")
    show.add_argument("--limit", type=int, default=1200,
                      help="characters printed per quoted text")
    show.add_argument("--history", action="store_true",
                      help="also print the stored conversation with the model")

    stats = sub.add_parser("stats", help="item counts per status")
    _common(stats)

    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    cfg = Config.from_env(
        db_path=args.db,
        language=args.language,
        model_name=args.model,
        terms=args.terms,
        build_timeout=args.timeout,
        keep_check_files=getattr(args, "keep_check_files", False),
    )
    conn = dbm.connect(cfg.db_path)

    if args.command == "stats":
        for row in dbm.stats(conn, cfg.language):
            print(f"{row['status']:>24}  {row['n']}")
        for row in dbm.gap_stats(conn, cfg.language):
            print(f"{row['status']:>24}  {row['n']}")
        return 0

    if args.command == "show":
        paint = view.Painter(view.want_color(args.color))
        if args.seq:
            name = args.seq.upper()
            programs = dbm.sequence_programs(conn, name)
            if not programs:
                print(f"no program blocks stored for {name}", file=sys.stderr)
                return 1
            view.show_sequence(
                programs, dbm.sequence_spans(conn, name), dbm.sequence_gaps(conn, name),
                name, paint,
            )
            return 0

        batch = dbm.load_batch(conn, args.batch_id)
        if batch is None:
            print(f"batch {args.batch_id} not found", file=sys.stderr)
            return 1
        history = load_history(batch["chat_history"]) if args.history else []
        items = dbm.batch_items(conn, args.batch_id)
        view.show_batch(
            batch,
            items,
            dbm.item_sources(conn, [i["id"] for i in items]),
            dbm.batch_gaps(conn, args.batch_id),
            history,
            paint,
            args.limit,
        )
        return 0

    if args.command == "retry":
        print(resume_batch(conn, cfg, args.batch_id, args.retry, args.learn))
        return 0

    rows = dbm.select_programs(
        conn,
        cfg.language,
        limit=args.batch_size * args.batches * 4,
        buckets=args.bucket,
        seqs=args.seq,
        include_attempted=args.include_attempted,
    )
    rows = [r for r in rows if defs_exists(cfg, r.oeis_name)]
    if not rows:
        print("nothing to do", file=sys.stderr)
        return 1

    batches = group_batches(rows, args.batch_size)[: args.batches]
    failures = 0
    for batch in batches:
        status = run_batch(
            conn, cfg, batch, args.retry, dry_run=args.dry_run, learn=args.learn
        )
        if status not in ("BATCH_OK", "BATCH_PENDING"):
            failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
