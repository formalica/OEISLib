#!/usr/bin/env python3
"""Mine OEIS %N title templates: sequences whose names differ only by constants.

Every `.seq` file carries exactly one `%N` line (id + human title). Titles that
become identical after erasing all constants form one *template*: its member
sequences differ only by the constant parameters (or small arithmetic
expressions built on them) sitting in those slots. This script extracts all
titles, normalizes them, groups by the resulting skeleton, and writes a
frequency-sorted markdown table of every template with >= min-count members.

Normalization rules (in order):
  * lowercase;
  * spelled-out number words -> digits ("twenty-one" -> 21, "once" -> 1, ...);
  * sequence references `Annnnnn` -> `{AK}` slots (K = occurrence index);
  * remaining integer literals -> `{pK}` slots (K = occurrence index);
  * collapse whitespace, strip trailing period.

Example: "Divisors of 492." and "Divisors of 170." both become
`divisors of {p1}` — the two sequences are instances of one template.

Usage:
    python3 Scripts/name_templates.py                    # walk the .seq tree
    python3 Scripts/name_templates.py --names-file FILE  # reuse "%N ..." lines
"""
import argparse
import os
import re
import sys
from collections import Counter, defaultdict

ONES = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
        "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
        "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
        "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19}
TENS = {"twenty": 20, "thirty": 30, "forty": 40, "fifty": 50,
        "sixty": 60, "seventy": 70, "eighty": 80, "ninety": 90}
WORDVALS = dict(ONES)
WORDVALS.update(TENS)
WORDVALS.update({"once": 1, "twice": 2, "thrice": 3, "hundred": 100})

# hyphenated/spaced compounds first ("twenty-one"), then single words
COMPOUND_RE = re.compile(
    r"(?<![a-z])(" + "|".join(TENS) + r")[ -](" + "|".join(ONES) + r")(?![a-z])")
WORD_RE = re.compile(r"(?<![a-z])(" + "|".join(WORDVALS) + r")(?![a-z])")
PARAM_RE = re.compile(r"\ba\d{6}\b|\d+")   # A-refs are lowercased before here
LINE_RE = re.compile(r"%N (A\d+) (.*)$")

MAX_TPL_LEN = 160      # truncate longer template cells with "..."
MAX_EXAMPLES = 5       # spread-out example member ids shown per row


def canon(name: str) -> str:
    """Title -> skeleton with {pK}/{AK} parameter slots."""
    s = name.lower()
    s = COMPOUND_RE.sub(lambda m: str(TENS[m.group(1)] + ONES[m.group(2)]), s)
    s = WORD_RE.sub(lambda m: str(WORDVALS[m.group(1)]), s)
    out, pos, na, np_ = [], 0, 0, 0
    for m in PARAM_RE.finditer(s):
        out.append(s[pos:m.start()])
        pos = m.end()
        if m.group(0)[0] == "a":
            na += 1
            out.append("{A%d}" % na)
        else:
            np_ += 1
            out.append("{p%d}" % np_)
    out.append(s[pos:])
    return re.sub(r"[ \t]+", " ", "".join(out)).strip().rstrip(".").strip()


def titles_from_seq_dir(seq_dir: str):
    """Yield (Axxxxxx, title) for every %N line under the .seq tree."""
    for root, _dirs, files in os.walk(seq_dir):
        for fn in files:
            if not fn.endswith(".seq"):
                continue
            try:
                with open(os.path.join(root, fn), encoding="utf-8",
                          errors="replace") as f:
                    for line in f:
                        m = LINE_RE.match(line.rstrip("\n"))
                        if m:
                            yield m.group(1), m.group(2)
                            break
            except OSError as e:
                print("warning: cannot read %s: %s" % (fn, e),
                      file=sys.stderr)


def titles_from_names_file(path: str):
    """Yield (Axxxxxx, title) from a file of raw `%N ...` lines."""
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            m = LINE_RE.match(line.strip())
            if m:
                yield m.group(1), m.group(2)


def main():
    parser = argparse.ArgumentParser(
        description="Group OEIS %N titles into constant-parameter templates.")
    parser.add_argument("--seq-dir", default="oeisdata/seq",
                        help="directory tree of *.seq files (default %(default)s)")
    parser.add_argument("--names-file", default=None,
                        help="read raw `%%N Axxxxxx title` lines from FILE instead "
                             "of walking --seq-dir")
    parser.add_argument("--out", default="Scripts/templates.txt",
                        help="output table path (default %(default)s)")
    parser.add_argument("--min-count", type=int, default=25,
                        help="report templates with at least this many members "
                             "(default %(default)s)")
    args = parser.parse_args()

    titles = (titles_from_names_file(args.names_file) if args.names_file
              else titles_from_seq_dir(args.seq_dir))
    tpl_count = Counter()
    members = defaultdict(list)
    for aid, title in titles:
        t = canon(title)
        tpl_count[t] += 1
        members[t].append(aid)

    qual = [(t, c) for t, c in tpl_count.items() if c >= args.min_count]
    qual.sort(key=lambda tc: (-tc[1], tc[0]))
    for ids in members.values():
        ids.sort()
    total = sum(tpl_count.values())
    covered = sum(c for _, c in qual)

    lines = []
    w = lines.append
    w("OEIS %%N name templates (>= %d sequences sharing one abstracted name "
      "pattern)" % args.min_count)
    w("=" * 79)
    w("")
    w("Method:")
    w("  All %%N (name) fields of the %s .seq files were extracted and"
      % f"{total:,}")
    w("  normalized: lowercased; integer literals and spelled-out number words")
    w("  replaced by {pK} slots; references to other sequences (Annnnnn)")
    w("  replaced by {AK} slots.")
    w("  Names that then coincide belong to one template: its members differ only")
    w("  by the constant parameters (or small arithmetic expressions built on")
    w("  them) in those slots.")
    w("")
    w("Stats:")
    w("  sequences total ............ %s" % f"{total:,}")
    w("  distinct raw templates ..... %s" % f"{len(tpl_count):,}")
    w("  templates with >= %d ....... %s" % (args.min_count, f"{len(qual):,}"))
    w("  sequences covered by them .. %s (%.1f%%)"
      % (f"{covered:,}", 100.0 * covered / total))
    w("")
    w("Placeholders: {pK} = K-th integer constant, {AK} = K-th sequence reference.")
    w("Templates longer than %d chars are truncated with '...'." % MAX_TPL_LEN)
    w("")
    w("|  # | count | template | example members |")
    w("|---:|------:|----------|-----------------|")
    for i, (t, c) in enumerate(qual, 1):
        ids = members[t]
        step = max(1, len(ids) // MAX_EXAMPLES)
        ex = ids[::step][:MAX_EXAMPLES]
        disp = t if len(t) <= MAX_TPL_LEN else t[:MAX_TPL_LEN].rstrip() + "..."
        disp = disp.replace("|", "\\|")   # keep markdown table intact
        w("| %3d | %5d | %s | %s |" % (i, c, disp, ", ".join(ex)))

    with open(args.out, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    print("wrote %s: %d templates (>= %d), %d/%d sequences covered"
          % (args.out, len(qual), args.min_count, covered, total))


if __name__ == "__main__":
    main()
