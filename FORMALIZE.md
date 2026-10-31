# Program formalization pipeline

How OEIS *program* blocks (Maple first, other languages later) are translated into Lean 4 by
an LLM, validated against the OEIS data, and recorded in `Metadata/oeis.db`.

This document describes what is implemented. For the overall project goal see [SPEC.md](SPEC.md).

---

## 1. Overview

```
oeisdata/seq/*.seq
        │  lake exe oeis-ingest        (Lean)
        ▼
  program table  ──────────────────────────────────────────┐
        │                                                  │
        │  python -m formalize run     (Python)            │
        ▼                                                  │
  batch of N Maple blocks from N distinct sequences        │
        │                                                  │
        ├─ skill text (function table filtered to the batch)│
        ├─ per-sequence context (title, offset, terms, API) │
        └─ referenced sequences + up to 3 alternative defs  │
        │                                                  │
        ▼  one LLM call, structured output                 │
  list of { oeis_name, start_marker, end_marker,           │
            lean_code, arg_kind, computable, note }         │
  plus  skipped[] { oeis_name, start_marker, reason }       │
        │                                                  │
        ▼  span resolution, shape check, arg_kind check     │
  OEISLib/<bucket>/<seq>/Equiv_<hash>.lean                    │
  Check/B<batch>/<seq>_<hash>.lean                          │
  program_gap  ← whatever no item claimed                   │
        │                                                  │
        ▼  lake build                                       │
  compile error / eval mismatch / dep range / verified      │
        │                                                  │
        ▼                                                  ▼
  formalization_batch + formalization_item ────────── resume / retry
```

One LLM call handles a whole batch. One Lean build validates the whole batch. Failures are
attributed back to individual items and fed to the model as a repair message inside the same
conversation.

---

## 2. Ingesting program blocks

The Lean ingest previously read only `%S/%T/%U`, `%N`, `%O`, `%K`, `%F`. It now also reads
program tags into a new `program` table:

| OEIS tag | `language` |
| --- | --- |
| `%p` | `maple` |
| `%t` | `mathematica` |
| `%o` | taken from the `(Language)` marker on the first line — `pari`, `python`, `haskell`, ... |

Consecutive lines of the same tag form **one block**, joined with `\n`, stored verbatim:

- `%p` / `%t` are **never** split. A Maple or Mathematica block routinely merges several
  programs behind an `# Alternative:` / `(* Alternative: *)` comment, and splitting on that
  comment is unreliable (many entries use other wording, or none at all). Splitting a block
  into individual programs is the LLM step's job, and the leftovers are tracked as gaps —
  see [§5.1](#51-programs-are-delimited-by-markers).
- a `%o` run **is** cut at every `(Lang)` marker, because one `%o` run usually holds several
  languages back to back. The marker also sets `language`.

`hash` is a 16 hex-char `String.hash` of the block text and is what the Python side uses to
tell whether a block was already attempted.

Run:

```bash
lake build oeis-ingest && lake exe oeis-ingest
```

---

## 3. Batch selection

`select_programs` in [Scripts/formalize/db.py](Scripts/formalize/db.py) picks blocks that:

- match the requested `language`,
- belong to a sequence with at least one known term,
- are **not** `tabl` / `tabf` — multi-parameter sequences are out of scope for now,
- have no `formalization_source` row with the same `source_hash` (unless `--include-attempted`).

The CLI additionally drops sequences whose `OEISLib/.../Defs.lean` does not exist yet, because
the generated `Equiv` file imports it.

`group_batches` then packs rows into batches of `--batch-size`, with the constraint that **one
batch never contains two blocks of the same sequence**. That keeps marker resolution
unambiguous: an anchor is always searched inside exactly one block.

---

## 4. The prompt

### 4.1 Skill document, filtered

`Skills/maple/SKILL.md` holds the general instructions plus a Maple → Lean function table
between two markers:

```markdown
<!-- BEGIN FUNCTION TABLE -->
| Maple | Usage | Lean 4 / Mathlib | Notes |
| --- | --- | --- | --- |
| `binomial` | ... | `Nat.choose n k` | ... |
<!-- END FUNCTION TABLE -->
```

The first column is a comma-separated list of Maple names owned by that row. Before each call,
`Skill.render` keeps only the rows whose keys occur in the batch's Maple text — identifier keys
match whole tokens, operator keys such as `!` match as substrings. A row with key `*` is always
kept. The rendered skill is stored per batch in `formalization_batch.skill_text`, so a stored
batch can be replayed with exactly the text the model saw.

### 4.2 Per-sequence context

For every block in the batch the prompt states the title, OEIS offset, the main definition's
signature, the **required** return type, the allowed `arg_kind` values, and the first `--terms`
known terms.

### 4.3 Referenced sequences

`referenced_sequences` scans the Maple text for `A\d{6}` tokens. For each referenced sequence
that has both `Defs.lean` and `Data.lean`, the prompt adds its title, offset, the three Lean
entry points (`Axxxxxx`, `.fn : Nat → r`, `.fz : Int → r`), its first terms, **and up to three
alternative definitions already verified for it** (`verified_definitions`, newest and
best-validated first). This is the "3 alternative definitions" requirement — it grows naturally
as more sequences get formalized.

---

## 5. Structured output contract

```python
class FormalizedProgram(BaseModel):
    oeis_name: str        # A-number this item belongs to
    start_marker: str     # first characters of the program, verbatim
    end_marker: str       # last characters, verbatim, author credit included
    lean_code: str        # Lean 4 defining `formula`
    arg_kind: Literal["Nat", "PNat", "NatSub", "Int", "IntSub"]
    computable: bool
    note: str = ""

class SkippedProgram(BaseModel):
    oeis_name: str
    start_marker: str
    reason: str

class BatchResult(BaseModel):
    items: list[FormalizedProgram]
    skipped: list[SkippedProgram] = []
```

A Maple block usually merges several independent programs (a `proc`, a `seq(...)` driver, an
alternative approach). The model is asked to split them and return one item per program.

### 5.1 Programs are delimited by markers

The model does **not** echo a whole program back. Long verbatim copies drift — whitespace gets
normalized, comments get dropped, `...` creeps in — and a single failed match used to silently
lose the whole program.

Instead each item carries two short anchors, and
[Scripts/formalize/spans.py](Scripts/formalize/spans.py) turns them into a `[start, end)` span
of the raw block:

- `start_marker` is searched in the block;
- `end_marker` is searched at or after that position; the span ends after it.

Constraints, all enforced and all stated in the prompt and the skill:

- both markers at least `MIN_MARKER` (6) characters, copied character for character;
- `start_marker` before `end_marker`;
- the spans of two items of the same sequence must not overlap;
- `end_marker` should extend through the trailing credit comment
  (`end proc: # _R. J. Mathar_, Nov 15 2014`), so no orphan attribution line is left behind
  and mistaken for a missed program.

Anchors can legitimately be ambiguous (the same `end proc:` appears twice). `resolve` therefore
enumerates every candidate span per item, orders items by fewest candidates first, and
**backtracks**, so neighbouring items pin an ambiguous one down. If no global assignment
exists it falls back to greedy placement, so the items that do fit still survive.

Rejection messages are specific — not found, only matches after collapsing whitespace, only
the first characters match, too short, every candidate overlaps — and are fed back verbatim in
the repair round.

`original_text` still exists downstream: it is the resolved `block[start:end]`, and it is what
the `Equiv_<hash>` file name and `formula_hash` (`hex(String.hash)` of it) are derived from.

### 5.2 Gaps: what nobody formalized

Once every accepted item has a span, `spans.gaps` computes the **complement** in the block.
Each remaining stretch is trimmed of surrounding whitespace and recorded in `program_gap`:

| status | meaning |
| --- | --- |
| `STATUS_UNFORMALIZED` | a real stretch of program text nothing claimed |
| `STATUS_GAP_TRIVIAL` | blank lines, stray delimiters, or a comment / author credit only |

`spans.is_trivial` makes that call: it drops comment-only lines (`# ...`, `(* ... *)`, `-- ...`,
`/* ... */`) and blank lines, then checks whether anything but `;:,)` whitespace is left.

A non-trivial gap is a **defect**. It is appended to the repair feedback with the offending
text quoted, so the next attempt in the same conversation must either translate it or list it
under `skipped` with a reason. A batch with an open gap cannot reach `BATCH_OK`.

When the model does list something under `skipped`, the reason is attached to whichever gap
contains that `start_marker`, and the gap stops counting as open.

This is what caught the original defect: A000002's `%p` block holds two Maple programs, the
model returned only the Cloitre one, and the first program silently vanished. It is now
recorded as `STATUS_UNFORMALIZED` and reported back.

### 5.3 Shape checks

`validate_lean_code` rejects code that does not define exactly one `formula`, or that contains
`import` / `namespace` / `section` / `#eval` / `#check` / `#print`. Helper definitions must be
`formula_`-prefixed. The pipeline owns the imports, the namespace and the theorem.

Two further rejections happen in `_validate`:

- `arg_kind` not allowed for the sequence's offset,
- `lean_code` calling **its own** sequence (`formula` *is* that definition — a recurrence must
  be written out),
- `lean_code` calling a sequence with no usable Lean definition.

---

## 6. Generated Lean

### 6.1 `Equiv_<hash>.lean`

`<hash>` is `hex(String.hash original_text)` (Lean's `String.hash`, ported in
`Scripts/formalize/hashing.py` and the same function the Lean tools use), so the same snippet always
maps to the same file.

```lean
import OEISLib.A001.A001006.Defs
import OEISLib.A000.A000108.Defs

/-! ... title, original Maple source, chosen types ... -/

namespace A001006.Equiv_780fb6e22f15f180

def formula : Nat → Nat := fun n =>
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * A000108.fn k

/-- The formalized Maple program agrees with the main definition. -/
theorem formula_eq (n : A001006.argType) :
    formula n = A001006 n := sorry

end A001006.Equiv_780fb6e22f15f180
```

The theorem is **appended by the pipeline**, never requested from the model. It is `sorry` on
purpose: this stage only formalizes, proofs come later.

### 6.2 `Check/B<batch>/<seq>_<hash>.lean`

Every main definition in `OEISLib` is still `sorry`, so a translation that calls `A000108.fn`
cannot be executed against the real definition. The check module therefore rebuilds the
translation against **data-backed shims**:

```lean
namespace Oeis.Check.Shim
def A000108.data : List Nat := [1, 1, 2, 5, 14, ...]
def A000108.fz (n : Int) : Nat :=
  let i := n - (0 : Int)
  if 0 ≤ i ∧ i < (A000108.data.length : Int) then A000108.data[i.toNat]!
  else panic! s!"OEIS_DEP_RANGE A001006 needs A000108 n={n}"
def A000108.fn (n : Nat) : Nat := A000108.fz (n : Int)
def A000108 : Nat → Nat := fun n => A000108.fz (n : Int)
end Oeis.Check.Shim

namespace Check.B0.A001006_780fb6e22f15f180
def formula : Nat → Nat := ...   -- same body, dependency calls redirected
#eval Oeis.Check.report "A001006" 0 [expected...] [formula 0, formula 1, ...]
end
```

`Oeis.Check.report` in [Check/Basic.lean](Check/Basic.lean) throws on the first disagreement, so
`#eval` turns a wrong translation into a build error carrying a machine-readable
`OEIS_CHECK_FAIL A001006: n=3: expected 5, got 4; ...` line.

Asking a shim for an index OEIS does not list panics with `OEIS_DEP_RANGE`, which is a distinct
outcome from "wrong": the translation may well be correct but unverifiable.

`checkable_terms` limits how many terms are evaluated to what the dependencies can actually
supply.

Check modules are deleted after the batch is recorded unless `--keep-check-files` is given.

---

## 7. Validation and classification

One `lake build` runs all check modules of the batch. `_attribute` parses
`error: path:line:col: message` and groups diagnostics per file. If the build failed but some
items got no diagnostic (Lake stops early), those targets are rebuilt alone so every failure is
attributed.

| Outcome | `status` |
| --- | --- |
| built and all evaluated terms match | `STATUS_VERIFIED` |
| Lean rejected the code | `STATUS_COMPILE_ERROR` |
| built, but values disagree with OEIS | `STATUS_EVAL_MISMATCH` |
| needed a dependency term OEIS does not list | `STATUS_DEP_RANGE` |
| `computable = false`, never compiled | `STATUS_NONCOMPUTABLE` |
| span / shape / arg_kind rejection, never written | `STATUS_REJECTED` |

`parse_failure_points` turns `OEIS_CHECK_FAIL` into
`[{"n": "3", "expected": "5", "got": "4"}, ...]` stored in `formalization_item.failure_points`,
which is the "failure points (argument values)" record.

Only `STATUS_VERIFIED` items keep their `Equiv` file; everything else is deleted from `OEISLib`
but stays in the database.

### Non-computable items

`computable = false` items are stored with their Lean code and never compiled — they are for
generating functions, real/complex analysis, asymptotics. Later stages that implement real-number
and generating-function validation will pick them up from the database.

---

## 8. Retry and resume

- `--retry N` — up to `N` LLM attempts **inside one batch**, in one conversation. After each
  failed attempt the model is sent `repair_prompt`, listing every rejection and every compiler
  diagnostic, and asked to return the complete list again with those problems fixed. Default is
  `1`, i.e. no repair round.
- `python -m formalize retry --batch-id K --retry M` — reopens a stored batch later. The full
  message history is restored from `formalization_batch.chat_history` (pydantic-ai
  `ModelMessagesTypeAdapter`), and `last_error` becomes the opening feedback, so the model
  continues **in the same context** rather than starting over.

Batch status: `BATCH_PENDING` → `BATCH_RUNNING` → `BATCH_OK` / `BATCH_PARTIAL` / `BATCH_FAILED`.

---

## 9. Skill self-improvement

With `--learn`, a fully successful batch is followed by a second call on the same conversation
asking for genuinely new, reusable knowledge. The result lands in `skill_suggestion`
(`kind = 'note' | 'table_row'`, `applied = 0`). Suggestions are **not** applied automatically —
they are reviewed and merged into `Skills/<language>/SKILL.md` by hand.

---

## 10. Database

Four new tables, all created by the Lean ingest's `schemaSql` and re-created defensively by
the Python side.

### `program`

| Column | Notes |
| --- | --- |
| `oeis_name`, `language`, `block_index` | PRIMARY KEY |
| `source_tag` | `p` / `t` / `o` |
| `text` | block verbatim |
| `hash` | 16 hex chars, used as `formalization_item.source_hash` |
| `line_count`, `status` | |

### `formalization_batch`

| Column | Notes |
| --- | --- |
| `id` | AUTOINCREMENT, appears in `Check/B<id>/` |
| `language` | `maple` today; the same machinery serves other languages |
| `model`, `status`, `attempts`, `max_attempts` | |
| `oeis_names` | JSON array of the sequences in the batch |
| `chat_history` | serialized pydantic-ai messages — what makes resume work |
| `skill_text` | the filtered skill actually sent |
| `last_error`, `usage`, `created_at`, `updated_at` | |

### `formalization_item`

One row per program the model extracted. `UNIQUE (oeis_name, producer, formula_hash, lean_kind)`;
the original text and its span are in `formalization_source` (one row, `ord = 0`, for an LLM item).

| Column | Notes |
| --- | --- |
| `batch_id`, `oeis_name`, `producer` | `producer = 'llm'` |
| `formula_hash` | `hex(String.hash)` of the resolved `original_text`; also the `Equiv_<hash>` file name |
| `computable`, `arg_kind`, `lean_code` | model output |
| `lean_file`, `check_file` | generated paths |
| `depends_on` | JSON array of referenced A-numbers |
| `status`, `failure_kind` | see the table in §7 |
| `failure_points` | JSON, e.g. `[{"n":"3","expected":"5","got":"4"}]` |
| `compiler_output` | truncated to 20 kB |
| `verified_upto` | number of terms actually checked |
| `attempt`, `notes`, `created_at`, `updated_at` | |

### `formalization_source`

One row per original text of an item: `item_id`, `ord`, `language`, `block_index`,
`source_hash` (`program.hash` of the block), `original_text`, `span_start`, `span_end` (NULL for a
rejected item, whose text could not be placed). `PRIMARY KEY (item_id, ord)`, `ON DELETE CASCADE`.

### `skill_suggestion`

`id`, `batch_id`, `language`, `kind`, `text`, `applied`, `created_at`.

### `program_gap`

One row per stretch of a program block that no item claimed.
`UNIQUE (oeis_name, language, source_hash, span_start, span_end)`; rewritten wholesale for a
block every time that block is processed, so it never goes stale.

| Column | Notes |
| --- | --- |
| `batch_id` | the batch that produced this view of the block |
| `oeis_name`, `language`, `source_hash` | identifies the block |
| `span_start`, `span_end`, `text` | the uncovered stretch, whitespace-trimmed |
| `status` | `STATUS_UNFORMALIZED` or `STATUS_GAP_TRIVIAL` |
| `reason` | the model's own explanation, when it listed the program under `skipped` |
| `created_at`, `updated_at` | |

---

## 11. Commands

```bash
# one batch of 5 Maple blocks, one repair round on failure
python -m formalize run --batch-size 5 --batches 1 --retry 2

# restrict to a bucket or specific sequences
python -m formalize run --bucket A000 --seq A000045

# see exactly what would be sent, without calling the model
python -m formalize run --seq A000045 --dry-run

# continue a stored batch in its original conversation
python -m formalize retry --batch-id 3 --retry 2

python -m formalize show --batch-id 3 [--history] [--limit N] [--color auto|always|never]
python -m formalize show --seq A000002 [--color auto|always|never]
python -m formalize stats
```

Common flags: `--db`, `--language`, `--model`, `--terms`, `--timeout`, `--keep-check-files`,
`--include-attempted`, `--learn`.

### Inspecting coverage: `show --seq`

`show --seq A000002` prints **every** program block OEIS has for that sequence — Maple,
Mathematica, PARI, Python, Haskell — colour-coded character by character:

- each formalized program gets its **own colour** from a fixed palette, keyed to its
  `formula_hash`;
- everything unformalized is **red**, whether it is a recorded `program_gap` or a block that
  was never processed at all;
- a legend under each block maps colour → span → `formula_hash` and status, and prints the
  percentage of the block that is formalized plus the number of real (non-trivial) gaps.

This is the fastest way to see that, say, only one of A000002's two Maple programs made it
through. Colour is auto-detected from the tty; `--color always` keeps the escapes when piping.

### Inspecting a batch: `show --batch-id`

Prints the batch metadata, a parsed `usage` summary (requests / tokens / cost), the size of the
filtered skill, and `last_error`. Then, per item: the resolved span, `arg_kind`, computability,
dependencies, verified term count, the model's note, the original program text, the generated
`lean_code`, parsed failure points and compiler output. Then every recorded gap, real ones
flagged in red together with the model's `skipped` reason when it gave one.

`--history` additionally replays the stored conversation turn by turn — system prompt, filtered
skill, batch prompt, each structured response, each repair round. That is what tells you
whether a missing program was the model's fault or the pipeline's. `--limit` caps how much of
each quoted text is printed (default 1200 characters).

Environment: `OEIS_LLM_MODEL` (default `anthropic:claude-sonnet-4-5`). A `provider:model` name
uses any pydantic-ai provider; a bare name uses the OpenAI-compatible endpoint given by
`OEIS_LLM_BASE_URL` / `OEIS_LLM_API_KEY`.

Setup:

```bash
uv venv && uv pip install -e .
PYTHONPATH=Scripts .venv/bin/python -m formalize stats
```

### Offline self-test

`PYTHONPATH=Scripts .venv/bin/python -m formalize.selftest` renders three hand-written
translations (one correct recurrence, one correct sum calling another sequence, one deliberately
wrong) and runs the whole render → build → classify path with **no model call**. Expected
result: two `PASS`, one `FAIL ... STATUS_EVAL_MISMATCH` with parsed failure points, plus a list
of `UNFORMALIZED` gaps — the fixtures deliberately anchor only one program per block, so the
gap detector has something to report.

---

## 12. Why the agent has no tools

Lean is compiled by the pipeline on every attempt, unconditionally. Giving the model a "compile
this" tool would only let it spend tokens deciding to do something that is going to happen
anyway. The model returns structured output; the pipeline decides everything else.

---

## 13. Known limitations

- `tabl` / `tabf` sequences are skipped.
- A translation is only validated as far as the terms OEIS lists, and only as far as the terms
  of the sequences it references (`STATUS_DEP_RANGE`).
- `formula_eq` is always `sorry`.
- Dependencies are resolved through data shims, so a verified item proves agreement with the
  OEIS data, not with the referenced sequence's eventual Lean definition.
- Only `maple` is wired up; `language` is a column and a flag everywhere so `mathematica` /
  `pari` / `python` need a new `Skills/<language>/SKILL.md` and nothing else structural.
