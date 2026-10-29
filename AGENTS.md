# AGENTS.md

Instructions for AI agents working in this repository. The dated progress log is in [PROGRESS.md](PROGRESS.md).
(VS Code / Copilot automatically loads `AGENTS.md`, so this is the file to keep current.)

## RULE 0 — Keep `Impl/` up to date (MANDATORY)

`Impl/` documents how the project is actually implemented: [Impl/Database.md](Impl/Database.md),
[Impl/Templates.md](Impl/Templates.md), and [Impl/README.md](Impl/README.md) as the index.

**After every change to code, schema, commands or behavior, update the matching `Impl/*.md` in the
same turn** (and create one if no document covers the area). Counts, file names and flags in them
must match what the code does now.

Each `Impl/` document describes the implementation and ends with a **Differences from Spec.md**
section. [Spec.md](Spec.md) does not cover every implementation detail, so that section contains
**only** places where Spec.md states something and the implementation does otherwise (one row per
contradiction: what Spec.md says | what the implementation does), sorted by importance with the most important row first. Importance is how much the difference changes the data, the verification results or the generated Lean code; naming and cosmetic differences come last. Do not put there:

- details Spec.md is silent about (they belong in the implementation sections),
- things that match Spec.md,
- inconsistencies inside Spec.md itself.

When a contradiction is resolved (code or Spec.md changed), delete its row.

## RULE 1 — Keep this file up to date (MANDATORY)

**After every user prompt you act on, you MUST update this file and [PROGRESS.md](PROGRESS.md) before finishing your turn.**

- Append what you did to [PROGRESS.md](PROGRESS.md) with the date. Progress is never written in this file.
- Update [Current state](#current-state), [Database schema](#database-schema), and
  [Commands](#commands) whenever they change.
- Update [Open items / next steps](#open-items--next-steps) here: add new open items and next steps, and remove what is done. The existing items stay here until they are moved into `Impl/*.md`.
- Record decisions the user made (naming, formats, tool choices) under [Decisions](#decisions)
  so they are not re-litigated.
- Keep it short. This is a working index, not documentation. Delete stale lines instead of
  letting the file grow.

This rule is repeated at the [bottom of the file](#rule-reminder) on purpose. Do not skip it.

## Project

Formalize OEIS sequences in Lean 4 + Mathlib. The end goal (see [SPEC.md](SPEC.md) and
[OEIS.md](OEIS.md)) is to generate, per sequence `Axxxxxx`, a directory `Axxx/Axxxxxx/` with:

- `Defs.lean` — main definition (`Axxxxxx`, `argType`, `retType`, `offset`, `fn`, `fz`, `prop`,
  coherence theorems)
- `Data.lean` — known terms + `data_eq` / `data_eq_fn` / `data_eq_fz`
- `Equiv_<hash>.lean` — alternative definitions + equivalence to the main definition
- `Basic_<hash>.lean` — properties that do not fully determine the sequence

Raw OEIS data lives in `oeisdata/seq/A<bucket>/A<number>.seq` (398,471 files, git-ignored,
official OEIS "internal format").

## Current state

Step 1 of SPEC.md (metadata tables) is **done**, and the `Defs.lean` / `Data.lean` skeleton
generator is **done**. The **Maple → Lean LLM formalization pipeline is implemented** (see
[FORMALIZE.md](FORMALIZE.md)); `%F` formula parsing / real main definitions are not started.
**`oeis-template` writes `formalization_item`** (four templates, 20,667 items; see
[Impl/Templates.md](Impl/Templates.md)) instead of generating Lean files; `oeis-gen` does not yet read items.

The ingest executable walks `oeisdata/seq`, parses every `.seq` file, and populates a SQLite
database at `Metadata/oeis.db` (git-ignored, ~360 MB). The generator reads that DB and writes
`LOEIS/<bucket>/<name>/{Defs,Data}.lean` where every declaration is `sorry`.

### Generated skeleton shape

`argType` from the OEIS offset:

| offset | `argType` | `fn` generated? |
| --- | --- | --- |
| `0` | `Nat` | yes |
| `1` | `PNat` | yes |
| `k ≥ 2` | `{n : Nat // k ≤ n}` | yes |
| `k < 0` | `{n : Int // k ≤ n}` | no (SPEC: skip `fn` for Int-based argTypes) |

`retType` is `Int` if any known term is negative, else `Nat`.

`tabl` / `tabf` sequences (31,428 of them) are two-argument in reality; for now they get a
flattened API and every name gains a prefix: `flat`, `flatArgType`, `flatRetType`, `flatOffset`,
`flatFn`, `flatFz`, `flatProp`, `flatData`, and `flat_prop_correct`, `flat_fn_eq`, `flat_fz_eq`,
`flat_fn_eq_fz`, `flat_data_eq`, `flat_data_eq_fn`, `flat_data_eq_fz`. Non-flat sequences keep
the main definition at top level (`def A000001 : A000001.argType → A000001.retType`); flat ones
put it inside the namespace as `A000012.flat`.

`data` holds every term OEIS knows, indexed from `offset`, so `a(n) = data[n - offset]`.

Aggregators are rebuilt from the filesystem on every run: `LOEIS/<bucket>/{Defs,Data}.lean`
import each sequence, and `LOEIS/{Defs,Data}.lean` import each bucket.

### Files

| Path | Purpose |
| --- | --- |
| [Scripts/OeisIngest.lean](Scripts/OeisIngest.lean) | `main`, CLI args, directory walk, transaction batching |
| [Scripts/OeisIngest/Parse.lean](Scripts/OeisIngest/Parse.lean) | `.seq` record parser, `Entry` struct, `formulaHash` |
| [Scripts/OeisIngest/Db.lean](Scripts/OeisIngest/Db.lean) | schema DDL, prepared upsert statements |
| [Scripts/OeisIngest/Json.lean](Scripts/OeisIngest/Json.lean) | minimal JSON array/string emitter, hex encoder |
| [Scripts/OeisGen.lean](Scripts/OeisGen.lean) | `main`, CLI args, DB query, file writing, aggregators |
| [Scripts/OeisGen/Render.lean](Scripts/OeisGen/Render.lean) | `Defs.lean` / `Data.lean` text templates, `ArgKind`, `Names` |
| [Scripts/OeisCache.lean](Scripts/OeisCache.lean) | `prune` / `stat` / `put` / `get` for `.lake/build` artifacts |
| [Scripts/OeisTemplate.lean](Scripts/OeisTemplate.lean) | `oeis-template` runner: selection, transaction, reporting |
| [Scripts/OeisTemplate/](Scripts/OeisTemplate/) | `Source` (`SeqSource` loaded from the DB), `Base` (`Candidate`, `Template`, `locate`, `publish` = the only writer), `Recognize` (cursor toolkit, `codeEnd`, `hits`, `checkPrefix`), `Tests` (`#guard`), `IntegrationTest` (`oeis-template-test`) |
| [Scripts/Templates/](Scripts/Templates/) | `Registry` + one module per template: `Coxeter`, `PrimeCongruent`, `SqrtContinuedFraction` (+ `…Test`), `WalkN3` |
| [OEISLib/Common/](OEISLib/Common/) | shared math of the families (`OEISLib.Common.Coxeter`, `Residue`, `SqrtContinuedFraction`, `Walk3`); `OEISLib` lean_lib |
| [Impl/Templates.md](Impl/Templates.md) | template contract, runner, the four templates, authoring guide, differences from Spec.md |
| [GenExpr/](GenExpr/) | standalone expression parser (see [Spec.md](Spec.md) §GenExprParser) |
| [GenExprTests/](GenExprTests/) | `#guard` suites + `lake exe genexpr-test` runner |
| [lakefile.toml](lakefile.toml) | `Scripts` + `OEISLib` lean_libs, `oeis-ingest` / `oeis-gen` / `oeis-cache` / `oeis-template` / `oeis-template-test` lean_exe, `LOEIS.+`, `Check.+`, `GenExpr.+`, `GenExprTests.+`, `OEISLib.Common.+` globs |
| [FORMALIZE.md](FORMALIZE.md) | design doc for the LLM formalization pipeline |
| [Skills/maple/SKILL.md](Skills/maple/SKILL.md) | Maple→Lean instructions + filterable function table |
| [Check/Basic.lean](Check/Basic.lean) | `Oeis.Check.report`, throws on term mismatch so `lake build` fails |
| [Scripts/formalize/](Scripts/formalize/) | the Python pipeline (`config`, `db`, `models`, `prompt`, `render`, `lean`, `agent`, `pipeline`, `spans`, `view`, `selftest`, `__main__`) |
| [Impl/Database.md](Impl/Database.md) | current DB tables, row counts, and differences from Spec.md |
| [Impl/README.md](Impl/README.md) | index of the `Impl/` documents and their conventions (RULE 0) |
| [PROGRESS.md](PROGRESS.md) | dated progress log (RULE 1) |

### Parsed OEIS record tags

`%S`/`%T`/`%U` terms · `%N` title · `%O` offset · `%K` keywords · `%F` formulas · `%C` comments ·
`%p` Maple / `%t` Mathematica / `%o` other-language programs (→ `program` table).
Everything else (`%D`, `%H`, `%e`, `%Y`, `%A`, `%E`, `%I`) is ignored for now.

## Database schema

`Metadata/oeis.db`. Columns that later stages fill in are created empty / `STATUS_UNKNOWN`;
re-running the ingest refreshes only OEIS-derived columns and preserves them.
Full table inventory (2026-10-29 counts) and the gap to Spec.md: [Impl/Database.md](Impl/Database.md).

### `sequence`

| Column | Notes |
| --- | --- |
| `name` | `Axxxxxx`, PRIMARY KEY |
| `title` | `%N` |
| `"offset"` | first component of `%O` (must be quoted — SQL keyword) |
| `offset_first_big` | second component of `%O` |
| `keywords` | JSON array of strings |
| `data` | JSON array of bare integer numerals (arbitrary precision) |
| `data_count` | number of terms |
| `main_definition_hash` | *unused* — NULL |
| `formalized_formula_hashes` | *unused* — `[]` |
| `unformalized_formula_hashes` | JSON array of `%F` hashes |
| `formula_lines` | JSON array of the verbatim `%F` lines (was `all_unformalized_formulas_text`); `formula` section text = lines joined with `\n` |
| `comment_lines` | JSON array of the verbatim `%C` lines |
| `main_item_id` | id of the `formalization_item` that is the current main definition (set by templates) |
| `status` | `STATUS_UNKNOWN` |
| `source_file`, `updated_at` | provenance |

### `formula`

PRIMARY KEY `(oeis_name, hash)`; indexes on `hash` and `status`.

| Column | Notes |
| --- | --- |
| `hash` | 16 hex chars of `String.hash` of the formula text |
| `oeis_name`, `human_written_formula` | from `%F` |
| `formalized_formula`, `type` | *filled later* — `''` |
| `status` | `STATUS_UNKNOWN` → `STATUS_PROVED` / `STATUS_VERIFIED` / `STATUS_SORRY` |
| `verification_values`, `disproved_values`, `additional_conditions` | *filled later* — `[]` |
| `source_tag`, `line_index` | `'F'` and position within the sequence |

### `program`

PRIMARY KEY `(oeis_name, language, block_index)`; indexes on `language`, `hash`,
`(language, status)`.

| Column | Notes |
| --- | --- |
| `language` | `maple` (`%p`), `mathematica` (`%t`), or the lowercased `(Lang)` marker of `%o` |
| `source_tag` | `p` / `t` / `o` |
| `text` | block verbatim; `%p`/`%t` split at `# Alternative`, `%o` split at each `(Lang)` |
| `hash` | `String.hash`, 16 hex chars — used as `formalization_item.source_hash` |
| `line_count`, `status` | |

### `formalization_batch` / `formalization_item` / `program_gap` / `skill_suggestion`

`formalization_item` is the unified table of formalizations, written by the Python LLM pipeline
(`producer = 'llm'`) and by templates (`producer = 'template:<name>'`). One row = one stretch of
original text (`language` = `maindef` / `formula` / `comment` / program language, `block_index`,
`span_start`/`span_end` in characters, `original_text`) plus name-free Lean content
(`lean_kind`, `lean_type`, `lean_code`, `imports`, `aux_code`, `eq_statement`, `eq_proof`;
`«self»` / `«main»` placeholders) and verification (`status`, `verified_upto`, `verified_ranges`).
Unique on `(oeis_name, language, formula_hash, producer, lean_kind)`. Column list and gap to the
Spec: [Impl/Database.md](Impl/Database.md). `Db.migrate` (Lean) and `_migrate` (Python) upgrade an
older DB in place.

The LLM-side tables are created by the Lean ingest's `schemaSql`.
Full column list in [FORMALIZE.md](FORMALIZE.md#10-database). Key points:
`formalization_batch.chat_history` stores serialized pydantic-ai messages (that is what makes
`retry --batch-id` continue the same conversation), `skill_text` stores the filtered skill the
model actually saw, and `formalization_item.failure_points` stores the disagreeing indices as
`[{"n":…,"expected":…,"got":…}]`. `formalization_item.span_start`/`span_end` locate the item
inside its block; `program_gap` holds the **complement** — every stretch of a program block no
item claimed, as `STATUS_UNFORMALIZED` (a real missed program) or `STATUS_GAP_TRIVIAL`
(whitespace / stray delimiters / an author-credit comment). Gap rows are rewritten wholesale
per block on every run, so they never go stale.

## Commands

```bash
lake build oeis-ingest
lake exe oeis-ingest [--seq-dir oeisdata/seq] [--db Metadata/oeis.db] [--limit N]

lake build oeis-gen
lake exe oeis-gen [--db Metadata/oeis.db] [--out LOEIS] [--all] [--bucket A000]... [--seq A000001]... [--force]

lake build oeis-cache
lake exe oeis-cache <prune|stat|put|get> [--archive PATH] [--manifest PATH] [--build-dir PATH] [--level N] [--force]

lake build oeis-template oeis-template-test
.lake/build/bin/oeis-template <walkN3|coxeter|primeCongruent|sqrtContinuedFraction>
    (--all | --bucket A147 | --seq A147999) [--force] [--dry-run] [--limit N] [--db PATH] [--check-cap=K]
lake exe oeis-template-test      # DB integration test; `lake build Scripts` runs the #guard suites
# `lake exe` replays library warnings on every call; the binary under .lake/build/bin is quieter.

# GenExprParser: the `#guard` suites fail the build, the exe covers the acceptance corpus.
lake build GenExprTests
lake exe genexpr-test [--engine internal|lean|internalThenLean|crossCheck] [--elab-noncomputable]
                      [--timeout MS] [--filter SUBSTRING] [--list]
lake exe genexpr-test --check-imports   # every declared import list, one child process per set

uv venv && uv pip install -e .
PYTHONPATH=Scripts .venv/bin/python -m formalize run   [--batch-size N] [--batches N] [--retry N] [--bucket A000] [--seq A000045] [--dry-run] [--learn] [--include-attempted] [--keep-check-files]
PYTHONPATH=Scripts .venv/bin/python -m formalize retry --batch-id K [--retry N]
PYTHONPATH=Scripts .venv/bin/python -m formalize show  --batch-id K [--history] [--limit N] [--color auto|always|never]
PYTHONPATH=Scripts .venv/bin/python -m formalize show  --seq A000002 [--color auto|always|never]
PYTHONPATH=Scripts .venv/bin/python -m formalize stats
PYTHONPATH=Scripts .venv/bin/python -m formalize.selftest    # no model call
```

`--limit N` truncates to the first N `.seq` files — use it for fast iteration.
Full ingest run: ~2m25s, 398,471 sequences, 539,052 formula rows, 544,711 program rows (counts as of 2026-10-29).

`oeis-gen` never overwrites an existing file unless `--force` is passed, so later stages that
replace `sorry` with real definitions are safe from regeneration.

No `sqlite3` CLI on this machine; inspect the DB with `python3 -c "import sqlite3; ..."`.

## Decisions

- **Scope**: ingest all ~396k sequences, no keyword filtering.
- **DB path**: `Metadata/oeis.db`.
- **Hashing**: `String.hash` (fast), rendered as 16 lowercase hex chars. SHA-256 rejected as
  too slow.
- **Lists**: always stored as JSON serialized to a `TEXT` column.
- **Re-run semantics**: upsert. OEIS-derived columns refreshed, formalization columns
  untouched. Verified by test.
- **`%C` (comments) are never ingested** — not stored, not treated as formula candidates.
- **Multi-line `%F` blocks stay split one-row-per-line for now.** Lines that carry no formula
  (e.g. `"From _Mitch Harris_, ... (Start)"`, `"(End)"`) are expected to just fail to parse
  later and be skipped — no special-casing needed at ingest time.
- **Subtype bounds use `offset ≤ n`**, consistent with `PNat` for offset 1 and `Nat` for offset 0.
- **Generated files import `Mathlib.Tactic` + `Mathlib.Data.PNat.Defs`.**
- **Linter options live in `lakefile.toml`, never in generated files** —
  `weak.linter.unusedVariables = false` and `weak.linter.style.longLine = false`, because the
  skeletons have unused binders (proofs are `sorry`) and very long term lists by construction.
- **Hosting moves to Hugging Face**: `https://huggingface.co/datasets/formalica/lean4oeis`.
  GitHub is dropped (CI in `workflows/` is lost). All 792k `LOEIS/**.lean` files are committed
  raw, despite HF recommending <100k files per repo.
- **`oeisdata` is NOT a submodule** — it stays git-ignored and users clone it themselves,
  shallow + sparse (`seq/` only), from `https://github.com/oeis/oeisdata`.
- **`Metadata/oeis.db` is committed via Git LFS** (`.gitattributes`), no longer git-ignored.
  HF upgrades LFS to Xet storage server-side.
- **`*.setup.json` is pruned, never cached.** Lake writes one per module (~1.8 MB with
  `import Mathlib.Tactic`) = 174 GB of the 187 GB build dir. `Module.checkArtifactsExist`
  checks `.olean`/`.ilean`/`.c` but *not* `setup.json`, so deleting them is safe.
  `.c` files (2.5 GB) **must** be kept or Lake rebuilds the module.
- **`defaultFacets = ["leanArts"]` is a dead end** — it is already the Lake default, and `.c`
  output is produced unconditionally as part of every module's artifacts.
- **LLM framework is pydantic-ai**, with `output_type=BatchResult` structured output.
- **The agent gets no tools.** Lean is compiled by the pipeline on every attempt regardless, so
  a "compile" tool would only burn tokens on a decision that is already made.
- **Programs are delimited by anchors, not copied.** The model returns `start_marker` /
  `end_marker` (verbatim, ≥6 chars, `end_marker` extended through the trailing author credit)
  and `spans.resolve` backtracks to a non-overlapping assignment. Asking for the whole
  `original_text` verbatim was unreliable — the model tidies whitespace and drops comments.
  `original_text` is now the *resolved* `block[start:end]`.
- **Everything unclaimed is recorded, never silently dropped.** `spans.gaps` computes the
  complement of the accepted spans; non-trivial gaps become `STATUS_UNFORMALIZED` rows and are
  fed back as a defect, so a batch with an open gap cannot reach `BATCH_OK`. `BatchResult.skipped`
  lets the model explain a gap instead of translating it.
- **`%p` / `%t` blocks are never split by the ingest** — splitting on `# Alternative` is
  unreliable, so one block can hold several programs and the LLM step splits them.
- **The `formula_eq` theorem is appended by the pipeline, never requested from the model**, and
  is `sorry` — this stage only formalizes.
- **Dependencies are validated through data-backed shims** in `Check/B<id>/`, because every
  `LOEIS` main definition is still `sorry`. Asking a shim out of range is `STATUS_DEP_RANGE`,
  a distinct outcome from a wrong translation.
- **`computable = false` items are stored but never compiled** — generating functions / real
  analysis wait for a later validation stage.
- **`tabl` / `tabf` (multi-parameter) sequences are excluded** from formalization for now.
- **Skill suggestions are stored, never auto-applied** (`skill_suggestion.applied = 0`).
- **Copying another branch's work** (e.g. `origin/template2`) goes into the working tree as
  untracked files only. The parser commit `6fc1f0a24cf` is never copied. Tracked files that
  the other branch changes are not overwritten without explicit user approval.

- **Templates only talk to the DB through `Oeis.Template.publish`.** A template is a pure function
  `SeqSource → Verdict` with no DB handle and no `.seq` access. `publish` refuses a candidate unless
  its `originalText` is a substring of the stored section (`maindef` = title, `formula`/`comment` =
  lines joined with `\n`, else a `program` block), then derives span, `formula_hash` and
  `source_hash`. Templates write no Lean files (Spec: `oeis-gen` renders items).
- **Template re-runs replace**: a producer's items for a sequence not re-submitted are deleted;
  other producers' items are never touched. Without `--force` a sequence that already has items
  from the template is skipped.
- **Lean content of items is name-free** (`«self»`, `«main»`, family parameters inlined) and carries its own
  `formula_eq` statement and proof (`eq_statement`, `eq_proof`) because the Spec's `data_eq` field does
  not cover them. The same text may have a `prop` and a `computable` item (`lean_kind` is in the key).
- **Shared template math lives in `OEISLib/Common/`** (namespace `OEISLib.Common.<Name>`). The Spec's
  later `LOEIS` → `OEISLib` rename is not done.
- **Recognized snippets exclude credits and comments**: `Recognize.codeEnd` cuts a trailing
  `- _Name_, date` and `(* … *)`; the language marker `(PARI)` etc. is not in the stored program text.
- **`%F` and `%C` are stored verbatim in `sequence`** (`formula_lines`, `comment_lines`); the old
  `formula` table is no longer written.
- **`verified_definitions` offers the LLM only `producer = 'llm'` rows** until lean_code conventions are unified.
- **Differences from Spec.md tables are sorted by importance, most important row first** (RULE 0).
- **Progress is kept in PROGRESS.md. Open items and next steps are written in AGENTS.md. The existing open items list stays here until it is moved.**

### GenExprParser decisions

- **`GenExpr/` is standalone**: it imports nothing from LOEIS/Scripts, and nothing from Mathlib
  either — Mathlib will be loaded into a scratch environment at runtime by `GenExpr.Verify`.
  That keeps ~90% of the tests running in milliseconds.
- **Segmentation is a max-weight non-overlapping cover DP over every start position**, never
  greedy leftmost-longest. `words (1+2*x^4)/(...)` parses fine as a call; it loses because the
  call head is an unfillable hole, not because of any prose handling.
- **Ambiguity is a costed list of parses, not an AST node.** The parser returns one result per
  end position, which is also what the cover DP consumes.
- **Operand positions use maximal munch** (`parseOperand`). Feeding short checkpoints back into
  operator construction makes `3n^2 - 7*n` also parse as `(3n^2 - 7)*n`.
- **A relation is never an operand**, so `a(n) = 0^n + n` has exactly one reading.
- **Precedences mirror Lean's** so a rendered term re-parses to the same tree: rel 50, `+ -` 65,
  `* / mod` 70, juxtaposition 72, unary `-` 75, `^` 75 (right, rbp 72 so `2^2n` reaches
  `2^(2n)`), postfix `!` 90.
- **Implicit multiplication requires glued tokens**, and `ident ident` is never a product — that
  is what keeps `2 for` and `Dec 29 2012` out.
- **A name used as a call head anywhere (`prescan.applied`) is a function hole wherever it is
  unresolved**, including bare. This is what rejects `1 + T(x)` instead of reading it as `1 + T*x`.
- **Fragments with no operator at all are dropped** (`Ast.hasStructure`): `a(n)` states nothing.
- **A goal is never invented from scraps.** If the text plainly defines the requested name and we
  fail to read that line, `plan` returns nothing rather than renaming a leftover sub-expression.
- **Arithmetic alternatives are *transparent*** — usable only at their exact result type, never
  cast. Everything else is *opaque* — usable at or below the context type, with the cast on its
  result. Casts therefore only ever land on leaves and opaque results, which is what keeps
  `(n-2) * 2^(2n-1)` at ℚ from becoming `↑(n - 2 : ℕ) * …`.
- **Inference is a k-best table per result type, built bottom-up.** The table *is* the feasibility
  analysis: "can this be ℚ?" is one array lookup, and there is no separate `feas` pass.
- **Narrowed readings are always offered, not only as a fallback.** A formula can typecheck at the
  requested type and still be wrong there (A084847), so `⌊…⌋₊` variants are ranked after the direct
  ones rather than suppressed.
- **ℕ chains are re-emitted additions-first and multiplications-first**, and only the *left spine*
  is flattened — `a + (b - c)` is genuinely not `a + b - c` over ℕ.
- **Bodies are stored name-free** with a `«self»` placeholder, so the same body can be re-rendered
  under any name (Spec: `formalization_item` stores code "without any name").
- **Normalization happens where the typing is produced, not where it is printed**, so the
  interpreter and the renderer always see the same term.
- **The interpreter is built on Lean's own `Nat`/`Int`/`Rat` operations**, so truncated
  subtraction, floor division and Euclidean `Int` division agree with the emitted code by
  construction. (`/` on `Int` in this toolchain is `ediv`: `(-7)/2 = -4`.)
- **A recursive body cannot produce its own base cases**, so *any* outcome at a patchable prefix
  position — mismatch, divergence, or an out-of-domain value — is repaired the same way. Only a
  prefix is ever forgiven; a failure in the middle rejects the reading.
- **The step budget lives in the interpreter, not in Lean.** A compiled Lean term cannot be
  interrupted once running, which is why `internal` is the default engine.
- **A call to a data-only function outside its table is `unknown`, not a failure** — the point
  proves nothing rather than counting against the formula.
- **One verification policy, two evaluators.** `runPolicy` (prefix patching, guards, success
  rate) is generic over a point evaluator; the interpreter and `GenExpr.LeanEngine` only differ in
  how one point is computed, so they cannot drift on what counts as verified.
- **The Lean engine checks the declaration exactly as emitted** (`renderDef` output, base-case
  arms included), elaborated with `Lean.Elab.process` in memory and run through a
  `probe : Array Int → String` via `evalConst`. Data-only functions become stubs, elaborated twice
  with different junk values in one snippet; differing results mean `unknown`.
- **Base cases are keyed by their argument**, not by position — data starting at 1 used to be
  rendered as an arm for 0, which the interpreter could not notice and Lean did.
- **One shared environment, imported once.** `importModules` costs seconds for a targeted set,
  7.5 min / 3.9 GB for all of Mathlib, and an environment is never freed. Default base set is
  `Builtins.computableImports` (≈12 s cold, 2 GB); `--elab-noncomputable` switches to
  `Builtins.allImports` (≈26 s, 2.8–4.1 GB). Several separate analysis environments OOM'd a 15 GB box.
- **Import *sufficiency* is checked in child processes** (`LeanEngine.elabIsolated`,
  `--check-imports`): one fresh environment per import set, memory released on exit.
- **Non-computable readings are returned flagged** (`computable := false`, `report.accepted :=
  false`), never silently dropped — but only when *no* computable reading exists, so a computable
  formula that fails its data is not replaced by an unrunnable one.
- **`internalThenLean` only evaluates in Lean the points the interpreter already settled**, so a
  slow Lean evaluation can time out but never runs on a point that was never going to finish.
- **Recursion ladder** (`RecForm`): *structural* pattern arms → *well-founded* `if n < B then …
  else …` + `termination_by` / `decreasing_by all_goals omega` → *fuel* (`where go`). Lean already
  proves non-structural calls such as `a((n+1)/2)` in the pattern form, so well-founded is only
  needed for `ℤ` arguments, and fuel only for nested recursion (`a(n-a(n-1))`), which Lean rejects
  otherwise. The pure path predicts the rung from the term's shape (`recFormOf`); the Lean engine
  climbs the ladder until one elaborates and reports it in `VerifyReport.recForm`.
- **Junk is rendered twice for recursive definitions too**, not just for tables: a value that
  leaned on a junk arm or exhausted fuel would otherwise pass. Such a point is `undetermined` —
  patchable at a prefix position, otherwise merely unknown.
- **Statements** (`ret := .prop`): a relation fragment becomes `∀ vars, guards → conjuncts`,
  decided at each data index (expected value 1) by the interpreter and by a `decide` probe over a
  reducible `abbrev` in Lean. An equality chain repeats its smallest member, or uses
  `List.Pairwise` when every member has ≥ 5 nodes; every applied name must be known, so
  `a(n) = n^2 = n*n` is a statement only once `a` is supplied. Each statement in a line is its
  own item, emitted as `theorem statement : … := by sorry` with the body stored name-free.
- **A name used as a plain operand anywhere is a variable**, even where it is followed by `(`:
  `2 | n(n+1)` is a product because `n+1` shows `n` is a value (`Prescan.bare`).

## Lean 4.34 gotchas (this toolchain)

- `String.drop`/`take`/`takeWhile`/`dropWhile` return `String.Slice`, not `String`.
  Convert with `.toString`.
- `String.trim`/`trimLeft`/`trimRight` are deprecated; use `trimAscii` / `trimAsciiStart` /
  `trimAsciiEnd` (they return `Slice`).
- `String.mk` is deprecated; use `String.ofList`.
- `String.Pos` is now dependent (`s.Pos`), so `⟨0⟩` literals and `posOf` are awkward — prefer
  `splitOn` / list-based parsing. `GenExpr.Input` sidesteps this with a char array plus a byte
  offset table.
- `#guard` evaluates `partial def`s (it goes through the compiler, not the kernel), so nested
  inductive recursion in test helpers is fine.
- A Lake glob `Foo.+` does **not** include the module `Foo` itself; write
  `globs = ["Foo", "Foo.+"]`.
- A module docstring must come *after* the `import` lines.
- `have` is a keyword and cannot be used as a structure or constructor field name; so is `rec`.
- `Array.get?` and `List.enum` are gone; use `arr[i]?` and an explicit counter.
- A `let x := match …` inside a function needs an explicit type annotation, or dotted constructor
  notation in the branches fails to resolve.
- **A parameterless `def` is a closed term and is evaluated at module initialization**, before
  `main` runs. `def run : Array Result := corpus.map runCase` therefore executed the whole test
  corpus at process start and blew the stack; give such definitions a `Unit` parameter or drop
  them. The interpreter (`#guard`, `lean --run`) does not show this, only the compiled binary.
- `String.dropRight` is deprecated in favour of `String.dropEnd`, which returns a `Slice`.
- **Runtime elaboration needs**: `supportInterpreter = true` on the `lean_exe`;
  `enableInitializersExecution` before *every* `importModules (loadExts := true)` (each import
  resets the flag); `evalConst … (checkMeta := false)`; `LEAN_PATH` from `lake exe` / `lake env`.
- **An abandoned task keeps the process alive** after `main` returns. Anything that may time out
  a Lean evaluation must end with `IO.Process.exit`.
- `Options.setNat` is gone; use `maxHeartbeats.set opts n`. `List.allSome` does not exist; use
  `Array.mapM id` in `Option`. `matches` is a keyword.
- Mathlib module moves seen while fixing the catalogue: big operators are
  `Mathlib.Algebra.BigOperators.Group.Finset.Defs`, `Real.logb` is `…SpecialFunctions.Log.Base`,
  `Real.sqrt` is `Mathlib.Analysis.Real.Sqrt`, the `|x|` notation is
  `Mathlib.Algebra.Order.Group.Unbundled.Abs`; `Nat.sqrt` is core.
- `leansqlite` is built with `experimental.module`; `SQLite.open` must be written
  `SQLite.«open»`.
- A `lean_exe` root outside any `lean_lib` glob will not get its imports built. The `Scripts`
  `lean_lib` in `lakefile.toml` exists for exactly this reason.
- The Lean language server can report stale `unknown module prefix` errors after `lakefile.toml`
  changes; restart the Lean server, `lake build` is the source of truth.
- `noncomputable` and `theorem` are keywords and cannot be constructor names (`LeanKind.nonComputable`,
  `.thm`); a doc comment (`/-- -/`) cannot precede `namespace`.
- A library that imports Mathlib (`OEISLib.Common.*`) makes the importing exe link all of Mathlib's C
  output (`lake build oeis-template` the first time compiles ~6000 `:c.o` jobs); `#guard` files that import
  it need `set_option linter.hashCommand false`.
- `lake build` with no target also builds the 792k `LOEIS` modules. For this tree use
  `lake build Scripts OEISLib oeis-template oeis-template-test oeis-ingest oeis-gen`.

## Open items / next steps

1. **Validate the prune+cache round trip on the `cache_test` branch.** Build `LOEIS.A000`,
   `oeis-cache prune`, confirm `lake build LOEIS.A000` is still a no-op, then `put`, upload,
   and `get` on another box.
2. **Run the formalization pipeline at scale.** `uv pip install anthropic` is required for the
   default `anthropic:claude-sonnet-4-5` model; the live path has not been exercised yet, only
   `formalize.selftest` (offline) and `--dry-run`. First live target: re-run A000002 with
   `--include-attempted` and confirm the model now returns **both** Maple programs, and that
   `show --seq A000002` reports 100% coverage.
3. **Re-run the sequences already attempted before the marker change.** Their `program_gap` rows
   were backfilled from `original_text`, but the model was never asked to close them.
3. Multi-line `%F` blocks (`... (Start)` / `... (End)`) are currently split into one row per
   line. Group them before treating each line as a standalone formula.
4. Formula AST + parser (`generate_lseq`), type inference, interpretation search
   (`Nat` → `Int` → `Real`, main def → `fn` → `fz`), validated against `sequence.data`.
5. Fill the `sorry`s in `Defs.lean` from the parsed `%N` title, then `Equiv_<hash>.lean` /
   `Basic_<hash>.lean` from the `%F` formulas.
6. `tabl`/`tabf` sequences currently get the flattened one-argument API only; the real
   two-argument version is deferred, and they are skipped by the formalization pipeline.
7. Add `Skills/mathematica/SKILL.md`, `Skills/pari/SKILL.md`, ... — `language` is already a
   column and a flag everywhere, nothing structural is missing.
8. Prove the `formula_eq` theorems that the pipeline currently emits as `sorry`.
9. Build cost: `import Mathlib.Tactic` in every generated file makes a full 396k-sequence build
   impractical. Revisit if the A000 bucket build turns out too slow.
10. Consider exporting the DB to Parquet/JSONL — HF's dataset viewer cannot read SQLite.
11. **Finish GenExprParser.** The pipeline is complete and green end to end with all four
    verification engines, the full recursion ladder and `Prop` statements.
    `lake exe genexpr-test --engine crossCheck` runs 35 checks; `--check-imports` confirms all 114
    declared import lists. Remaining:
    * *OEISParser* — the OEIS-specific wrapper that feeds sequences in as custom alternatives and
      writes results to `formalization_item`. Should use `run` with `internalThenLean` and one
      long-lived `LeanEngine.Session` per process.
    * *`oeis-verify`* — can reuse `LeanEngine.Session.check` / `runPolicy` directly.
    * *Multi-argument recursion* (`T(n,k)`) always takes the fuel rung; a lexicographic
      `termination_by` would be cheaper to prove things about.
    * *Later* — LaTeX/Wolfram frontends (`GenExpr.Ast` is the extension point), `PowerSeries` /
      `EReal` (`Ty` has an `other` constructor reserved).
12. `lake build` with no target builds `LOEIS` (792k modules) — it is in `defaultTargets`. Use
    `lake build GenExpr GenExprTests genexpr-test` for parser work.
13. **Template files copied from `origin/template2` are now rewritten** onto the new interface. Still
    untracked and not merged: `README.md`, `lakefile.toml`, `Metadata/oeis.db`, 5,558 LOEIS `Defs.lean`
    and 5,546 `Equiv_*.lean` of that branch were never copied; `oeis-gen` must regenerate equivalents
    from items. `Scripts/OeisParseReport.lean` (imports the absent `FormulaParser`) is outside every
    glob and can be deleted.
14. **Close the Spec.md vs DB gap** (details in [Impl/Database.md](Impl/Database.md)). Decide each
    conflict with the user before changing code:
    * Ingest: Spec says insert-only; current code upserts (see Decisions).
    * `main_definition_hash` (NULL, unused) vs `main_item_id`; `unformalized_formula_hashes`,
      `formalized_formula_hashes` and the `formula` table are redundant and can be dropped.
    * `status`: no stage writes `STATUS_COMPLETE` / `FORMALIZED` / `DEFINED` / `NOT_STARTED`.
    * Python LLM rows still store `lean_code` with names and hash with blake2b.
    * `Spec/Database.md` is empty, so the per-argument offset algorithm is undefined.
    * `oeis-show` is not in [lakefile.toml](lakefile.toml). `python -m formalize show` covers program blocks only.
15. **Fix `program.language` defects.** 517 rows hold values like `+`, `0 to 49`, `1 to 50` from `%o` parsing.
    Find the cause in the `%o` splitter, then re-ingest (program rows upsert safely).
16. **Check `formalization_batch` rows in `BATCH_RUNNING`** (2 rows) for staleness left by interrupted runs.
17. **Render items into files.** `oeis-gen` must read `formalization_item` (`--hash`, per sequence) and emit
    `Defs` / `Equiv_<hash>` / `Basic_<hash>` from `maindef` / template items: `def formula : lean_type :=
    lean_code`, `theorem formula_eq : eq_statement := by eq_proof`, `«self»`→`formula`, `«main»`→`Axxxxxx`.
    Until then the content is validated only by hand-rendering scratch files (all four templates, 180
    random sequences, 0 errors).
18. **Template follow-ups.** coxeter `formula` items are `List Nat`, not the Spec's value form; 859
    coxeter sequences have a g.f. in another shape (degree `r-1`) that no recognizer covers; the old
    primeCongruent `nth_spec` theorem, the isolated `lean` compile check and `pruneTemplateRows` of the
    sqrt template are gone (verification moves to `oeis-verify`); more families from `Scripts/templates.txt`.
19. **`oeis-verify`** (Spec): verify items from the table against data, update `verified_ranges`; this will
    also cover noncomputable items and re-check template rows.
20. **Python selftest not re-run** after the schema change (`formalize.selftest` builds Lean files); `stats`,
    `show --seq`, the Python migration and `upsert_item` were exercised on scratch copies.
21. **Sort the existing Differences from Spec.md tables** in [Impl/Database.md](Impl/Database.md) and
    [Impl/Templates.md](Impl/Templates.md) by importance, as RULE 0 now requires.

## RULE reminder

Repeating [RULE 0](#rule-0--keep-impl-up-to-date-mandatory) and
[RULE 1](#rule-1--keep-this-file-up-to-date-mandatory) as promised:

> **After every change, update the matching `Impl/*.md`** (its *Differences from Spec.md* section holds
> only Spec.md statements the code contradicts, most important first), **and after every user prompt you act on, update this
> file** — append to [PROGRESS.md](PROGRESS.md), refresh the current state / schema / commands sections, add new open items and re-prioritize the open items here. Do all of this before you end your turn, every time, without being asked.
