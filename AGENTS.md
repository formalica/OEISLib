# AGENTS.md

Instructions and living project log for AI agents working in this repository.
(VS Code / Copilot automatically loads `AGENTS.md`, so this is the file to keep current.)

## RULE 0 — Keep this file up to date (MANDATORY)

**After every user prompt you act on, you MUST update this file before finishing your turn.**

- Append what you did to [Progress log](#progress-log) with the date.
- Update [Current state](#current-state), [Database schema](#database-schema), and
  [Commands](#commands) whenever they change.
- Update [Open items / next steps](#open-items--next-steps): remove what is done, add what
  the new work revealed.
- Record decisions the user made (naming, formats, tool choices) under [Decisions](#decisions)
  so they are not re-litigated.
- Keep it short. This is a working index, not documentation. Delete stale lines instead of
  letting the file grow.

This rule is repeated at the [bottom of the file](#rule-0-reminder) on purpose. Do not skip it.

## Project

Formalize OEIS sequences in Lean 4 + Mathlib. The end goal (see [SPEC.md](SPEC.md) and
[OEIS.md](OEIS.md)) is to generate, per sequence `Axxxxxx`, a directory `Axxx/Axxxxxx/` with:

- `Defs.lean` — main definition (`Axxxxxx`, `argType`, `retType`, `offset`, `fn`, `fz`, `prop`,
  coherence theorems)
- `Data.lean` — known terms + `data_eq` / `data_eq_fn` / `data_eq_fz`
- `Equiv_<hash>.lean` — alternative definitions + equivalence to the main definition
- `Basic_<hash>.lean` — properties that do not fully determine the sequence

Raw OEIS data lives in `oeisdata/seq/A<bucket>/A<number>.seq` (396,006 files, git-ignored,
official OEIS "internal format").

## Current state

Step 1 of SPEC.md (metadata tables) is **done**, and the `Defs.lean` / `Data.lean` skeleton
generator is **done**. The **Maple → Lean LLM formalization pipeline is implemented** (see
[FORMALIZE.md](FORMALIZE.md)); `%F` formula parsing / real main definitions are not started.

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
| [GenExpr/](GenExpr/) | standalone expression parser (see [Spec.md](Spec.md) §GenExprParser) |
| [GenExprTests/](GenExprTests/) | `#guard` suites + `lake exe genexpr-test` runner |
| [lakefile.toml](lakefile.toml) | `Scripts` lean_lib + `oeis-ingest` / `oeis-gen` / `oeis-cache` lean_exe, `LOEIS.+`, `Check.+`, `GenExpr.+`, `GenExprTests.+` globs |
| [FORMALIZE.md](FORMALIZE.md) | design doc for the LLM formalization pipeline |
| [Skills/maple/SKILL.md](Skills/maple/SKILL.md) | Maple→Lean instructions + filterable function table |
| [Check/Basic.lean](Check/Basic.lean) | `Oeis.Check.report`, throws on term mismatch so `lake build` fails |
| [Scripts/formalize/](Scripts/formalize/) | the Python pipeline (`config`, `db`, `models`, `prompt`, `render`, `lean`, `agent`, `pipeline`, `spans`, `view`, `selftest`, `__main__`) |

### Parsed OEIS record tags

`%S`/`%T`/`%U` terms · `%N` title · `%O` offset · `%K` keywords · `%F` formulas ·
`%p` Maple / `%t` Mathematica / `%o` other-language programs (→ `program` table).
Everything else (`%C`, `%D`, `%H`, `%e`, `%Y`, `%A`, `%E`, `%I`) is ignored for now.

## Database schema

`Metadata/oeis.db`. Columns that later stages fill in are created empty / `STATUS_UNKNOWN`;
re-running the ingest refreshes only OEIS-derived columns and preserves them.

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
| `main_definition_hash` | *filled later* — NULL |
| `formalized_formula_hashes` | *filled later* — `[]` |
| `unformalized_formula_hashes` | JSON array of `%F` hashes |
| `all_unformalized_formulas_text` | JSON array of raw `%F` lines |
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

Written by the Python pipeline; created by the Lean ingest's `schemaSql`.
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
Full ingest run: ~2m25s, 396,006 sequences, 527,877 formula rows.

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

## Progress log

- **2026-08-18** — Implemented SPEC.md step 1: `oeis-ingest` executable, `.seq` parser, JSON
  helpers, `sequence` + `formula` tables. Full ingest run: 396,006 sequences / 527,877
  formulas. Verified signed terms (`A001057`), 54-digit bignums (`A000178`), and upsert
  idempotency (formalization columns preserved, no duplicate rows). Added `Metadata/*.db` to
  `.gitignore`.
- **2026-08-18** — Created this file and adopted RULE 0 (agent updates `AGENTS.md` after every
  prompt).
- **2026-08-18** — Printed full `sequence`/`formula` rows for `A000001` to inspect real data.
  Confirmed with user: `%C` lines stay excluded (already the case), and standalone `%F`
  continuation lines like `(Start)`/`(End)` are fine to keep as their own formula rows — the
  later formalization parser is expected to just skip them silently.
- **2026-08-19** — Added `oeis-gen`: renders `Defs.lean` + `Data.lean` skeletons (all `sorry`)
  per sequence, plus bucket and root aggregators. Verified all four `argType` shapes and the
  flat/`tabl` variant compile: `A000001` (Nat), `A000027` (PNat + tabl), `A000063` (offset 5
  subtype), `A000297` (offset -1, Int subtype, no `fn`), `A000023`/`A000036` (Int retType).
  Moved the `unusedVariables` / `longLine` linter options out of generated files into
  `lakefile.toml`.
- **2026-08-20** — Rewrote README.md: elan/toolchain setup, `lake exe cache get`, oeisdata
  acquisition pointer, then the three-step ingest → gen → build pipeline with common flags.
- **2026-08-20** — Planned the Hugging Face migration. Measured: `.lake/build` 189 GB (98k of
  792k modules), of which `ir/` is 178 GB; oleans 9.6 GB; `LOEIS/` 4.6 GB / 792,809 files;
  Mathlib is *not* in `.lake/build` (it lives in `.lake/packages/mathlib/.lake/build`, 6.5 GB).
  Confirmed oeisdata upstream is `github.com/oeis/oeisdata` (`seq/` 398,471 entries,
  `files/` 275,775). Un-ignored `oeisdata` and `Metadata/*.db`, added `.gitattributes` LFS rule,
  rewrote README setup section (clone → elan → sparse oeisdata → LFS database).
- **2026-08-20** — Read Lake's `Build/Module.lean`: `.c` is emitted unconditionally and is part
  of `checkArtifactsExist`, but `*.setup.json` is not — and it is 174 GB of the 187 GB build
  dir. Added `oeis-cache` (`prune`/`stat`/`put`/`get`), reverted oeisdata to a manual sparse
  clone, documented disk-usage strategy and cache download in README.
- **2026-08-20** — Added Hugging Face dataset card to README.md: YAML metadata block with
  `dataset_info`, feature descriptions (name, title, offset, data, formulas, keywords), split
  info (396,006 sequences), download/dataset size, license (CC0-1.0), tags, task IDs. Resolves
  HF warning "empty or missing yaml metadata in repo card".
- **2026-08-20** — Fixed README.md YAML validation errors: changed `language` from invalid
  "lean4" to valid "code" (special value for code/programming datasets), changed `license`
  from cc-by-sa-4.0 to cc0-1.0 (proper for OEIS), removed invalid `task_ids`
  "sequence-annotation", added complete `dataset_info` with feature descriptions.
- **2026-08-20** — Simplified README.md dataset card by removing empty `dataset_info` section.
  Kept minimal YAML: language, license, pretty_name, size_categories, source_datasets, tags.
- **2026-08-20** — Updated license in README.md YAML metadata to cc-by-sa-4.0 per user
  specification: Creative Commons Attribution Share-Alike 4.0.
- **2026-08-21** — Built the LLM formalization pipeline for Maple program blocks.
  Lean side: ingest now parses `%p`/`%t`/`%o` into a new `program` table (splitting `%o` at
  `(Lang)` markers and `%p`/`%t` at `# Alternative`), and `schemaSql` gained
  `formalization_batch`, `formalization_item`, `skill_suggestion`; `lakefile.toml` gained the
  `Check.+` glob. Python side: `Scripts/formalize/` (pydantic-ai, no tools) batches N blocks
  from N distinct sequences into one call, sends a skill whose function table is filtered to the
  functions actually present, includes referenced sequences with up to 3 already-verified
  alternative definitions, validates `original_text` as a verbatim non-overlapping span, renders
  `Equiv_<hash>.lean` + a `Check/B<id>/` module that evaluates the translation against OEIS terms
  through data-backed dependency shims, runs one `lake build`, and classifies each item as
  `STATUS_VERIFIED` / `COMPILE_ERROR` / `EVAL_MISMATCH` / `DEP_RANGE` / `NONCOMPUTABLE` /
  `REJECTED`. Chat history is persisted so `retry --batch-id` continues the same conversation.
  Wrote [FORMALIZE.md](FORMALIZE.md), `Skills/maple/SKILL.md` (10 function-table rows), and a
  README section. Verified offline with `formalize.selftest`: 2 PASS, 1 deliberate
  `STATUS_EVAL_MISMATCH` with parsed failure points. Fixed a table-filter bug where rows keyed
  by non-identifiers (`!`, `numtheory[factorset]`) were always kept.
- **2026-08-22** — Debugged A000002: its `%p` block holds **two** Maple programs (the `# Alternative`
  split never happens — `%p`/`%t` are stored whole), the model returned only the Cloitre one, and
  the first program vanished with no trace. Root cause was on the LLM side, invisible because
  nothing tracked what was *not* claimed. Fixes:
  * **Anchor-based spans.** `FormalizedProgram.original_text` → `start_marker` + `end_marker`
    (verbatim, ≥6 chars, `end_marker` extended through the trailing author credit). Rewrote
    `spans.py`: `resolve` enumerates every candidate span per item, orders by fewest candidates
    and backtracks to a non-overlapping assignment, with specific rejection messages (too short,
    only matches after collapsing whitespace, only the first chars match, all candidates overlap).
  * **Gap tracking.** `spans.gaps` computes the complement of the accepted spans; `spans.is_trivial`
    separates real missed programs from comment/whitespace leftovers. New `program_gap` table
    (both in `Db.lean` `schemaSql` and the Python migration) rewritten per block on every run.
    Non-trivial gaps are fed back as repair feedback, so a batch with an open gap can no longer
    reach `BATCH_OK`. Added `BatchResult.skipped` so the model can explain a gap instead.
  * **New `Scripts/formalize/view.py`.** `show --seq A000002` prints every program block of a
    sequence colour-coded — one palette colour per formalized program, red for anything
    unformalized or never processed — with a per-block legend and coverage percentage.
    `show --batch-id K` now prints parsed usage, spans, `lean_code`, dependencies, gaps and,
    with `--history`, the whole stored conversation turn by turn. Added `--color` / `--limit`.
  * Backfilled `span_start`/`span_end` and gaps for the two existing items; `stats` now also
    reports gap counts. Updated `Skills/maple/SKILL.md`, `FORMALIZE.md` (§2 corrected: `%p`/`%t`
    are never split; new §5.1/§5.2 and `program_gap` docs) and README. `selftest` moved to the
    marker contract: still 2 PASS + 1 deliberate `STATUS_EVAL_MISMATCH`, now plus reported gaps.- **2026-09-04** — Started GenExprParser (Spec.md §GenExprParser). Reviewed four independent
  plans (`run1`–`run4`) and merged them; the decisions that survived are recorded under
  [GenExprParser decisions](#genexprparser-decisions). Implemented and tested phase 1:
  `GenExpr/{Types,Lexer,Ast,Analyze}.lean`, `GenExpr/Frontend/Raw/{Prescan,Parser,Segmenter}.lean`,
  plus `GenExprTests/{LexerTests,ParserTests,SegmenterTests}.lean` (~90 `#guard`s) and the
  `genexpr-test` runner skeleton. Two bugs found and fixed while iterating, both worth
  remembering: parse *checkpoints* must not be reused as operands (otherwise `3n^2 - 7*n` also
  reads as `(3n^2 - 7)*n`), and a relation must never be an operand (otherwise `a(n) = 0^n + n`
  also reads as `(a(n) = 0^n) + n`). Every "important corner case" and "multiplication corner
  case" from Spec.md now parses and segments to the expected tree, including extracting only the
  generating function out of `another words (1+2*x^4)/(...). - _John Doe_, Dec 29 2012` and
  rejecting `A(x) = 1 + T(x) - T^2(x)/2 + ...` with `unresolved name 'T'`.
- **2026-09-04** — GenExprParser phases 2–4: `GenExpr/{Plan,Registry,Typed,Infer,Render}.lean`
  plus `GenExprTests/{PlanTests,RenderTests}.lean`. Raw text now produces Lean that elaborates
  and evaluates: checked against Mathlib that `3 * n ^ 2 + 6 - 7 * n`, `((n : ℤ) - 1).natAbs`,
  `∑ k ∈ Finset.range (n + 1), k ^ 2`, `∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2`, `∫ x in (0 : ℝ)..1, x ^ 2`
  and the structural `def A000330 : ℕ → ℕ | 0 => 0 | 1 => 1 | n + 2 => A000330 (n + 1) + (n+2)^2`
  all compile, and that the A084847 reading `⌊2*3^n + ((n:ℚ)-2) * 2^(2*(n:ℤ)-1)⌋₊` reproduces
  `1, 4, 18, 86, 418, 2022`. What cost the most to get right: transparent-vs-opaque alternatives
  (so casts land on leaves only), always offering narrowed readings instead of treating them as a
  fallback, giving applications precedence 1023 so nested calls parenthesise, and `simplifyOffsets`
  so the shifted recursive call reads `A000330 (n + 1)` rather than `A000330 (n + 2 - 1)`.
- **2026-09-04** — GenExprParser phases 5–6: `GenExpr/{Normalize,Eval/Interp,Verify,Api}.lean`,
  `GenExprTests/{VerifyTests,Cases}.lean` and the `genexpr-test` runner. `analyze` now takes raw
  text plus known values and returns checked Lean. Highlights: A084847 is rejected over ℕ and ℤ
  and accepted on the fifth reading as `⌊2*3^n + ((n:ℚ)-2) * 2^(2*(n:ℤ)-1)⌋₊`; `a(n) = a(n-1)+n^2
  for n > 1` becomes `def a : ℕ → ℕ | 0 => 0 | n + 1 => a n + (n + 1) ^ 2` with the base case
  taken from the data because the text said `for n > 1`; Fibonacci needs `allowedFailures = 2`
  and produces two arms. All 23 acceptance cases pass and every generated declaration was
  compiled and evaluated against Mathlib. Two findings worth keeping: normalization had to move
  out of the printer into `Infer` so the interpreter and the renderer share one term, and a
  parameterless `def` is a closed term that Lean evaluates at module initialization — which ran
  the whole test corpus before `main` started and overflowed the stack.
- **2026-10-02** — GenExprParser Lean verification engines: new `GenExpr/LeanEngine.lean`;
  `Verify` refactored so `runPolicy` is shared by both evaluators; `Api` split into a generic
  `analyzeWith` used by pure `analyze` (interpreter) and IO `run` (any engine). `lean`,
  `internalThenLean` and `crossCheck` all pass the 28-check corpus; a deliberately drifting
  catalogue entry (`sqrt` keyed, `Nat.log` rendered) is accepted by the interpreter and rejected
  by every Lean engine at point 1; a 40-term naive Fibonacci times out once in Lean and is still
  accepted. The Lean engine found three real bugs the interpreter could not: two registry
  modules that do not exist in this Mathlib (`BigOperators.Basic`, `SpecialFunctions.Logb`),
  table stubs using `ℤ` without importing it, and base cases rendered by position so data
  starting at 1 produced an arm for 0. `--check-imports` then verified all 107 declared import
  lists in child processes and caught one more (`|x|` on `ℤ` lacked the notation module).
  Measurements that shaped the design: importing all of Mathlib at run time takes 7.5 min /
  3.9 GB, a targeted set 2–14 s; environments are never freed, and importing several analysis
  sets in one process was OOM-killed at 5.8 GB, hence one shared environment per process and
  child processes for import checks.
- **2026-10-03** — GenExprParser: the rest of the recursion ladder and `Prop` statements, both
  absent before. `RecForm` + `recFormOf` in `Render`, with well-founded and fuel renderings in
  `renderDef`; the Lean engine climbs the ladder until a rung elaborates. `planProps` /
  `typeProp` / `inferProp` turn relation fragments into guarded `∀` statements; the interpreter
  decides them, Lean checks them with `decide`. Under all three Lean engines Lean independently
  picked the rung the pure path predicted: structural for `a(floor(n/2)) + n mod 2`, well-founded
  for an `ℤ` argument, fuel for Hofstadter's Q. Spec case 14 now yields its two theorems,
  `∀ n : ℕ, A046080 (a n) = 1` and `∀ n : ℕ, A046109 (a n) = 12`. Found on the way: `2 | n(n+1)`
  read `n` as an unresolved function, contradicting the spec's `n(n+1)/2` rule once the line is not
  a definition; a name used as an operand anywhere is now a variable. Corpus 35/35 under every
  engine, 114/114 import lists sufficient.

## RULE 0 reminder

Repeating [RULE 0](#rule-0--keep-this-file-up-to-date-mandatory) as promised:

> **After every user prompt you act on, update this file** — append to the progress log, refresh
> the current state / schema / commands sections, and re-prioritize the open items. Do this
> before you end your turn, every time, without being asked.
