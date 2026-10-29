# PROGRESS.md

Dated progress log of this project. Moved here from [AGENTS.md](AGENTS.md).

After every user prompt that is acted on, append an entry here (RULE 1 in [AGENTS.md](AGENTS.md)).
Progress is never written in `AGENTS.md`.

## Log

- **2026-08-18** — Implemented SPEC.md step 1: `oeis-ingest` executable, `.seq` parser, JSON
  helpers, `sequence` + `formula` tables. Full ingest run: 396,006 sequences / 527,877
  formulas. Verified signed terms (`A001057`), 54-digit bignums (`A000178`), and upsert
  idempotency (formalization columns preserved, no duplicate rows). Added `Metadata/*.db` to
  `.gitignore`.
- **2026-08-18** — Created this file and adopted the update-`AGENTS.md` rule (now RULE 1) (agent updates `AGENTS.md` after every
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
    marker contract: still 2 PASS + 1 deliberate `STATUS_EVAL_MISMATCH`, now plus reported gaps.
- **2026-09-04** — Started GenExprParser (Spec.md §GenExprParser). Reviewed four independent
  plans (`run1`–`run4`) and merged them; the decisions that survived are recorded under
  [GenExprParser decisions](AGENTS.md#genexprparser-decisions). Implemented and tested phase 1:
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
- **2026-10-29** — Copied template work from `origin/template2` (commits `2a84ad10b86` templates,
  `9ef289f1f12` sqrt) into the working tree as **untracked** files, byte-identical to the tip. The
  parser commit `6fc1f0a24cf` (`FormulaParser/*`) was excluded. 22 non-overlapping files:
  `OEISLib/{Coxeter,Residue,Walk3,SqrtContinuedFraction,SqrtContinuedFractionTest}.lean`,
  `Scripts/{OeisParseReport,OeisTemplate,name_templates.py,templates.txt}`,
  `Scripts/OeisTemplate/Registry.lean`, `Scripts/Templates/*` (8 files), `Scripts/__pycache__/*.pyc`,
  `Metadata/templates.txt` (gitignored), `TEMPLATES.md`, `tmp_sample.lean`. Nothing tracked was
  touched. Not copied yet, pending the user's decision: `README.md`, `lakefile.toml`, `AGENTS.md`
  (template2 version carries the parser lineage), `Metadata/oeis.db` (an LFS pointer that would
  replace the local DB), 5,558 modified `LOEIS/**/Defs.lean`, and 5,546 new `LOEIS/**/Equiv_*.lean`.
  `Scripts/OeisParseReport.lean` imports `FormulaParser.Parser`, so it will not compile until the
  parser is copied. It is outside every lean_lib glob, so `lake build` is unaffected.
- **2026-10-29** — Documented the current database in the `# Database` section of [Impl/README.md](Impl/README.md) (moved later, see below): the seven
  tables with live row counts and key columns, and a comparison against the `# Database` section of Spec.md.
  Corrected the stale counts above (396,006 / 527,877 became 398,471 / 539,052; program rows 544,711). Recorded
  the Spec.md conflicts (insert-only ingest vs upsert, `main_definition_hash` kept and dropped, empty
  `Spec/Database.md`), the 517 bad `program.language` values, and 2 `BATCH_RUNNING` batches as open items 14-16.
  No code or data changed.
- **2026-10-29** — Moved the `# Database` section from [Impl/README.md](Impl/README.md) to
  [Impl/Database.md](Impl/Database.md), at the user's request. Impl/README.md keeps only its original
  purpose line. Updated the links in Current state, open item 14 and the progress log, and added the
  Files table row. No content changed.
- **2026-10-29** — **Stage 1 of the new Spec: `oeis-template` writes `formalization_item`.** Plan:
  DB first, then a base interface, then port every template.
  * *DB.* `oeis-ingest` now also stores `%C` (`sequence.comment_lines`) and keeps `%F` verbatim in
    `formula_lines` (renamed from `all_unformalized_formulas_text`); `sequence.main_item_id` added.
    `formalization_item` rebuilt (producer, language incl. `maindef`/`formula`/`comment`, `block_index`,
    `lean_kind`, `lean_type`, name-free `lean_code`, `imports`, `aux_code`, `eq_statement`, `eq_proof`,
    `verified_ranges`, `batch_id` nullable, unique key with `producer` and `lean_kind`). Migration in
    `Db.migrate` (Lean) and `_migrate` (Python), tested on a legacy DB; the live DB was migrated by
    re-running `oeis-ingest` (backup in `/tmp/oeis.db.bak`, not kept in the repo). Python pipeline adapted
    (`lean_kind`, `producer`, `block_index`, upsert key).
  * *Base.* `Scripts/OeisTemplate/{Source,Base,Recognize}`: a template is a pure function over a `SeqSource`
    loaded from the DB; `publish` is the only writer and rejects candidates whose original text is not in
    the stored section. New runner replaces the `.seq`-reading one; `markFormalized` and the `formula`
    table writes are gone.
  * *Templates.* coxeter, primeCongruent, sqrtContinuedFraction, walkN3 ported (shared cursor code and the
    four verify loops folded into `Recognize`; old files kept in `/tmp/oeis-old-templates`). Full runs:
    2302 / 979 (36 skipped) / 967 (8 skipped) / 3254 sequences, 0 failures, 20,667 items, ~5 s each. The
    port fixed two latent problems: the Wolfram `Select[Prime[Range[K]], …]` literal had one `]` too few
    (the flavor never matched), and snippets used to include author credits and were joined with a space
    instead of the stored `\n`. 180 random sequences rendered by hand into scratch Lean files compile.
  * *Housekeeping.* `OEISLib/*.lean` moved to `OEISLib/Common/` (namespace `OEISLib.Common.*`), `OEISLib`
    lean_lib, `oeis-template` and `oeis-template-test` exes and the template modules added to
    [lakefile.toml](lakefile.toml). Rewrote the templates guide (now [Impl/Templates.md](Impl/Templates.md)) and updated
    [Impl/Database.md](Impl/Database.md). Tests: `#guard` suites (`Scripts/OeisTemplate/Tests.lean`,
    `Scripts/Templates/SqrtContinuedFractionTest.lean`) and `oeis-template-test`.
- **2026-10-29** — Documentation conventions. Added RULE 0 (keep `Impl/` current; the *Differences from
  Spec.md* sections list only Spec.md statements the implementation contradicts, never details the Spec
  does not cover). Moved `TEMPLATES.md` to [Impl/Templates.md](Impl/Templates.md) and rewrote it as an
  implementation description (templates, runner, interface, tests, limitations) with a Spec differences
  section; rewrote [Impl/Database.md](Impl/Database.md) so its differences section only holds Spec
  contradictions (unmatched Spec items such as a missing `oeis-show`, the file hash, per-argument offsets
  and insert-only ingest stay as rows). `Spec.md` still says "Authoring guide: `TEMPLATES.md`" (user-owned,
  not edited). No code changed.
- **2026-10-29** — Created empty `Impl/` documents for the single-`#` sections of [Spec.md](Spec.md):
  `LEAN4OEIS`, `Build-and-cache`, `Formalization`, `GenExprParser`, `OEISParser`, `Generator`,
  `LLM-agent-autoformalization-pipeline`, `OEISLib`, `Verification`. The file name is the heading
  text before any ` — `. `Database.md` and `Templates.md` already existed and were left unchanged.
  All nine are listed in [Impl/README.md](Impl/README.md). No code changed.
- **2026-10-29** — Required the *Differences from Spec.md* rows to be sorted by importance, most important
  first (RULE 0, [Impl/README.md](Impl/README.md) conventions, Decisions). Impl/README.md index was out of
  step with the files in `Impl/` (renamed `BuildAndCache.md` and `AgentAutoformalizationPipeline.md`, no
  `LEAN4OEIS.md`); links fixed and the `LEAN4OEIS` row removed. The existing tables in Database.md and Templates.md are not reordered yet
  (open item 21). No code changed.

- **2026-10-29** — Moved the progress log from AGENTS.md into this file. RULE 1 now sends progress here and requires new open items and next steps to be written in the matching `Impl/*.md` document instead of AGENTS.md. The existing open items stay in AGENTS.md until they are moved. Added the header link, the Files row and a Decisions bullet in AGENTS.md. No code changed.

- **2026-10-29** — Reverted the open-items part of the change above at the user's request: open items and next steps are written in AGENTS.md again. RULE 1, the RULE reminder and the Decisions bullet in AGENTS.md now say so. Progress is still kept in this file. No code changed.
