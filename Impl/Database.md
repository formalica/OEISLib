# Database

Snapshot of `Metadata/oeis.db` taken 2026-10-29 (after `oeis-template` started writing `formalization_item`), and where it differs from the `# Database` section of [Spec.md](../Spec.md).
Schema sources: [Db.lean](../Scripts/OeisIngest/Db.lean) (`schemaSql`, `migrate`) and [db.py](../Scripts/formalize/db.py) (`MIGRATION_SQL`, `_migrate`); both migrate an older database in place.

## Current tables

| Table | Rows | Written by | Purpose |
| --- | ---: | --- | --- |
| `sequence` | 398,471 | `oeis-ingest` | One row per `.seq` file: title, offsets, keywords, terms, verbatim `%F` and `%C` lines. |
| `formula` | 539,052 | `oeis-ingest` | One row per `%F` line. Raw text only, never formalized. |
| `program` | 544,711 | `oeis-ingest` | One row per program block from `%p`, `%t`, `%o`. |
| `program_gap` | 5 | `formalize` | Stretches of a program block that no `formalization_item` claims. |
| `formalization_batch` | 10 | `formalize` | One LLM call: model, status, chat history, skill text sent. |
| `formalization_item` | 20,673 | `formalize`, `oeis-template` | One formalization of one stretch of original text: span, Lean code, verification result. |
| `skill_suggestion` | 0 | `formalize` | Skill edits proposed by the model. Never applied automatically. |

Indexes exist on `formula(hash)`, `formula(status)`, `program(hash)`, `program(language)`,
`program(language, status)`, `sequence(status)`, `formalization_item(batch_id)`,
`formalization_item(oeis_name)`, `formalization_item(language, status)`,
`formalization_item(producer, language, status)`, `formalization_item(oeis_name, source_hash)`,
`formalization_batch(language, status)`, `program_gap(oeis_name, language)` and `program_gap(language, status)`.

### `sequence`

- `name` (primary key, `Axxxxxx`), `title` (`%N`), `offset` (first `%O` component), `offset_first_big` (second `%O` component, set for 396,433 rows).
- `keywords` and `data` are JSON. `data` merges the `%S`, `%T`, `%U` terms into one list. `data_count` is its length.
- `formula_lines` (JSON) holds the `%F` lines and `comment_lines` (JSON) the `%C` lines, verbatim in file order with the tag stripped and empty lines dropped. This is the text templates quote from: the `formula` section text is the lines joined with `\n`. `formula_lines` is the former `all_unformalized_formulas_text`, renamed by `migrate`.
- `unformalized_formula_hashes` (JSON) is still filled by ingest. `formalized_formula_hashes` is `[]` in every row and written by nothing.
- `main_item_id` points at the `formalization_item` that is the current main definition. `oeis-template` sets it to its computable `maindef` item (7,502 rows) unless another producer owns it. `main_definition_hash` is NULL in every row. Spec.md asks for a "current main definition key" in its body and drops `main_definition_hash` in TO_BE_CHANGED; `main_item_id` was chosen as the key.
- `status` is `STATUS_UNKNOWN` in every row.
- `source_file` and `updated_at` are provenance.

### `formula`

- Primary key `(oeis_name, hash)`. `hash` is 16 hex characters of `String.hash`.
- `human_written_formula` is the `%F` text. `source_tag` is `F` and `line_index` is its position.
- `formalized_formula`, `type`, `verification_values`, `disproved_values`, `additional_conditions` are empty. `status` is `STATUS_UNKNOWN` in every row.
- Nothing writes to it any more: templates record formalizations in `formalization_item` and read the original `%F` text from `sequence.formula_lines`.

### `program`

- Primary key `(oeis_name, language, block_index)`. `source_tag` is `p`, `t` or `o`. `text` is the block verbatim. `%p`/`%t` blocks are never split; `%o` is split at each `(Lang)` marker, which is not part of `text`.
- `hash` (16 hex characters of `String.hash`, used as `formalization_item.source_hash`), `line_count`, `status` (`STATUS_UNKNOWN` in every row).
- Largest languages: mathematica 220,935, pari 153,865, maple 63,768, magma 38,603, python 26,036, sagemath 15,331.

### `program_gap`

- `oeis_name`, `language`, `source_hash`, `span_start`, `span_end`, `text`, `batch_id`, `reason`.
- `status` is `STATUS_UNFORMALIZED` (3 rows) or `STATUS_GAP_TRIVIAL` (2 rows).
- Unique on `(oeis_name, language, source_hash, span_start, span_end)`.

### `formalization_batch`

- `language`, `model`, `status` (`BATCH_PENDING` 5, `BATCH_RUNNING` 2, `BATCH_OK` 2, `BATCH_PARTIAL` 1), `oeis_names` (JSON), `attempts`, `max_attempts`.
- `chat_history` holds the serialized messages that `retry --batch-id` continues. `skill_text` is the skill as the model saw it.
- `last_error`, `usage` (JSON), `created_at`, `updated_at`.

### `formalization_item`

- `oeis_name`, `producer` (`llm`, `template:<name>`, later `genexpr`), `producer_params` (JSON: the family parameters, e.g. `{"g":4,"r":3}`), `batch_id` (LLM rows only, NULL otherwise).
- `language` is the section the text came from: `maindef` (the `%N` title), `formula` (`%F`), `comment` (`%C`, no producer yet) or a program language (`maple`, `mathematica`, `pari`, `magma`, ...). `block_index` selects the program block; `source_hash` is `program.hash` (or the hash of the section text).
- `original_text`, `span_start`, `span_end`: the exact quoted text and its character offsets inside the section text (see [Templates.md](Templates.md#interface)). `formula_hash` is `hex(String.hash original_text)` for templates. A template cannot write a row unless the text occurs in the stored section.
- `lean_kind` (`prop`, `computable`, `noncomputable`, `theorem`), `arg_kind`, `lean_type` (type of the declaration), `lean_code` (its body), `imports` (JSON module names), `aux_code` (empty in every row). Template items are name-free: `«self»` is the declaration, `«main»` the sequence's main definition, family parameters are inlined.
- `eq_statement` / `eq_proof`: statement and tactic proof of `formula_eq`, the item's agreement with the main definition. Spec.md only mentions the `data_eq` proof, but templates have real `formula_eq` proofs that must be stored. `data_eq_proof` / `data_eq_aux` are NULL in every row.
- `lean_file`, `check_file`, `depends_on` (JSON) are LLM-only.
- `status` (`STATUS_VERIFIED` 20,667 template rows + 4 LLM rows, `STATUS_COMPILE_ERROR` 2), `failure_kind`, `failure_points` (JSON), `compiler_output`, `verified_upto` (leading terms checked), `verified_ranges` (JSON `[{"from","to","result"}]`, written by templates with `pass`), `attempt`, `notes` (template flavor).
- Unique on `(oeis_name, language, formula_hash, producer, lean_kind)`: the same text can have a `prop` and a `computable` formalization, and a producer's re-run updates in place. For LLM rows `formula_hash` matches no row of `formula`; the link is not enforced.
- Template rows per producer: coxeter 7,210 (2,302 sequences), primeCongruent 4,130 (979), sqrtContinuedFraction 2,819 (967), walkN3 6,508 (3,254).
- `verified_definitions` (Python) offers the LLM only `producer = 'llm'` rows, because template and LLM `lean_code` follow different conventions.

### `skill_suggestion`

- `batch_id`, `language`, `kind`, `text`, `applied` (0 means not applied). The table has no rows yet.

## Known issues

- 517 `program.language` values are not language names (examples: `+`, `0 to 49`, `1 to 50`, `0 to 26`). The cause is not investigated.
- 2 batches are in `BATCH_RUNNING`. It is not checked whether they are stale from interrupted runs.
- `oeis-ingest` stores `%F`/`%C` lines trimmed and without empty lines, so "original text" means the stored form, not the exact bytes of the `.seq` file.
- `formula`, `sequence.unformalized_formula_hashes` and `sequence.formalized_formula_hashes` are redundant now.
- A database created before this schema is migrated on the first `oeis-ingest`, `oeis-template` or `python -m formalize` call, including a `--dry-run`.

## Differences from Spec.md

Only places where Spec.md states something and the implementation does otherwise. Things Spec.md does not cover, and things that match it, are described above.

| Spec.md | Implementation |
| --- | --- |
| `sequence` contains the original text of the `%N %O %K %F %T %o %C` lines. | `%N`, `%F`, `%C` are stored verbatim. `%O`, `%K` and the terms are stored parsed. Program lines are in `program`, not in `sequence`. |
| `sequence` stores the hash of the `.seq` file. | No hash; `source_file` holds the path only. |
| `sequence.status` is `STATUS_COMPLETE`, `STATUS_FORMALIZED`, `STATUS_DEFINED` or `STATUS_NOT_STARTED`. | `STATUS_UNKNOWN` in all 398,471 rows; none of the four values is written anywhere. |
| Re-running ingest only inserts new sequences; existing rows stay the same. | Ingest upserts: OEIS-derived columns are refreshed on every run (`ON CONFLICT ... DO UPDATE` in [Db.lean](../Scripts/OeisIngest/Db.lean)). |
| `sequence` stores the offset of each argument, computed by the algorithms of `Spec/Database.md`. | Only `offset` and `offset_first_big` (the raw `%O` components) are stored. `Spec/Database.md` is empty, so the algorithm is not written down. |
| TO_BE_CHANGED: `main_definition_hash`, `formalized_formula_hashes` and `unformalized_formula_hashes` are not needed. | All three columns still exist (NULL, `[]`, filled by ingest). |
| TO_BE_CHANGED: the `formula` table is no longer needed (merged into `formalization_item`). | It still exists and ingest still fills it (539,052 rows). |
| `formalization_item` holds Lean code without any name. | LLM rows (6) store a full declaration with names and binders in `lean_code`, e.g. `def formula (n : Nat) : Nat := ...`. |
| LLM section TO_BE_CHANGED: hashes become `hex(String.hash)`, not blake2b. | LLM rows still use blake2b for `formula_hash`; template rows use `String.hash`. |
| `formalization_item` records for which values a formalization passed, failed or timed out, as ranges. | Templates write `pass` ranges only. LLM rows keep a single `verified_upto` and `failure_points`. No row has a timeout state. |
| `oeis-show` shows which formulas of which sections are formalized, in colour; TO_BE_CHANGED: `formalize show --seq` must show all sections. | There is no `oeis-show`. `python -m formalize show --seq` colours program blocks only; `maindef`, `formula` and `comment` sections are not shown. |
