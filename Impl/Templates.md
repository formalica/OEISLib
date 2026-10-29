# Templates

Snapshot taken 2026-10-29: how `lake exe oeis-template` and the four templates are implemented, and where this differs from the `# Templates` section of [Spec.md](../Spec.md) (and the other Spec sections that constrain templates).
Sources: [Scripts/OeisTemplate.lean](../Scripts/OeisTemplate.lean) (runner), [Scripts/OeisTemplate/](../Scripts/OeisTemplate/) (interface and toolkit), [Scripts/Templates/](../Scripts/Templates/) (one module per template), [OEISLib/Common/](../OEISLib/Common/) (shared math). The tables they write are described in [Database.md](Database.md).

## Current templates

| Template | Sequences (ok / skipped) | Items | Sections written |
| --- | ---: | ---: | --- |
| `walkN3` | 3,254 / 0 | 6,508 | `maindef`, `mathematica` |
| `coxeter` | 2,302 / 0 | 7,210 | `maindef`, `formula`, `mathematica`, `pari`, `magma` |
| `primeCongruent` | 979 / 36 | 4,130 | `maindef`, `mathematica`, `pari`, `magma` |
| `sqrtContinuedFraction` | 967 / 8 | 2,819 | `maindef` (computable and `prop`), `mathematica` |

A full run of one template takes 3 to 6 seconds. Skipped sequences are those whose title does not parse as a member of the family (`primeCongruent`: titles such as `Primes congruent to 1 or 2 modulo 4`; `sqrtContinuedFraction`: square radicands).

### `walkN3`

- Title: the step set `{(x, y, z), ...}` of walks in `N^3`. The `%t` program (`aux[i_, j_, k_, n_] := Which[...]; Table[Sum[aux[...]], {n, 0, K}]`) is recognized at the start of the `mathematica` block, in any spacing; its recursion offsets must encode the same step set as the title.
- Verification: its own dynamic program (`dpValues`), not `OEISLib.Common.Walk3`, for `n` up to `min(12, K, index of the last published term)`. Flags: `--table-max=K`, `--check-cap=K`.
- Items: `maindef` = `fun n => Walk3.count [steps] n`; `mathematica` = `Walk3.countDp [steps]` with `formula n = main n`. A sequence whose program does not match still gets the `maindef` item.

### `coxeter`

- Title: `g` generators, relation exponent `r` (`3 ≤ g, r ≤ 60`), offset 0. All terms are compared with `OEISLib.Common.Coxeter.coxSeq g r`. Flag: `--check-cap=K`.
- Snippets: g.f. (rational and Greubel's factored form) and the order-`r` recurrence in `%F` (a g.f. split over up to 4 lines is joined with `\n`), `coxG[...]` and `CoefficientList[Series[...]]` in `mathematica`, `Vec(...)` in `pari`, `PowerSeriesRing` in `magma`. Each becomes `coeffsUpTo g r K` (`K` = the snippet's own bound, else the number of verified terms minus one) with a proof that `formula[n] = main n`.
- 859 sequences have a g.f. of degree `r - 1` that no recognizer covers; they get no `formula` item.

### `primeCongruent`

- Title: `Primes congruent to a mod m.`, offset 1 (`PNat`). The bound is the last published term; the enumeration `membersUpTo a m bound` is compared with all terms. Flag: `--check-cap=K`.
- Items: `maindef` = `nthIn a m (n.val - 1) bound`; Magma list and `Select[Range[s, e, m], PrimeQ]` = `membersUpTo` with `formula[i]? = some (main (i + 1))`; PARI `is(n)=isprime(n) && n%m==a` = `isMember a m` with `formula n = true ↔ Nat.Prime n ∧ n % m = a`; `Select[Prime[Range[K]], MemberQ[{a}, Mod[#, m]] &]` = `selectFrom ((primesUpTo bound).take K) a m`, equal to the enumeration under the hypothesis that the lengths agree.

### `sqrtContinuedFraction`

- Title: `Numerators of continued fraction convergents to sqrt(d).`, non-square `d`, offset 0. A001077 and A005667 are the two sequences that carry a leading `1` (`prependsOne`). All terms are compared with `OEISLib.Common.SqrtContinuedFraction.program`.
- Items: `maindef` computable (`computed d n`), `maindef` `prop` (`relation d n p`, proved equivalent to `p = main n` through `relation_iff_eq_computed`), and one `mathematica` item per distinct whole-line expression (`Numerator[Convergents[Sqrt[d],K]]`, `...//Numerator`, `Table[...]`, each optionally inside `Join[{1}, ...]`). An expression whose leading-one convention or values disagree with the sequence is not recorded.

## Runner

`lake exe oeis-template <template> (--all | --bucket A147 | --seq A147999) [--force] [--dry-run] [--limit N] [--db PATH] [--<flag>=V]`. The binary at `.lake/build/bin/oeis-template` avoids the library warnings that `lake exe` replays.

- Selection: `--all` / `--bucket` use the template's `selectWhere` SQL over `sequence`; `--seq` adds explicit names. `--limit` truncates.
- Each sequence is loaded from the database (`loadSource`), never from `oeisdata/`. The whole run is one transaction.
- Without `--force`, a sequence that already has items from the template is skipped. `--force` re-formalizes it and updates the rows in place.
- `--dry-run` prints every accepted item (section, span, original text, Lean fields) and writes nothing.
- A template accepts only the flags in its `flags` array; the runner rejects any other `--flag` before touching the database.
- Exit code 1 if any sequence failed (verification mismatch, or a candidate whose text is not in the stored section).

## Interface

[Base.lean](../Scripts/OeisTemplate/Base.lean) defines the contract; [Source.lean](../Scripts/OeisTemplate/Source.lean) the input.

- `SeqSource`: name, title, offset, terms, `%F` lines, `%C` lines, program blocks. The text a candidate is quoted from, by `language`: `maindef` = title, `formula` = `%F` lines joined with `\n`, `comment` = `%C` lines joined with `\n`, anything else = the `program` block `(language, block_index)`. The `(PARI)` / `(Magma)` language marker is not part of the stored block text.
- `Template`: `name`, `descr`, `selectWhere`, `flags`, and the pure function `formalize : extras → SeqSource → Verdict` (`skip`, `fail` or `items`). It has no database handle.
- `Candidate`: section, block index, `originalText`, `leanKind`, `argKind`, `leanType`, `leanCode`, `auxCode`, `imports`, `eqStatement`, `eqProof`, `verifiedUpto`, `params`, `notes`.
- `publish` is the only writer. For each candidate it finds `originalText` in the section text; if absent it rejects the candidate and nothing is written. Otherwise it derives the span (characters), `formula_hash = hex(String.hash originalText)` and `source_hash`, then upserts into `formalization_item` with `producer = 'template:<name>'`. Afterwards it deletes this producer's items of the sequence that were not submitted again, and points `sequence.main_item_id` at the computable `maindef` item unless another producer owns it. With `--dry-run` it only checks.
- Status is `STATUS_VERIFIED` when `verifiedUpto > 0` (the number of leading terms the template compared with `sequence.data`), else `STATUS_UNKNOWN`; `verified_ranges` records `{from, to, result: pass}` from the offset.

### Lean content of an item

Name-free, so a generator can re-render it under any names:

| Field | Meaning |
| --- | --- |
| `leanKind` | `prop`, `computable`, `nonComputable`, `thm` |
| `leanType`, `leanCode` | type and body of the declaration; `«self»` is the declaration itself |
| `auxCode` | declarations placed before it (unused so far) |
| `eqStatement`, `eqProof` | statement and tactic proof of `formula_eq`; `«self»` is the item, `«main»` the sequence's main definition |
| `imports` | module names, e.g. `OEISLib.Common.Coxeter` |

Family parameters are inlined as literals (`coxSeq 4 3 n`), never named constants. Rendering an item is `def formula : <leanType> := <leanCode>` plus `theorem formula_eq : <eqStatement> := by <eqProof>` with `«self»` → `formula` and `«main»` → `Axxxxxx`.

### Toolkit

[Recognize.lean](../Scripts/OeisTemplate/Recognize.lean): whitespace-tolerant matching over a character array (`eatLit`, `digitsFrom`, `skipWs`, `endAfterSemicolon`); `codeEnd` (end of a line's code, before a trailing ` - _Name_, date` credit or `(* ... *)` comment); `hitsInText` / `hits` (apply line recognizers to a section, first hit per flavor, or per distinct text with `byText`, optionally over windows of several lines); `termsNat` and `checkPrefix` (compare computed values with the data).

## Adding a template

1. Shared math goes to `OEISLib/Common/<Name>.lean`, namespace `OEISLib.Common.<Name>`, computable, with the bridge lemmas proved once.
2. `Scripts/Templates/<Name>.lean`, in this order: `parseTitle`; recognizers `String → Option Nat` grouped per language; computation and `checkPrefix`; one candidate for the main definition (`language := Section.maindef`, `originalText := src.title`) and one per recognized snippet; `def template : Template`. [Coxeter.lean](../Scripts/Templates/Coxeter.lean) is the reference.
3. Import it in [Scripts/Templates/Registry.lean](../Scripts/Templates/Registry.lean) and list it in `templates`.
4. Add `#guard` tests (see [SqrtContinuedFractionTest.lean](../Scripts/Templates/SqrtContinuedFractionTest.lean)); they run during `lake build Scripts`.
5. `lake build oeis-template`, then `--seq A... --dry-run`, then `--all`.

## Tests

- `lake build Scripts` runs the `#guard` suites: [Tests.lean](../Scripts/OeisTemplate/Tests.lean) (original-text check, `codeEnd`, hit scanning, JSON decoding) and the sqrt template's recognizer and verdict tests.
- `lake exe oeis-template-test` ([IntegrationTest.lean](../Scripts/OeisTemplate/IntegrationTest.lean)): `publish` on a scratch database (accept, reject, idempotence, dry run, stale removal, other producers untouched) and migration of a legacy-schema database.
- The Lean content of items is compiled only by hand: render the items of a sequence into a scratch file and run `lake env lean`. 180 random sequences across the four templates compiled without errors.

## Limitations

- `oeis-gen` does not read `formalization_item` yet, so no `Equiv_<hash>.lean` is produced from template items.
- No template recognizes `comment` text.
- Templates verify in-process against `sequence.data`; there is no `oeis-verify` to re-check them.
- Stored `%F`/`%C` lines are trimmed and empty lines are dropped, so "original text" means the stored form, not the bytes of the `.seq` file.
- Dropped in the port: `primeCongruent`'s `nth_spec` theorem and `sqrtContinuedFraction`'s isolated compile check.

## Differences from Spec.md

Only places where Spec.md states something and the implementation does otherwise.

| Spec.md | Implementation |
| --- | --- |
| Templates: unknown args passed through to the template should be propagated to it. | The runner rejects every `--flag` the template did not declare in `flags`. |
| Templates: `--dry-run` generates files in memory and prints them, and does not change any table. | It prints the items, not files. The runner opens the database through `Db.openDb`, which migrates an outdated schema even in a dry run. |
| Templates: the table of found templates is stored in a text file or database, and a template is marked completed there after it is implemented. | `Scripts/templates.txt` (from `name_templates.py`) exists, but nothing marks implemented templates in it. |
| OEISLib: `Equiv` `formula` has the signature of a main-definition declaration (value form) or of `prop` (proposition form). | Template items use other shapes: `List Nat` (coxeter, primeCongruent enumerations; `formula[i]? = some (main (i + 1))`), `Nat → Bool` (PARI membership test), and a conditional equality (`primeCongruent` first-primes). Only `walkN3` (`Nat → Nat`) and the `sqrtContinuedFraction` `prop` item follow the Spec's forms. |
| Formalization: a formula given by a generating function defines `gen_func : PowerSeries` and the formula calls `.coeff` on it. | `coxeter` g.f. snippets are truncated coefficient lists `coeffsUpTo g r K`; no `PowerSeries` is defined. |
| OEISLib TO_BE_CHANGED: move the OEISLib files to `LOEIS/Common`, rename `LOEIS` to `OEISLib`, update imports. | The files are in `OEISLib/Common/` (`OEISLib.Common.*`), but `LOEIS` is not renamed. |
