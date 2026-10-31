# Templates

Snapshot taken 2026-10-31: how `lake exe oeis-template` and the five templates are implemented, and where this differs from the `# Templates` section of [Spec.md](../Spec.md) (and the other Spec sections that constrain templates).
Sources: [Scripts/OeisTemplate.lean](../Scripts/OeisTemplate.lean) (runner), [Scripts/OeisTemplate/](../Scripts/OeisTemplate/) (interface and toolkit), [Scripts/Templates/](../Scripts/Templates/) (one module per template), [OEISLib/Common/](../OEISLib/Common/) (shared math). The tables they write are described in [Database.md](Database.md).

There are two kinds of template (`TemplateKind`): a **family** template (`walkN3`, `coxeter`, `primeCongruent`, `sqrtContinuedFraction`) is selected by the title, rebuilds the exact original text from the family's parameters and writes only when that text is really there; a **scan** template (`linearRecurrence`) searches every section of any sequence for texts of one shape and parses them.

## Current templates

| Template | Sequences (ok / skipped) | Items | Sections written |
| --- | ---: | ---: | --- |
| `walkN3` | 3,254 / 0 | 6,508 | `maindef`, `mathematica` |
| `coxeter` | 2,302 / 0 | 7,210 | `maindef`, `formula`, `mathematica`, `pari`, `magma` |
| `primeCongruent` | 979 / 36 | 4,130 | `maindef`, `mathematica`, `pari`, `magma` |
| `linearRecurrence` (scan) | 29,365 / 163,017 | 29,767 | `maindef`, `formula`, `comment`, `mathematica`, `magma`, `maple`, `sagemath`, `python`, `pari`, `haskell` |
| `sqrtContinuedFraction` | 967 / 8 | 2,819 | `maindef` (computable and `prop`), `mathematica` |

A full run of one family template takes 3 to 6 seconds; `linearRecurrence --all` takes about a minute. Skipped sequences of a family template are those whose title does not parse as a member of the family (`primeCongruent`: titles such as `Primes congruent to 1 or 2 modulo 4`; `sqrtContinuedFraction`: square radicands). Skipped sequences of `linearRecurrence` are the ones the prefilter selected but where no verified recurrence was found.

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

### `linearRecurrence` (scan)

Sources: [LinearRecurrence.lean](../Scripts/Templates/LinearRecurrence.lean) (selection, dedup, Lean text) and [LinearRecurrence/](../Scripts/Templates/LinearRecurrence/) (`Lin` expression parser, `Core` recurrence and verification, `Statement`, `Mathematica`, `Programs`, `Scripting`). It finds homogeneous linear recurrences with constant coefficients `a(n) = c₁·a(n-1) + … + c_k·a(n-k)` and formalizes each as Mathlib's `LinearRecurrence`.

- **Selection.** `selectWhere` is a prefilter (offset ≥ 0, no `tabl`/`tabf`; some section has `(n-`/`(n+`, or a program has `LinearRecurrence`, `RecurrenceTable`, `[n_`, `(n-`, `Self(`, `[-1]` or `zipWith`). 192,382 sequences pass; 29,365 yield items.
- **Recognized texts.** Statements `lhs = rhs` in the title, `%F` and `%C` with the sequence's own name `a` or its A-number (the title may call the sequence anything, `F(n) = F(n-1) + F(n-2)`), in any lag form (`a(n+2) = 3a(n+1) - a(n)`, `a(n+2) - 3a(n+1) + a(n) = 0`), with the guard (`for n >= 2`) and the stated initial values (`a(0)=1, a(1)=2`, `a(0)=a(1)=1`) next to it, before or after, as part of the quoted text. A chain never reaches across the author credit of a line. Wolfram: `LinearRecurrence[{c…}, {a…}, n | {m, n}]`, `RecurrenceTable[{…}, a, {n, lo, hi}]`, and `a[n_] := a[n] = …` with `a[0] = …`. PARI `a(n)=if(n<2, n, …)`; Maple `proc`/`->`/`` `if` `` and `a(0):=…: a(n):=…`; Magma `[n le 2 select … else Self(n-1)+…: n in [1..N]]` (with `I[n]` lists); Python/Sage `def` ladders and `a = [..]` + `append`; Haskell clauses and `zipWith (+)` streams. The function bodies are read into trees of conditions on `n` (`BExpr`) that are evaluated at every published index.
- **Not formalized:** a constant or `n`-dependent term (`a(n) = 1 + a(n-1)`, `n*a(n-1)`), products or powers of terms, divisions, other function names in prose, orders above 1000 (`a(n+25239592216021) = a(n)` is a period), matrix powers, generating functions, `Nest`/`Fold`, recurrences that only hold from a later index than the order.
- **Verification** (`Rec.verify`). The recurrence is run from the first `k` published terms and has to reproduce every term up to `--check-cap` (default 2000), with at least `--min-extra` (default 3) terms beyond the first `k`. Initial values the text states and a program's own output are only cross-checked against the data, so shifted or wrong initial values reject the text; the Lean item always starts from the published terms.
- **Dedup.** Two texts are the same formalization when their coefficient lists are equal (trailing zero lags stripped). All their texts are the item's sources, in canonical order; a source lying inside another source of the same section is dropped.
- **Items.** Value type `DType` is `Nat` unless the sequence has a negative term or the recurrence a negative coefficient or initial value; a `Nat`-valued sequence over `Int` is wrapped in `Int.toNat`. `auxCode` holds `def linearrec : LinearRecurrence DType := ⟨k, ![c_k, …, c₁]⟩` (oldest lag first) and `def init : Fin k → DType := ![…]`; `imports` is `Mathlib.Algebra.LinearRecurrence`. A recurrence whose sources include the title is the main definition (the first one found becomes `sequence.main_item_id`): `argKind` and `leanType` follow the offset (`Nat`, `PNat` through `n.val - 1`, `NatSub`), no equation. Every other item has the signature of `fn` (`Nat → RetType`), `leanCode = fun n => linearrec.mkSol init (n - offset)`, and `eqStatement = ∀ n : Nat, [offset ≤ n →] «self» n = «main».fn n` with `eqProof = sorry`: the sequence is abstract, so the template cannot prove it. `params` holds `{"order","coeffs","dtype"}`, `notes` the flavors (`statement`, `wolfram-LinearRecurrence`, `magma-select`, ...).
- **Result of the full run** (2026-10-31): 29,767 items. Sources by section: `%F` 23,175, Mathematica 17,006, Magma 3,710, title 1,471, `%C` 94, Maple 82, Sage 71, Python 27, PARI 16, Haskell 6. Items with 1 / 2 / 3 / ≥4 sources: 16,997 / 9,875 / 2,706 / 189. 26,395 items use `Int`. 1,471 main definitions.

## Runner

`lake exe oeis-template <template> (--all | --bucket A147 | --seq A147999) [--force] [--dry-run] [--limit N] [--verbose] [--db PATH] [--<flag>=V]`. The binary at `.lake/build/bin/oeis-template` avoids the library warnings that `lake exe` replays.

- Selection: `--all` / `--bucket` use the template's `selectWhere` SQL over `sequence`; `--seq` adds explicit names. `--limit` truncates.
- Each sequence is loaded from the database (`loadSource`), never from `oeisdata/`. The whole run is one transaction.
- Without `--force`, a sequence that already has items from the template is skipped. `--force` re-formalizes it and updates the rows in place.
- `--dry-run` prints every accepted item (sections and spans, every original text, Lean fields) and writes nothing.
- A template accepts only the flags in its `flags` array; the runner rejects any other `--flag` before touching the database.
- A `scan` template selects many sequences that yield nothing, so the runner only counts its skips; `--verbose` prints them with the reasons. With `--force`, a sequence the template no longer matches loses its earlier items from that template.
- Exit code 1 if any sequence failed (verification mismatch, or a candidate whose text is not in the stored section).

## Interface

[Base.lean](../Scripts/OeisTemplate/Base.lean) defines the contract; [Source.lean](../Scripts/OeisTemplate/Source.lean) the input.

- `SeqSource`: name, title, offset, terms, `%F` lines, `%C` lines, program blocks. The text a candidate is quoted from, by `language`: `maindef` = title, `formula` = `%F` lines joined with `\n`, `comment` = `%C` lines joined with `\n`, anything else = the `program` block `(language, block_index)`. The `(PARI)` / `(Magma)` language marker is not part of the stored block text.
- `Template`: `name`, `descr`, `kind` (`family` or `scan`), `selectWhere`, `flags`, and the pure function `formalize : extras → SeqSource → Verdict` (`skip`, `fail` or `items`). It has no database handle.
- `Source`: one original text a formalization stands for: `language`, `blockIndex`, `originalText` and an optional `start?`, the character offset inside the section text (without it the first occurrence is taken).
- `Candidate`: `sources` (one or more), `leanKind`, `argKind`, `leanType`, `leanCode`, `auxCode`, `imports`, `eqStatement`, `eqProof`, `verifiedUpto`, `params`, `notes`.
- `publish` is the only writer. For each candidate it locates every source in its section text; if any is absent it rejects the candidate and nothing is written. Otherwise it sorts the sources into canonical order (title, `%F`, `%C`, then programs by language, block and position; two sources at the same place are one) and derives each span (characters) and `source_hash`. The item's `formula_hash` is `hex(String.hash)` of its texts joined with a newline, so a single text gives the hash of that text. It upserts into `formalization_item` with `producer = 'template:<name>'`, rewrites the item's `formalization_source` rows, then deletes this producer's items of the sequence that were not submitted again (their sources go with them). The first computable item whose first source is the title becomes `sequence.main_item_id`, unless another producer owns it. With `--dry-run` it only checks.
- Status is `STATUS_VERIFIED` when `verifiedUpto > 0` (the number of leading terms the template compared with `sequence.data`), else `STATUS_UNKNOWN`; `verified_ranges` records `{from, to, result: pass}` from the offset.

### Lean content of an item

Name-free, so a generator can re-render it under any names:

| Field | Meaning |
| --- | --- |
| `leanKind` | `prop`, `computable`, `nonComputable`, `thm` |
| `leanType`, `leanCode` | type and body of the declaration; `«self»` is the declaration itself |
| `auxCode` | declarations placed before it (`linearRecurrence`: `linearrec` and `init`) |
| `eqStatement`, `eqProof` | statement and tactic proof of `formula_eq`; `«self»` is the item, `«main»` the sequence's main definition |
| `imports` | module names, e.g. `OEISLib.Common.Coxeter` |

Family parameters are inlined as literals (`coxSeq 4 3 n`), never named constants. Rendering an item is `def formula : <leanType> := <leanCode>` plus `theorem formula_eq : <eqStatement> := by <eqProof>` with `«self»` → `formula` and `«main»` → `Axxxxxx`.

### Toolkit

[Recognize.lean](../Scripts/OeisTemplate/Recognize.lean): whitespace-tolerant matching over a character array (`eatLit`, `digitsFrom`, `skipWs`, `endAfterSemicolon`); `codeEnd` (end of a line's code, before a trailing ` - _Name_, date` credit or `(* ... *)` comment); `hitsInText` / `hits` (apply line recognizers to a section, first hit per flavor, or per distinct text with `byText`, optionally over windows of several lines; a `Hit` knows its character offset `start` and converts to a `Source`); `termsNat` and `checkPrefix` (compare computed values with the data).

## Adding a template

1. Shared math goes to `OEISLib/Common/<Name>.lean`, namespace `OEISLib.Common.<Name>`, computable, with the bridge lemmas proved once.
2. `Scripts/Templates/<Name>.lean`, in this order: `parseTitle`; recognizers `String → Option Nat` grouped per language; computation and `checkPrefix`; one candidate for the main definition (`sources := #[{ language := Section.maindef, originalText := src.title }]`) and one per recognized snippet (`sources := #[hit.source]`); `def template : Template`. [Coxeter.lean](../Scripts/Templates/Coxeter.lean) is the reference. A scan template sets `kind := .scan`, parses texts at any position (`LinearRecurrence/Statement.lean`, `scanText`), groups what it finds into one candidate per distinct formalization with all its texts as `sources`, and gives `selectWhere` as a cheap prefilter.
3. Import it in [Scripts/Templates/Registry.lean](../Scripts/Templates/Registry.lean) and list it in `templates`.
4. Add `#guard` tests (see [SqrtContinuedFractionTest.lean](../Scripts/Templates/SqrtContinuedFractionTest.lean)); they run during `lake build Scripts`.
5. `lake build oeis-template`, then `--seq A... --dry-run`, then `--all`.

## Tests

- `lake build Scripts` runs the `#guard` suites: [Tests.lean](../Scripts/OeisTemplate/Tests.lean) (original-text check, canonical source order and identity, `codeEnd`, hit scanning, JSON decoding), the sqrt template's recognizer and verdict tests, and [LinearRecurrenceTest.lean](../Scripts/Templates/Tests/LinearRecurrenceTest.lean) (the parser's accepts and refusals, every recognizer, verification, and whole-sequence verdicts).
- `lake exe oeis-template-test` ([IntegrationTest.lean](../Scripts/OeisTemplate/IntegrationTest.lean)): `publish` on a scratch database (accept, reject, idempotence, multi-source items with canonical order and joined hash, dry run, stale removal with sources, other producers untouched) and migration of a database in the previous schema (one source row per item, LLM hashes recomputed, cascade delete).
- The Lean content of items is compiled only by hand: render the items of a sequence into a scratch file and run `lake env lean`. 180 random sequences across the four family templates, and 275 random `linearRecurrence` items (with the stub `A… : Nat → Nat` and `A….fn`), compiled without errors.

## Limitations

- `oeis-gen` does not read `formalization_item` yet, so no `Equiv_<hash>.lean` is produced from template items.
- The family templates recognize no `comment` text; `linearRecurrence` recognizes recurrences in `%C` (94 sources).
- `LinearRecurrence.mkSol` is irreducible and recurses without memoization, so evaluating a `linearRecurrence` item in Lean at a large index is exponential; the template checks the recurrence with its own integer iteration. A future `oeis-verify` has to evaluate these items differently.
- A `linearRecurrence` item is only as faithful as its text allows: initial values come from the data, so `a(0) = 1, a(n) = 3*a(n-2)` is formalized with the published `a(1)`.
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
| OEISLib: `Equiv` `formula` has the signature of a main-definition declaration (value form) or of `prop` (proposition form). | Template items use other shapes: `List Nat` (coxeter, primeCongruent enumerations; `formula[i]? = some (main (i + 1))`), `Nat → Bool` (PARI membership test), and a conditional equality (`primeCongruent` first-primes). Only `walkN3` (`Nat → Nat`), `linearRecurrence` (`Nat → RetType`, the shape of `fn`) and the `sqrtContinuedFraction` `prop` item follow the Spec's forms. |
| Formalization: a formula given by a generating function defines `gen_func : PowerSeries` and the formula calls `.coeff` on it. | `coxeter` g.f. snippets are truncated coefficient lists `coeffsUpTo g r K`; no `PowerSeries` is defined. |
| OEISLib TO_BE_CHANGED: move the OEISLib files to `OEISLib/Common`, rename `OEISLib` to `OEISLib`, update imports. | The files are in `OEISLib/Common/` (`OEISLib.Common.*`), but `OEISLib` is not renamed. |
