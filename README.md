---
language:
- code
license: cc-by-sa-4.0
pretty_name: OEISLib - Lean OEIS Formalization
size_categories:
- 100K<n<1M
source_datasets:
- OEIS
tags:
- mathematics
- formal-verification
- lean
- oeis
- sequence-formalization
---

# OEISLib

Formalizing OEIS sequences in Lean 4 + Mathlib. See [SPEC.md](SPEC.md) and [OEIS.md](OEIS.md)
for the design, and [AGENTS.md](AGENTS.md) for current project status.

## Setup

### 1. Clone this repository

```bash
git clone https://huggingface.co/datasets/formalica/lean4oeis
cd lean4oeis
```

This gives you the Lean sources and scripts only. The OEIS raw data and the metadata database
are fetched separately (next two steps) so that a plain clone stays small.

### 2. Install Lean

Install [elan](https://github.com/leanprover/elan) (the Lean version manager) if you don't
have it, then let it pick up the toolchain pinned in [lean-toolchain](lean-toolchain)
(`leanprover/lean4:v4.34.0-rc1`):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan toolchain install $(cat lean-toolchain)
lake exe cache get   # download prebuilt Mathlib .olean files instead of building from source
```

### 3. Fetch the OEIS raw data (only if you want to rebuild the database)

The raw data comes from [oeis/oeisdata](https://github.com/oeis/oeisdata) and is **not** part of
this repository (`oeisdata/` is git-ignored). You only ever need its `seq/` tree — the `files/`
tree holds 275,775 supporting-file entries that are useless here — so clone it sparsely:

```bash
git clone --depth 1 --filter=blob:none --sparse \
  https://github.com/oeis/oeisdata.git oeisdata
git -C oeisdata sparse-checkout set seq
```

That downloads ~1.6 GB (398,471 files at `oeisdata/seq/A<bucket>/A<number>.seq`) instead of the
full repository.

### 4. Get the metadata database

`Metadata/oeis.db` (~360 MB) is stored with Git LFS. Either pull it from your clone:

```bash
git lfs install
git lfs pull --include="Metadata/oeis.db"
```

or download it directly without cloning:

```bash
mkdir -p Metadata
curl -L -o Metadata/oeis.db \
  https://huggingface.co/datasets/formalica/lean4oeis/resolve/main/Metadata/oeis.db
```

With the database in place you can skip straight to step 2 below — the raw OEIS data from
step 3 is only needed if you want to regenerate the database yourself.

## 1. Build the metadata database

Parses every `.seq` file into `Metadata/oeis.db` (SQLite, tracked with Git LFS):

```bash
lake build oeis-ingest
lake exe oeis-ingest
```

Add `--limit N` while iterating to only ingest the first N files. See
[AGENTS.md](AGENTS.md#commands) for the full flag list and database schema.

## 2. Generate the Lean skeletons

Reads `Metadata/oeis.db` and writes `OEISLib/<bucket>/<name>/{Defs,Data}.lean` (every declaration
is `sorry` at this stage):

```bash
lake build oeis-gen
lake exe oeis-gen --all
```

Useful variants:

```bash
lake exe oeis-gen --bucket A000               # one bucket
lake exe oeis-gen --seq A000001 --seq A000045 # specific sequences
lake exe oeis-gen --all --force               # overwrite already-generated files
```

`oeis-gen` never overwrites an existing file unless `--force` is passed, so it's safe to rerun
after later stages have replaced `sorry`s with real proofs.

## 3. Build everything

```bash
lake build
```

This compiles every generated sequence file plus the `OEISLib`/bucket aggregators. Expect
`declaration uses 'sorry'` warnings — that's expected until the formula formalization step
(see [AGENTS.md](AGENTS.md#open-items--next-steps)) is implemented.

## 4. Formalize OEIS program blocks with an LLM

Maple (and later Mathematica / PARI / Python) programs attached to OEIS entries are translated
into Lean by a batched LLM pipeline, compiled, and evaluated against the known terms.

```bash
uv venv && uv pip install -e .
PYTHONPATH=Scripts .venv/bin/python -m formalize run --batch-size 5 --batches 1 --retry 2
```

A single OEIS program block usually merges several independent programs. The model delimits
each one with a verbatim start/end anchor pair; everything no item claims is recorded as
unformalized and fed back as a defect to fix. To see the result:

```bash
# every program block of one sequence, colour-coded:
# one colour per formalized program, red for anything unformalized
PYTHONPATH=Scripts .venv/bin/python -m formalize show --seq A000002

# one batch in full: items, spans, lean code, gaps, and the model conversation
PYTHONPATH=Scripts .venv/bin/python -m formalize show --batch-id 9 --history
```

See [FORMALIZE.md](FORMALIZE.md) for the full design, the database tables it writes and all
available commands.

### Disk usage while building

Lake writes a `*.setup.json` per module listing every transitively imported module. With
`import Mathlib.Tactic` these are ~1.8 MB each and account for **93% of `.lake/build`**. They
are inputs that Lake regenerates on demand and are not part of the up-to-date check, so prune
them as you go:

```bash
lake exe oeis-cache stat     # size breakdown of .lake/build by file type
lake exe oeis-cache prune    # delete *.setup.json
```

Building bucket-by-bucket and pruning in between keeps peak disk near ~100 GB instead of ~1.5 TB:

```bash
for b in OEISLib/A*; do
  lake build "OEISLib.$(basename "$b")" && lake exe oeis-cache prune
done
```

## Skip the build: use the prebuilt cache

Rather than compiling everything yourself, restore the artifacts:

```bash
mkdir -p cache
curl -L -o cache/loeis-build.tar.zst \
  https://huggingface.co/datasets/formalica/lean4oeis/resolve/main/cache/loeis-build.tar.zst
curl -L -o cache/manifest.json \
  https://huggingface.co/datasets/formalica/lean4oeis/resolve/main/cache/manifest.json

lake exe oeis-cache get
lake build      # should be a no-op
```

`oeis-cache get` refuses to extract if `lean-toolchain` or `lake-manifest.json` differ from what
the cache was built against; pass `--force` to override. You still need Mathlib's own oleans via
`lake exe cache get`.
