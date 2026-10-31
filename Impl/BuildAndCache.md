# Build and Cache

## Lean modules

`GenExpr`, `GenExprTests`, `Scripts`, and their shared `OEISLib.Common` dependencies are Lake
libraries in `lakefile.toml`. Their Lean source files use the explicit `module` command. Declarations
are private by default; each library module uses `public section` for its existing cross-module API,
closed before the enclosing namespace ends. `public import` re-exports runtime dependencies, and
`public meta import` re-exports dependencies evaluated by compile-time `#guard` tests. Files whose
definitions are used both ways import the dependency in both modes.

`OEISLib.Common.Residue.membersUpTo` is marked `@[expose]` because the exported theorem
`selectFrom_primesUpTo` relies on its body for definitional equality.

The root module of every `lean_exe` (`oeis-ingest`, `oeis-gen`, `oeis-cache`, `oeis-template`,
`oeis-template-test`) must declare `public def main`. A private `main` is mangled and not emitted as
the program entry point; the binary then links and runs another `main` (a Mathlib dependency's
exporter, which prints `{"meta":{"exporter":...` and fails on the arguments).

## Lake configuration

Common linter options are configured in `lakefile.toml`, not in generated Lean files. The current
settings include `weak.linter.mathlibStandardSet = true`,
`weak.linter.unusedVariables = false`, and `weak.linter.style.longLine = false`. The latter two
accommodate generated skeletons with unused binders and long term lists. The sorry-declaration
warning remains enabled; see the Spec difference below.

## Build cache

`oeis-cache` manages the compiled `.lake/build` archive:

| Command | Behavior |
| --- | --- |
| `prune` | Removes `*.setup.json` and `*.setup.json.hash` files under `.lake/build/ir`; if `ir` does not exist, it reports that there is nothing to prune. |
| `stat` | Recursively reports file counts and byte totals grouped by extension. |
| `put` | Archives `lib/` and, when present, `ir/`, excluding setup files; writes `cache/loeis-build.tar.zst` and `cache/manifest.json` by default. The manifest records the toolchain, Lake manifest and lakefile hashes, archive path, and archive size. |
| `get` | Extracts the archive. If a manifest is present, it checks the toolchain and Lake manifest hash, refusing a mismatch unless `--force` is used. It records the lakefile hash but does not check it during restore. |

The commands accept `--build-dir`, `--archive`, `--manifest`, `--level`, and `--force`; the
compression level defaults to 6. The archived `.olean`, `.ilean`, and `.c` artifacts are retained,
while setup files are excluded because Lake regenerates them.

## Targeted builds

Build the package libraries and their `#guard` tests without building the generated `OEISLib` tree:

```bash
lake build GenExpr GenExprTests Scripts
lake build genexpr-test oeis-ingest oeis-gen oeis-cache oeis-template oeis-template-test
lake exe genexpr-test --engine internal
lake exe oeis-template-test
```

## Differences from Spec.md

| Spec.md says | Implementation does |
| --- | --- |
| The `lakefile.toml` options should include an option that disables the “definition/theorem contains sorry” warning. | `lakefile.toml` does not disable that warning; it disables only the unused-variable and long-line warnings among the requested linter options. |
