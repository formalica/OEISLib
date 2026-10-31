should contain impl details and parts of implementation which contradict with Spec

# Documents

| Document | Describes |
| --- | --- |
| [Database.md](Database.md) | `Metadata/oeis.db`: tables, columns, row counts |
| [Templates.md](Templates.md) | `oeis-template`: runner, interface, the five templates (family and scan), how to add one |
| [BuildAndCache.md](BuildAndCache.md) | Spec.md section `Build and cache` (empty) |
| [Formalization.md](Formalization.md) | Spec.md section `Formalization` (empty) |
| [GenExprParser.md](GenExprParser.md) | Spec.md section `GenExprParser` (empty) |
| [OEISParser.md](OEISParser.md) | Spec.md section `OEISParser` (empty) |
| [Generator.md](Generator.md) | Spec.md section `Generator — lake exe oeis-gen` (empty) |
| [AgentAutoformalizationPipeline.md](AgentAutoformalizationPipeline.md) | Spec.md section `LLM-agent autoformalization pipeline` (empty) |
| [OEISLib.md](OEISLib.md) | Spec.md section `OEISLib — per-sequence file shape` (empty) |
| [Verification.md](Verification.md) | Spec.md section `Verification` (empty) |

# Conventions

- Keep these documents current after every change (RULE 0 in [AGENTS.md](../AGENTS.md)).
- Each document describes the implementation first and ends with `## Differences from Spec.md`.
- That section lists only what [Spec.md](../Spec.md) states and the implementation contradicts, one row per contradiction, sorted by importance with the most important row first. Details Spec.md does not cover, and things that match it, belong in the implementation sections.
