# Status: invariants in types, API lemmas and position-free effects (ADR 0013, step 7)

Created 2026-10-18. Status: open.
Task file: [task](20261018-types-and-api.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), D8 and D7.

## Relevant files

- Errors: `packages/belay-sqlite/Belay/Sqlite/Resolution/Resolved.lean` (`PrepareError`),
  `Values.lean` (`ValueIssue`), `ErrorKinds.lean`, `IssueLemmas.lean`, `OperandIssues.lean`,
  `ReturningIssues.lean`, `InsertCellRules.lean`, `UpdateRules.lean`, `UpsertRules.lean`,
  `PrepareRules.lean`, `DefinitionRules.lean`, `PrepareSpec.lean`, `Messages.lean`,
  `Codec/Resolution.lean`, `SchemaScript.lean`.
- Reals: `Arithmetic.lean` (`realValue`, `isNullCell`), `Comparison.lean` (`isNull`),
  `StoreValue.lean`, `Json/SqlValue.lean`, `Model.lean` (`Table.Valid`).
- Effects: `StatementStep.lean`, `Execution.lean`, `UpsertRun.lean`, `Laws.lean`,
  `StepCatalog.lean`, `SqlProofs.lean`.
- Users of unfolding: `packages/sqlite-verifier/SqliteVerifier/*Demonstration.lean`,
  `examples/*/Proofs.lean`, `examples/atuin/AtuinFacts.lean`.

## Progress

- 2026-10-18: code map (see the task file's key points). 36 `PrepareError` constructors,
  5 of which name a catalog object; only `noSuchTable` of a `FROM` table reaches
  `ValueIssue` among those. The `_issue` lemma family has no users outside
  `Resolution/`.
- 2026-10-18: `Resolved.Statement.kind` (outcome 7, in `StatementCatalog.lean`):
  `isControl`, `SchemaOnly` and `NoWrites` classify through it, and `nonControl` is gone.
  `prepareError?` stays a match because it returns the error.
- 2026-10-18: owner decision 8 (ADR 0013): every computed REAL is built through
  `realValue` (literals, the most negative integer default, JSON payloads) or keeps the
  bits of a REAL (`integerAffinity`, `realRead`, documented); `Value.isNull` (in
  `Declarations.lean`) replaces `isNull` by rank and `isNullCell`; `Table.Valid` does not
  change, because `Float` is opaque to proofs. The task's outcome 2 is amended by the
  decision. Verdict counts unchanged (the step 5 reports were collected by the GC;
  `build/agent-logs/report-s7b.json` keeps this one for later diffs).

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
