# Status: switch the verifier to Lean resolution, step 1b of ADR 0008

Created 2026-10-12. Status: IN PROGRESS.
Task: [task](20261012-resolution-switch.task.md).
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md).
Previous step: [step 1a status](20261010-syntax-resolution-core.status.md).

Relevant files: `belay/sqlite/`, `migration_check/`,
`packages/belay-sqlite/Belay/Sqlite/`, `SqliteVerifier/`, `GateCore.lean`,
`ProofChecker.lean`, `BundleChecker.lean`, `VerifierConformance/`,
`examples/`, `tests/`.

## Findings

- Survey, 2026-10-12, on `main` `5feb549e`: about 4,000 lines of Lean outside
  `Resolution/` use the old model, in the core package, `SqliteVerifier/`, the
  gate, the harness and the examples (784 lines). About 115 files mention
  `Schema`.
- The `.olean` gate trusts the compiled `SqlInputs` from the Python emitter.
  The bundle checker builds `nextSchema`, `script` and `profile` from the
  structural record and trusts the record's `nextSchema`.

## Progress

- 2026-10-12: task and status files created in the jj workspace `adr8-step1`,
  from `main` `5feb549e`.

- 2026-10-12: baseline build times on `main` `5feb549e`, forced rebuild with
  `nix-build --check` in the sandbox, no other load: `modelPackage` 14 s,
  `leanRuntime` 15 s, `conformanceRuntime` 19 s, `publicDocumentation` 5 s,
  development test suites 146 s (all suites rebuilt in parallel, with
  `--keep-going`, because test logs are not bit-for-bit reproducible).
- 2026-10-12: commit `0ff6b34c`: `Resolved.createTable` and `createIndex`
  carry their catalog position; `Resolved.insert` and `update` carry the
  table's unique keys (`Catalog.uniqueKeys`: primary key, UNIQUE constraints,
  unique indexes). Review `20261012T104153Z-0ff6b34c`: no findings.
- 2026-10-12: commit `e77423a6`: `resolveRequest` (schema in description mode, then migration in
  execution mode; a schema holds only CREATE TABLE and CREATE INDEX),
  `PrepareError.message`, the codec for syntax, catalogs and resolved
  statements, the version 2 `RequestRecord`, and the Lean source of the
  generated modules (`leanTerm`, derived `Repr`). A build-time check
  elaborates the printed terms of a sample and compares them with the values.
  Review `20261012T104800Z-e77423a6`: one must finding (R5, a catch-all match
  in `firstPrepareError`) and four should findings (R1 version literal, R6
  application words in model docstrings, R11 only single terms checked). All
  fixed in the next refactor: the names are now `resolveSchemaAndScript`,
  `ResolvedScript`, `ScriptIssue` and `ScriptRecord` in module
  `Resolution/SchemaScript`, `scriptRecordVersion` names the version, and the
  build-time check elaborates both complete generated modules.

## Remaining

- All outcome items of the task.
