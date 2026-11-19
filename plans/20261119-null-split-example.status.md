# Status: an example of data loss that depends on row values (split by age)

Created 2026-11-19. Task: `20261119-null-split-example.task.md`.
Status: in progress.

## References

- Fixture: `tests/surface/Schema/Tests/SplitByAge.lean`; test: `tests/surface_split_by_age_test.py`.
- Pattern of a hand proof of a rebuild: `examples/table-rebuild/Proof/` (`RebuildKeeps.lean`,
  `RebuildKeepsInvariant.lean`, `RebuildSucceedsCopy.lean`).
- Preservation from a certificate: `ReadCertificate.preservesAt` in
  `packages/belay/Belay/Sqlite/Programs/Reasoning/ReadCertificatePreservation.lean`.
- Branches of a sent script: `sendStatements_branch_invariant` in
  `packages/belay/Belay/Sqlite/Programs/Claims/SendStatementsInvariant.lean`.
- INSERT from a query: `runScriptStep_insertSelect_success`
  (`packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/InsertSelectStepLaws.lean`).
- Normal form of unordered rows: `Resolved.normalForm`
  (`packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Execution/PossibleResults.lean`).

## Findings

- The model accepts every statement of the migration: `CREATE VIEW` with `UNION ALL` after
  `DROP TABLE` inside a transaction, and `INSERT … SELECT … WHERE`.
- `#sql_check splitByAge preserves allCustomers on shop` answers `false` with one customer
  `(1, '', NULL)`. Every statement of the migration gives `done 0`, and the read after it gives no row.
- On an idle machine the fixture elaborates about 8 s longer with the check than without it, near the
  default limit of 10 s. The fixture sets `sql.checkTimeLimit` to 60 s (issue #426).
- `#sql_check` answers `unknown` for `splitByAgeFixed preserves allCustomers on shop` and for
  `splitByAgeFixed succeeds on shop`.
- Result order: an unordered read gives `Output.rows` of its rows in the normal form, a sort by
  `Resolved.compareRows`. `Output.oneOf` is only for a read whose rows SQLite can give differently,
  for example `LIMIT` without `ORDER BY`. So `preserves` compares the read before and after as a
  multiset of rows, and the claim needs no `ORDER BY`.

## Progress

- 2026-11-19: task and status files; fixture `SplitByAge` with the check, the counterexample `found`,
  two `decide +kernel` facts about it and `split_loses_null_age` (`sql_refute`); its test. Checks: the
  test file, local run (not evidence); `just test-full` not run.
