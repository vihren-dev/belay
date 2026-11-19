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
- On an idle machine the fixture elaborates about 8 s longer with the check than without it. The time
  limit of the check was not measured apart from that. The fixture sets `sql.checkTimeLimit` to 60 s,
  because a loaded machine makes the check slower (issue #426).
- `#sql_check` answers `unknown` for `splitByAgeFixed preserves allCustomers on shop` and for
  `splitByAgeFixed succeeds on shop`.
- Result order: an unordered read gives `Output.rows` of its rows in the normal form, a sort by
  `Resolved.compareRows`. `Output.oneOf` is only for a read whose rows SQLite can give differently,
  for example `LIMIT` without `ORDER BY`. So `preserves` compares the read before and after as a
  multiset of rows, and the claim needs no `ORDER BY`.

## Stop: the proof of the fixed migration

The request for this task sets a stop condition that the workspace rules do not have: stop and
report when the proof needs more than about 200 lines of new general library code. The proof of
`splitByAgeFixed preserves allCustomers on shop` stops at that condition and is pending. Not proved: that claim and `splitByAgeFixed succeeds on shop`. The proof needs
these general laws, which the packages do not have:

- The normal form of two permutations of the same rows is the same list (`Resolved.normalForm`).
  This needs that `compareNormal` is a total order with equality as its equal case, and that two
  sorted permutations are equal. Estimate: 100 to 150 lines.
- A step law for `CREATE VIEW`. Estimate: 30 to 40 lines.
- The output of a read through a view over `UNION ALL`. The resolved read is a query over
  `Source.subquery 0 3`; subquery 0 is a compound (`first := 1`, `rest := [(unionAll, 2)]`), and
  subqueries 1 and 2 scan `minors` and `adults`. `resolvedStepOutput_calm_unordered` needs
  `query.compound = none` and no subqueries, so the law must build `Connection.SelectReady` with
  subqueries: the source of the subquery (`Query.subqueryRun`), its certain fault
  (`Query.compoundRun`, `Compound.ending_done`, `keepsCertain` of `UNION ALL`), the certainty of
  its whole rows (`run.sourceCertain = true`, which `QuerySource.join` checks; it follows from the
  zero offset and the absent limit of the view), and its rows (`Compound.rows_unionAll`). Estimate: 150 lines or more; not measured.
- A form of `ReadCertificate.preservesAt` without the certificate: when the read resolves with
  `fromQuery = false` before and after the migration on every branch
  (`sendStatements_single_observations` needs both), equal step outputs on every branch give
  `PreservesAt`. A draft of about 40 lines moved the proof body; it is not in a commit.

Together the general laws are more than 200 lines. The example proof would add about 500 to
1000 lines (an invariant over eight statements, as in `examples/table-rebuild/Proof`).

## Progress

- 2026-11-19: task and status files; fixture `SplitByAge` with the check, the counterexample `found`,
  two `decide +kernel` theorems about it (`split_loses_found_customer`,
  `fixed_keeps_found_customer`) and `split_loses_null_age` (`sql_refute`); its test. Checks: the
  test file, local run (not evidence); `just test-full` not run.
