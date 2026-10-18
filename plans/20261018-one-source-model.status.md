# Status: one source model (ADR 0013, step 5)

Created 2026-10-18. Status: open.
Task file: [task](20261018-one-source-model.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), D5 and amendment 2.

## Relevant files

- Model: `packages/belay-sqlite/Belay/Sqlite/Resolution/QueryForm.lean` (`Query`, `Join`,
  `EachSource`), `QueryJoins.lean`, `QueryFunctions.lean`, `QueryRun.lean`, `JsonReady.lean`,
  `QueryJoinLaws.lean`.
- Resolution: `Resolution/Sources.lean`, `FunctionSources.lean`, `JoinUsing.lean`,
  `MergedLeft.lean`, `MergedNames.lean`, `Scope.lean`, `Queries.lean`, `QuerySpec.lean`.
- Examples: `Resolution/JoinExamples.lean`, `UsingExamples.lean`, `MergedNameExamples.lean`,
  `RightJoinExamples.lean`, `QueryExamples.lean`, `JsonFaultExamples.lean`.
- Mutants: `conformance/join_mutants.py`, `right_mutants.py`, `using_mutants.py`,
  `merged_mutants.py`, `json_each_mutants.py`, `fromless_mutants.py`.

## Progress

- 2026-10-18: code map done. Only 3 frozen cases are refused by the source restrictions,
  all `duplicate-source` (`FROM x3, x3`). Native checks: `count(*)` over a duplicate is 4,
  and names over it are ambiguous, also `*` (`main.x3.a`); `OUTER LEFT` and `LEFT LEFT` are
  left joins; `LEFT JOIN json_each(t.b)` is correlated. The owner chose the full D5
  (owner decision 6); ADR 0013 amendment 2 records the details.

- 2026-10-18: commit `nzxzowqv` (one source list, one join); its suites pass and its
  verdict equals step 4's. Commit `tkpkwzqz`: join operators parsed once
  (`joinOperator`), and `USING`/`NATURAL` equalities resolved from positions; review clean.
- 2026-10-18: sources resolve in written order (`Resolution/SourceList.lean`): tables and
  `json_each` in any order, `LEFT JOIN json_each`, ON conditions then `json_each`
  arguments after `WHERE`. `table-after-function` is gone; `function-join` covers only
  RIGHT/FULL, NATURAL and USING; `later-table-in-on`, `function-join` and
  `later-source-in-arguments` are *unsupported*. The `join-operator` example is now
  `INNER OUTER JOIN`, which SQLite refuses. Verdict: no case changes.

## Remaining

- Duplicate sources with SQLite's ambiguity rules; the `subquery` kind; source offsets in
  the scope (outcome 6).
- Measurement over every corpus, full checks, review, CI time, pull
  requests A and B.
