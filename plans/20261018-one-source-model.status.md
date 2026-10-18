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
- 2026-10-18: review of the written-order commit: a NATURAL join after `json_each` would
  match its hidden columns, which SQLite skips; restricted under `function-join`
  (`refactor:` commit, review clean).
- 2026-10-18: duplicate sources resolve. Qualified names resolve over the sources with
  the name (`Scope.resolveQualified`), `x.*` expands every such source, and `*` and `x.*`
  give `ambiguous column name: main.x.c` as SQLite does; a table's source name is the
  declared name. `duplicate-source` leaves the registry. Verdict: the 3 v5 cases
  `e_select-1.4.3.7.1/2/3` now agree; no other case changes.
- 2026-10-18: each scope source keeps its offset (`ScopeSource.offset`, set by
  `Scope.place`); the scope folds that recomputed offsets are gone (outcome 6). Mutant
  anchors moved; `natural_without_common_no_rows` now writes a resolved expression,
  since the merged condition is no longer Syntax. Verdict unchanged.

## Remaining

- The `subquery` kind: the ADR (D5) and amendment 2 disagree on whether SQL can reach
  it, and `tests/conformance_restriction_examples_test.py` refuses a kind no SQL reaches;
  asked the owner.
- Measurement over every corpus, full checks, review, CI time, pull
  requests A and B.
