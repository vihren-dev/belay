# Status: row-dependent writes (slice 3b)

Created 2026-10-14. Status: IN PROGRESS.
Task: [task](20261014-row-dependent-writes.task.md).
Specification: [ADR 0012, Amendment 1](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/LiteralData.lean`,
`SqlExecution.lean`, `Model.lean`, `QueryEval.lean`, `Arithmetic.lean`,
`Resolution/Resolved.lean`, `Resolution/Writes.lean`, `Resolution/Values.lean`,
`LiteralPreservation.lean`, `packages/verifier-conformance/VerifierConformance/Outputs.lean`,
`belay/sqlite/syntax_writes.py`, `conformance/authored_writes.py`,
`conformance/write_mutants.py`, `conformance/obligation_mutants.py`,
`conformance/authored_obligations.py`, `conformance/restriction_examples.py`.

## Progress

- 2026-10-14: task and status files created. The amendment (#111) is ACCEPTED, with
  its "Testing" text changed to the evidence form of the restriction registry task:
  a conjunct has a mutant and a boundary case, or names what covers it.
- 2026-10-14: `storeValue` (`StoreValue.lean`), a port of `applyAffinity`,
  `applyNumericAffinity`, `alsoAnInt` and `sqlite3VdbeIntegerAffinity` of 3.51.0, with
  the read of a REAL column. A REAL in a REAL column keeps its bits except that -0.0
  becomes +0.0 (`positiveZero`): this closed form of "write the whole REAL as an
  integer, read it back as a double" makes idempotence provable without float lemmas.
  `StoreValueLaws.lean` proves idempotence and that TEXT affinity stores no number;
  `StoreValueExamples.lean` checks the amendment's store list against values from
  native 3.51.0.
- 2026-10-14: stored values. Resolution stores INSERT values, defaults and SET values
  with `storeValue`; `storedValue`, `lossless` and `nonnumericText` are removed, and
  with them the restrictions `real-value` and `affinity-conversion` (registry 33 ids).
  `insertReady` and `updateReady` require `storedForm`. `Table.Valid`, and so
  `Conforms`, requires `Row.Stored`; `appendColumns` and `insertRow` keep it. The
  verdict on main versus this commit: AGREE v1 11→13, v2 17→19, v3 34→46, v4 16→26,
  v5 217→232; no DISAGREE.
- 2026-10-14: the refactor commit 4d71d36c moved `Table.Valid.appendColumns` to
  `SchemaExtension` without rebuilding the runtime, so `SqliteVerifier.Demonstration`
  did not build at that commit; the next commit adds the import.
- 2026-10-14: row-dependent UPDATE. `Resolved.Statement.update` holds expressions and an
  optional condition. `Resolution/Updates.lean` resolves each assignment in SQLite's
  order (expression, then column name; the earlier code resolved all values first, so
  `SET missing = 1, b = other` reported the wrong column), folds constant values to
  stored literals, refuses a row-dependent value for a key column (`row-dependent-key`)
  and resolves the filter as a SELECT condition. `RowUpdate.lean` evaluates the filter
  and the values on the old row and stores each value. `updateReady` keeps
  `tableReady`, a column at each assigned position and the key check after the
  update. Restrictions `column-in-value`, `literal-comparison`, `non-integer-filter`
  and `filter-form` leave the registry (30 ids). `Row.Stored` is decidable, so the
  Atuin example proves stored form by `decide`. Verdict: AGREE v3 46→47, v5 232→235; no
  DISAGREE. The authored legacy catalog: 20 agree (was 10), 23 out of scope.
- 2026-10-14: `tableReady` in `updateReady` re-examined: with row-dependent values only
  in non-key columns, the key check after the update still covers every key cell that
  the update does not change, so `COVERED_ELSEWHERE["update-table-ready"]` stays.
- 2026-10-14: two review rounds in a row had a "must" finding (8aff03b5: a catch-all
  pattern; 351f3415: the fix used aggregate constructors that do not exist and was
  committed although the build failed, because a pipeline hid the exit code). Both are
  fixed (e356f084, review clean). Stopped to report to the owner, as the review rule
  requires. Builds are now checked by their exit code before a commit.

## Remaining

- Preservation of `Conforms` by every statement (insert, update, schema statements).
- Authored coverage cases of the amendment's "Testing" list (store-time list and UPDATE
  list, including the old filter boundary case), with kernel proofs, a corpus writer.
- Mutants of the amendment's list.
- CI timing, pull request A, and pull request B (judge: claim the coverage corpus and
  corpus 10).
