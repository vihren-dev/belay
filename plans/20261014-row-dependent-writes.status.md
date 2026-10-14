# Status: row-dependent writes (slice 3b)

Created 2026-10-14. Status: DONE.
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
- 2026-10-14: `WritePreservation.lean`: `Table.Valid.updated` (no premise),
  `Table.Valid.inserted` (under the conjuncts of `insertReady`), `checkedWrite_conforms`,
  and the step theorems `literalStep_insert_conforms` and `literalStep_update_conforms`.
  Schema statements keep `Conforms` by the existing `Conforms.appendAt` and
  `Conforms.set`. The module count test (`just test-nix`) was not run after the UPDATE
  commit and failed there (57 modules); it now expects 58. `just test-nix` runs with
  `test-full` from now on.
- 2026-10-14: evidence. `conformance/authored_row_writes.py`: 24 cases (11 store-time,
  13 UPDATE, including the slice 3a filter boundary case, which now agrees), all agree
  with kernel proofs (about 12 s). `conformance/row_write_evidence.py` writes corpus 11.
  `conformance/row_write_mutants.py`: the 9 mutants of the amendment's list, all killed
  in the mutants suite. Storing constants at resolution matters only for the key-domain
  check (the execution stores again), so its mutant targets `SET k = '7'`.
- 2026-10-14: CI time of the pull request suites that this work changes (forced rebuild,
  same machine, main then branch): `tests.harness` 21 s and 21 s, `tests.mutants` 110 s
  and 125 s (9 new mutants), `tests.model` 158 s and 169 s (24 new cases with kernel
  proofs), `tests.frozen` 180 s and 179 s. The suites run in parallel; the longest of
  these, `tests.frozen`, does not change. Pull request A opened.
- 2026-10-14: CI of #115 failed: the single mutant test (54 mutants) passed the 300 s
  pytest limit on the hosted runner. Split into a query and number test (79 s locally)
  and a write test (27 s); together 107 s locally, less than the 125 s before.
- 2026-10-14: the second CI run failed: the frozen v5 progress test passed 300 s.
  On main's Linux runner it already took 260 s, and the query mutant test 266 s; the
  9 new mutants added contention. Profiling (owner's request) found:
  - 37 of the 61 s of the v5 test in 1,061 one-case classifier runs of the query
    diagnostic: now batched (256 cases per run);
  - 7 of the 11 s of corpus `load` in the cyclic garbage collector, which walked the
    10.9 million decoded objects on each full collection: load and replay now run with
    the collector paused (`conformance/replay_support.py`). The test takes 24 s alone.
  - every mutant rebuilds the modules after its file, and Resolution.Syntax and the
    modules after it depended on Comparison and Arithmetic only for the operator types:
    the types moved to `Operators.lean`, and Values dropped an unused import. An
    Arithmetic mutant rebuilds 20 modules instead of 29; the query and number
    measurement takes 59 s instead of 77 s alone.
  Under the full parallel test load locally: query mutants 110 s → 80 s, v5 test → 47 s.

- 2026-10-14: #115 merged. Pull request B: corpus 10 (2 obligation boundary cases,
  DISAGREE and HARNESS_ERROR forbidden) and corpus 11 (24 row-dependent write cases,
  all in `mustAgree`) are frozen and claimed; the 45 cases of v1 to v5 that agree since
  #115 are added to `mustAgree` (v1 +2, v2 +2, v3 +13, v4 +10, v5 +18). `just
  judge-lock` regenerated the lock: the judge entry changes and the two corpora are
  added. Slice 3b is done.

## Remaining

- None. Next: slice 3c (DELETE).
