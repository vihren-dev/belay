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

## Remaining

- Everything in the task's "Outcome".
