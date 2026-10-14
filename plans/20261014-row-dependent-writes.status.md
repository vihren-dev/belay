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

## Remaining

- Everything in the task's "Outcome".
