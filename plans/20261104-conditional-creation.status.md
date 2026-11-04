# Conditional table and index creation: task status

Date: 2026-11-04. Status: OPEN.
Audience: the implementation team.
Task: [Conditional table and index creation](20261104-conditional-creation.task.md).
Specification: [ADR 0030](../docs/adr-0030-conditional-creation-and-expression-grouping.md).
Source baseline: main `528ea92`.

Relevant files: `packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Syntax.lean`,
`Resolution/Definitions.lean`, `Resolution/ViewDefinitions.lean`, `Resolution/StatementArms.lean`,
`packages/belay-sqlite-text/Belay/Sqlite/Translation/Tables.lean`, `Translation/Schema.lean`,
the theorems that the ADR's context lists, `tests/syntax_mapping_test.py`,
`conformance/requirement_cases.py`, `docs/semantic-subset.md`.

## Progress

- 2026-11-04: task specified; ADR 0030 accepted by the owner.
