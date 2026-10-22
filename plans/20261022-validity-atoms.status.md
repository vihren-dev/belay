# Status: the facts of a valid database (ADR 0022, slice 1)

Created 2026-10-22. Status: OPEN.
Task: [task file](20261022-validity-atoms.task.md).
Specification: [ADR 0022](../docs/adr-0022-database-validity.md), D1, D2 and D4.

## Relevant files

- `packages/belay-sqlite-model/Belay/Sqlite/Model/Database.lean` (today's invariant),
  `LiteralData.lean` (the constraint checks), `ForeignKeyMatch.lean`,
  `Resolution/Catalog.lean` (`Catalog.uniqueKeys`), `Model.lean` (the root).
- The laws over `Conforms`: `ModelLaws.lean`, `SchemaExtensionLaws.lean`, `DatabaseWriteLaws.lean`,
  `StoreValueLaws.lean`, `LiteralPreservationLaws.lean`.
- Tests: `tests/shared_table_shape_test.py`, `tests/test_model_package.py`,
  `tests/test_model_ownership.py`.

## Progress log

- 2026-10-22: the task file.
