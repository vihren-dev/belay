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
- 2026-10-22: the atoms and both bundles. `DatabaseFacts.lean` has `Database.EveryTable`,
  the row atoms (moved from `Database.lean`), `Table.Admitted`, `Database.Admitted` and
  `Conforms` over it; `DatabaseFactChecks.lean` decides them. `DatabaseConstraints.lean`
  has `NotNull`, `TypesFit`, `ChecksHold`, `KeysUnique` and `Database.Valid`;
  `DatabaseConstraintChecks.lean` decides them with the checks that
  `LiteralData.constraints` now combines (`notNullRows`, `typedRows`, `checkedRows`,
  `keysUnique`). `ForeignKeysHold.lean` states the foreign keys with `parentFound`.
  `ValidityExamples.lean` has the cases of the task file. The laws use `Admitted`
  (`Table.Admitted.appendColumns`, `Conforms.setRows`). The CHECK mutant
  `check_skipped` now removes `checkedRows` from `constraints`. `just test-source`:
  450 passed. The predictions are byte-identical to the baseline.
- 2026-10-22: review fixes: proof sketches for the library lemmas of `DatabaseFacts`,
  `DatabaseFactChecks` and `DatabaseConstraintChecks`, and failing examples for the catalog
  support (`lowered`) and the row-list shape.
