# Status of empty rows after table creation

Created 2026-11-19. Open. [Task](20261119-created-table-rows.task.md).

At the starting revision the mixed-script law in Programs/Claims/SchemaSuccess carried a caller's
invariant across successful executions. TablePath follows a table present at
the start. CreateTableStepLaws gives the next database and its single
execution. At the starting revision, RebuildSucceedsCopy tracked the source table
and separately required the new destination at position 2 to have no rows. The step theorem in CreatedTables gives the resolved shape and empty rows of a
new table. A mixed-script law carries that fact across preserving statements
and accounts for shifted positions after DROP. The rebuild proof uses it at
the copy step. SchemaSuccessChecks covers preservation and a no-op creation.
The focused test is tests/surface_rebuild_test.py. The slice review and Nix
checks are pending.
