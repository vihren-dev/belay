# Status of empty rows after table creation

Created 2026-11-19. Open. [Task](20261119-created-table-rows.task.md).

The mixed-script law in Programs/Claims/SchemaSuccess carries a caller's
invariant across successful executions. TablePath follows a table present at
the start. CreateTableStepLaws gives the next database and its single
execution. RebuildSucceedsCopy currently adds an empty-row condition to the
tracked source table. The implementation and acceptance checks are pending.
