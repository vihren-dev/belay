# Status of empty rows after table creation

Created 2026-11-19. DONE. [Task](20261119-created-table-rows.task.md).

At the starting revision the mixed-script law in Programs/Claims/SchemaSuccess carried a caller's
invariant across successful executions. TablePath follows a table present at
the start. CreateTableStepLaws gives the next database and its single
execution. At the starting revision, RebuildSucceedsCopy tracked the source table
and separately required the new destination at position 2 to have no rows. The step theorem in CreatedTables gives the resolved shape and empty rows of a
new table. A mixed-script law carries that fact across preserving statements
and accounts for shifted positions after DROP. The rebuild proof uses it at
the copy step. SchemaSuccessChecks covers preservation and a no-op creation.
The focused test is tests/surface_rebuild_test.py.

Review clarified the prefix and successful-execution premises, the empty
target required by the copy example and the subject of the regression.

The second review found no issues. The [full Nix suite](https://github.com/vihren-dev/belay/actions/runs/44579051692/job/135754357382) and the [verdict](https://github.com/vihren-dev/belay/actions/runs/44579051592/job/135754357383) passed on the PR source tree.

Before the stack was published, `just test-nix` passed all 99 selected
tests on the combined changes and `just test-scheduled-checks` passed.
