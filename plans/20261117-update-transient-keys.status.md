# Status of multi-row UPDATE and transient unique keys

Created 2026-11-17. Open. [Task](20261117-update-transient-keys.task.md).

The UPDATE branch in Schema/Dispatch/StatementStep.lean checks the final
table. Schema/Writes/RowUpdate.lean computes the updated rows in their
original positions. Schema/Rows/LiteralData.lean defines keyEqual.
Schema/Writes/DerivedColumnUpdateRun.lean proves the backfill is ready.
The existing diagnostic regression is in tests/surface_guide_test.py.

The acceptance conditions are recorded. Implementation and checks are pending.

The plain UPDATE ready check compares the old and new keys of distinct rows.
The backfill proof uses the fact that its keys read only the original cells.
The test in tests/surface_update_transient_keys_test.py uses SQLite as the
oracle for the two conflicts and a successful write. The companion check in
tests/surface_guide_test.py covers final-table constraint diagnostics.
Both findings on the task file are resolved. The Nix checks are pending.
