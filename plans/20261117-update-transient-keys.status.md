# Status of multi-row UPDATE and transient unique keys

Created 2026-11-17. Open. [Task](20261117-update-transient-keys.task.md).

The UPDATE branch in Schema/Dispatch/StatementStep.lean checks the final
table. Schema/Writes/RowUpdate.lean computes the updated rows in their
original positions. Schema/Rows/LiteralData.lean defines keyEqual.
Schema/Writes/DerivedColumnUpdateRun.lean proves the backfill is ready.
The existing diagnostic regression is in tests/surface_guide_test.py.

The acceptance conditions are recorded. Implementation and checks are pending.
