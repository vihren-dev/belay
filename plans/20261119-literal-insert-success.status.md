# Status of success of a literal INSERT

Created 2026-11-19. Open. [Task](20261119-literal-insert-success.task.md).

The statement and step parts of the issue can proceed independently of
the validity bridge. The proposed old-table freshness premise admits two
new equal rowid aliases on an empty table. Owner clarification is pending.

PlainInsertSuccess gives the single ready statement effect, updated rows and
change count. PlainInsertStep gives the continued script step, done output
and updated counters. PlainInsertStepCases applies the step law to two
literal rows and checks a conflicting batch on an empty table. The fixture
runs through tests/surface_schema_script_test.py.
