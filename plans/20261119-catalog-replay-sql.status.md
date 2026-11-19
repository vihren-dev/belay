# Status of SQL reconstruction of computed schemas

Created 2026-11-19. Open. [Task](20261119-catalog-replay-sql.task.md).

ReplayDatabaseSql currently supports simple tables. Tests of the public
command in tests/surface_check_run_schemas_test.py cover two sources of
construction text and an unknown result for a database with no text.
The printer and its acceptance checks are pending.
