# Status of SQL reconstruction of computed schemas

Created 2026-11-19. Open. [Task](20261119-catalog-replay-sql.task.md).

ReplayDatabaseSql now emits all four catalog entry kinds. ReplayTableSql and
ReplayResolvedExpr reconstruct table constraints and index expressions.
ReplayViewSql, ReplaySyntaxExpr and ReplayTriggerSql print stored query and
trigger syntax. The checker validates the emitted construction against both
the catalog and the stored rows. The fixtures in surface_check_run_schemas_test.py,
surface_views_test.py and surface_search_test.py exercise the public command,
native SQL, nested views and a sparse rowid candidate that fails exact replay.
The independent review and slice checks are pending.

Review added a public diagnostic case for an unprintable object name, module
descriptions, and exhaustive scalar function collation selection.
