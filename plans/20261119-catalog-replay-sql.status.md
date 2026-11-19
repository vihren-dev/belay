# Status of SQL reconstruction of computed schemas

Created 2026-11-19. Open. [Task](20261119-catalog-replay-sql.task.md).

ReplayDatabaseSql now emits all four catalog entry kinds. ReplayTableSql and
ReplayResolvedExpr reconstruct table constraints and index expressions.
ReplayViewSql, ReplaySyntaxExpr and ReplayTriggerSql print stored query and
trigger syntax. The checker validates the emitted construction against both
the catalog and the stored rows. The fixtures in surface_check_run_schemas_test.py,
surface_views_test.py and surface_search_test.py exercise the public command,
native SQL, nested views and a sparse rowid candidate that fails exact replay.
The slice covers the public command and exact replay on model and native SQLite.

Review added a public diagnostic case for an unprintable object name, module
descriptions, and exhaustive scalar function collation selection.

The public command test now describes the unknown answer for an unprintable name.

The code and documentation review found no issues. The Nix verdict passed.

The Nix surface layer check on pull request 463 found two imports of model
implementation modules. The printers use the model's public statement resolution
library for argument lists and the SQL names of foreign key actions. The regression
test is tests/surface_layers_test.py.
