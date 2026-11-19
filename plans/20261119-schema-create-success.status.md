# Status of schema-only success for catalog creation

Created 2026-11-19. Open. [Task](20261119-schema-create-success.task.md).

At the starting revision, `Programs/Scripts/SchemaSuccess.lean` rejects
views, triggers and all indexes. The step for CREATE INDEX can return a
constraint violation only when the index is unique. The corrected script
in `tests/surface/Schema/Tests/SplitByAge.lean` has two copy steps at
positions 3 and 4, followed by DROP TABLE, CREATE VIEW and COMMIT.

The implementation depends on the resolver certificate from #443. The
first review clarified that dependency and the DROP COLUMN acceptance check.
The implementation and acceptance checks are pending.

CreateSchemaSuccess proves continuing steps for the catalog creations and
DROP COLUMN. The schema success check accepts non-unique indexes and leaves
unique indexes to the caller. SchemaSuccessChecks exercises the public law.
SplitByAge checks that precisely its two data-copy steps need row proofs.
The focused tests are tests/surface_rebuild_test.py and
tests/surface_split_by_age_test.py. The slice review and checks are pending.
