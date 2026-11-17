# Status of the rebuild copy

Created 2026-11-17. Open. [Task](20261117-rebuild-copy.task.md).

Issue #415 needs a premise for statement side effects. The column-compatibility
check and proof that a valid source meets the target's column obligations
can be developed independently. The README success proof and data effect
tests are the acceptance checks for the assembled law.

CatalogTable.copyCompatible checks affinities, NOT NULL implication, aliases
and target constraints. InsertFits.copy_compatible proves the row operation
for any permutation of source rows with an alias. The concrete README copy
now returns the exact next database, with customers.scanRows in the target.
The proof directory shrank from 470 lines to 381. RebuildCopyChecks exercises
both directions of the NOT NULL condition and the width and affinity checks
through tests/surface_rebuild_test.py. The assembled statement law and Nix
checks are pending.

Table.accessOrders_perm now accounts for indexed scans, including partial
indexes. Resolved.Query.productions_copyOf gives the source values in each
scan order. The README uses this law, and RebuildCopyChecks exercises a table
whose partial index gives a different order. The proof files contain 377 lines.

The public scan laws describe the catalog, source position, rowid and streaming premises.
