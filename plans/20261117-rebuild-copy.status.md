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

The model package lists the scan-order, row compatibility and query production
modules. Its core import closure is checked by tests/test_model_package.py.

The pinned replay test now includes a copy that fires an audit trigger and a
copy that fails on an enforced foreign key. These cases exercise the write
rules that the general copy law must account for.

The rule-free run law now covers every scan of an admitted source with a
shared rowid alias. The model writes the table scan, and each alternative
writes a permutation that preserves the rowids. The README uses the law
for its INSERT. A row-level lemma also describes the values and newly
allocated rowids when an empty target has no alias or generated columns.
The six README proof files now total 362 lines. RebuildCopyChecks exercises
the default and partial-index writes; the native replay checks the distinct
source and target rowids of an implicit-rowid copy.

runScriptStep_copyOf lifts compatible alias copies without write rules to the
script API. It proves success and the database contents for the main execution
and every alternative. The README applies this law without checking a clock,
a counter, or a unique scan order. Its proof files now total 354 lines.

The implicit-rowid guarantee also depends on SQLite's transfer optimization.
In SQLite 3.51.0, start with s(v INTEGER), an index on v, values 10, 20, 30,
and delete 10. Create the empty t(v INTEGER) with a matching index and run
INSERT INTO t SELECT * FROM s. Native SQLite keeps the source rowids 2 and 3.
Belay reports the transfer as unmodeled. The owner decision is whether to
state the existing transfer support condition or to expand the model.
