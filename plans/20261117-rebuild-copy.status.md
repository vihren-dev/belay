# Status of the rebuild copy

Created 2026-11-17. DONE. [Task](20261117-rebuild-copy.task.md).

The script-step law requires a resolved INSERT without write rules. The column-compatibility
check and the row-level proof apply independently of that premise. The README success proof and data effect
tests are the acceptance checks for the assembled law.

CatalogTable.copyCompatible checks affinities, NOT NULL implication, aliases
and target constraints. InsertFits.copy_compatible proves the row operation
for any permutation of source rows with an alias. The concrete README copy
now returns the exact next database, with customers.scanRows in the target.
The proof directory shrank from 470 lines to 381. RebuildCopyChecks exercises
both directions of the NOT NULL condition and the width and affinity checks
through tests/surface_rebuild_test.py.

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
Belay reports this indexed transfer as unsupported.

At revision ba625cf90711 the [Linux checks](https://github.com/vihren-dev/belay/actions/runs/44221060452/job/134522729144)
and the [locked verdict](https://github.com/vihren-dev/belay/actions/runs/44221060249/job/134522724488)
passed for this PR. Both runs include the public script-step theorem and the
README proof. The earlier [verdict report](https://github.com/vihren-dev/belay/actions/runs/44212430809)
matched main on all 7,868 frozen cases.

On 2026-11-18 the owner accepted the rule-free copy law and the existing
transfer scope. The statement law covers the shared-alias copy. The
implicit-rowid lemma describes the ordinary row operation. The pinned SQLite replays in
`tests/surface_rebuild_test.py` check ordinary rowid allocation, an enforced
foreign-key failure and an audit trigger. The separate native and kernel
test in `tests/conformance_insert_queries_test.py` checks that the model
refuses `insert-query-transfer-with-rowid-gap`. It also checks the separate
column-list case, which the model conservatively refuses.
