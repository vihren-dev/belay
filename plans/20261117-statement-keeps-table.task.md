# Follow a table through a resolved script

Created 2026-11-17. Issue [#412](https://github.com/vihren-dev/belay/issues/412).
Status: DONE.

Given a resolved statement and a table position, a computable check gives
the position of the same table after the step or reports that it cannot
establish preservation. On every continuing execution with a successful
output, a reported position contains the original definition and rows.
The claim allows changes to other tables, counters and settings. It covers
successful alternatives of an INSERT from a query.

The check must follow a surviving table through a plain DROP. For a catalog
rewrite it may consult the previous catalog to compare the old and new
definitions at the position. It must refuse a rewrite that changes the
protected definition, a DROP that can cascade, and a write that can use
trigger rules. A rollback can restore different rows.

The checks for a complete script compose along its resolved schema path.
The README rebuild proof must use the computed positions for sessions and
for the old customers before the copy. One check must replace the
statement-by-statement proofs that locate the surviving tables.

## Acceptance

The kernel checks the law including INSERT from SELECT alternatives.
Exercise the complete rebuild, a drop that shifts sessions, a write to the
protected table, a rewrite that changes its foreign key definition and the
wrong rebuild with enforcement enabled. The README preservation and success
claims keep their hypotheses and conclusions. Run the existing rebuild
tests and the relevant repository checks.

## Existing laws

PlainWriteFrame and ReadOnlyFrame cover queries and plain writes.
CreateTableStepLaws, DropTableStepLaws and ControlStepFrames cover the
remaining rebuild statements. TableByName relates SQL names to positions.
ADRs 0025 and 0026 keep proof rules in the library.

The script-level check uses the schema path from #411 for
the resolved statement and catalog at each prefix.
