# Copy the rows of a compatible table

Created 2026-11-17. Issue [#415](https://github.com/vihren-dev/belay/issues/415).
Status: open.

A library law for the README rebuild must establish that the INSERT from a
full projection of the source succeeds, the empty target receives the source
values, and the other tables keep their definitions and rows. A rowid alias
copied as a column carries its rowid. A table with an implicit rowid needs a
separate account of the allocated rowids. The law must state which row
orders it preserves when SQLite can scan more than one index.

A catalog check must account for widths, affinities, rowid aliases, keys,
generated columns and CHECK constraints. Each NOT NULL target column needs
the corresponding guarantee in the source. The source can have additional
NOT NULL constraints. The only data-dependent typing premise for the README
is that the source rows fit the target's STRICT types.

There is an open question about the operational premise. The issue's stated
schema conditions allow an AFTER INSERT trigger to write an audit table.
The unchanged-other-tables conclusion would be false for that statement.
The owner has been asked whether the law should require the resolved INSERT
to have no write rules. Column compatibility and the theorem that compatible
source rows satisfy target column obligations apply in either case.

## Acceptance

Check the copy in the README and its existing public success claim. Exercise
a target requiring a nullable source column, a width or affinity mismatch
and a STRICT typing failure. Test the allowed weakening of a NOT NULL
requirement. Check the copied rows and the frame on successful executions,
including the alias values. Use the pinned SQLite oracle for concrete
copy and trigger examples. The trigger case must preserve the observed audit
write. Run the repository's Nix gates on the completed stack.

## Existing code

RebuildCopyFacts and RebuildSucceedsCopy contain the current concrete proof.
InsertFits.copy takes row-level premises about width, storage affinity, NULL,
types and keys. LiteralData.inserted_copy gives the stored rows for an alias
copy. runScriptStep_insertSelect_success exposes the exact updated database
for a single production and a resolved write without rules.
