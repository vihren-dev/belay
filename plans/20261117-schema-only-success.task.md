# Schema-only success for resolved statements

Created 2026-11-17. Issue [#414](https://github.com/vihren-dev/belay/issues/414).
Status: open.

A decidable check on a resolved statement and its input resolution state
must certify a continuing step, a successful output, and no alternative
executions from any valid connection with that state. It covers settings,
BEGIN in an idle connection, COMMIT in a transaction with foreign keys off,
CREATE TABLE at the end of the catalog, plain DROP, compatible catalog
rewrites, and a foreign-key check for which the catalog bounds the number
of tables that can contribute rows. A failing check makes no claim.
Deferred foreign keys prevent a schema-only COMMIT guarantee with
enforcement enabled.

A script whose statements all pass on their resolved prefixes must satisfy
Succeeds on the specified schema. For a mixed script, callers may carry an
invariant and supply success for the statements the check cannot certify.
Preservation of a caller's invariant is a separate obligation. The README
rebuild must use the schema proof for its control and DDL statements and
supply its row-dependent copy proof. Its accepted input rows and its public
success claim must stay the same.

## Acceptance

Compile the public statements and the README proof. Check a complete
schema-only transaction and the rebuild with its copy. Reject a nested
BEGIN, an idle COMMIT and a COMMIT with enforcement enabled. Cover a
foreign-key check on a catalog with one potential source of result rows
and one with multiple sources. Run the repository checks and measure the
rebuild success proof after the change.

## Existing facts

StepContinuesOk and ForeignKeyCheckContinues give per-kind execution laws.
Database.blocks models unspecified order among foreign-key check results
from multiple tables. SendStatementsSuccess accepts a branch invariant.
Issue #411 supplies the resolved path. The README uses the table frame of
#412 to carry its original tables.
