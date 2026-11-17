# Multi-row UPDATE and transient unique keys

Created 2026-11-17. Issue [#219](https://github.com/vihren-dev/belay/issues/219).
Status: open. The companion status file records the checks.

An UPDATE can leave a table with distinct keys and still fail while SQLite
writes a row. For example, on rows (3, 9) and (1, 2) with a unique index on
a + b, setting b to zero makes the first key equal to the second row's old
key. A partial index can do the same when one row enters its filter and
another leaves it. For a unique index on a WHERE b > c, use (a,b,c) rows
(1,10,20) and (1,3,0) and set c to 5. The plain UPDATE model must refuse an order-dependent
success when a new key conflicts with a different row's old key. The ready check marks the run as outside the model. The modeled effect
still uses the final-table constraint check. An UPDATE
whose final table violates a constraint must retain its existing diagnostic.

The filter, expression terms, collation and NULL behavior come from
LiteralData.keyEqual. LiteralData.updated preserves row positions, including
when the rowid changes. Matching a row's own old key is harmless.
StatementRun.withKeys also has a separate execution for trigger and
foreign-key rules. The restriction concerns the plain write. The public
derived-column backfill law must still prove success when the keys read
only the old columns.

## Acceptance

A regression test runs both SQL examples against the pinned SQLite shell
and checks that it reports a unique constraint error. The same examples
through Belay must refuse the ambiguous result. A successful update with
no cross-row conflict, including a row that retains its key, must still run.
The existing DbBangConstraintWrites fixture must retain its final-table
failure reports. The Lean packages, the full test suite, and the verdict on
the frozen corpora must pass. Report any change in corpus coverage.
