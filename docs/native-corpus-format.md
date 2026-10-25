# Native corpus records

`conformance.native_record.record_sql` records SQLite 3.51.0 before frontend
admission. `nativeVersion: 1` retains setup SQL, migration SQL, engine identity,
requirements, an initial snapshot and per-statement native events. SQLite's
prepare tail splits statements, including whole trigger definitions. Each event
retains result rows, primary/extended code, diagnostics, visible/committed
snapshots and transaction state. Up to version 5, execution stops on its first SQL
error. Later versions add setup operations, outputs, an explicit profile and, in
version 5, the phase of each error ([conformance format v2](conformance-format-v2.md)).

Version 6 is version 5 recorded with `run_on`: execution continues after an SQL
error, so each statement of the migration gives one event. SQLite's prepare tail
can stop in the middle of a failed statement, so in version 6 a statement ends at
the end of the shortest prefix of the remaining text that `sqlite3_complete`
accepts and that is not empty, or at the end of the text. A prefix is empty when
SQLite's prepare gives no statement and no error for it, as for a lone `;`; such a
prefix belongs to the statement after it. The event's `sql` is that whole
statement. A
statement that prepares must end at the same place as its prepare tail; the
recorder refuses a case where the two differ. The native replay records a
version 6 record again with `run_on`.

Version 7 is version 6 recorded with `counters` (ADR 0024, D1). The record has the field
`counters`: an object with the integers `changes`, `totalChanges` and `lastInsertRowid`,
which are `sqlite3_changes64`, `sqlite3_total_changes64` and `sqlite3_last_insert_rowid` of the
writer connection just before the migration runs. A new connection has 0 for each, so a setup
that reopens the connection (also for a read-only profile) gives 0, and a setup that writes
gives the counts and the rowid that it left. The counters need `run_on`. A record of another
version has no field `counters`, and its run starts with unknown counters. The native replay
records a version 7 record again with the counters and refuses a record whose counters differ.

Snapshots contain all main-schema SQL objects, including views and triggers;
`table_xinfo`, `index_list`, `index_xinfo`, foreign-key metadata, and typed rows.
WITHOUT ROWID tables use their ordered primary key. Ordinary tables use an
unshadowed rowid alias; views and tables with all rowid aliases shadowed use a
sorted full-row multiset. Column-bounded reads support wide tables. Acquisition
never invokes the production parser or translator.

This is a single-main-database profile. Attached and temporary schemas are
explicit excluded connection contexts, not silently missing observations.
Absent application callbacks are acquisition failures, except a view that calls a function that
is not defined: SQLite reports an SQL error when the view is read, and the entry below records it.

A view that SQLite cannot read is evidence, not a failure. `CREATE VIEW` over a missing table
or a cycle succeeds, and reading the view fails at preparation. The snapshot then holds the
entry `{"name", "kind": "view", "unreadable": {"primaryCode", "message"}}` instead of columns
and rows. Only an SQL error of the view counts (its result code is one of the SQL error codes);
a timeout or an I/O failure still stops acquisition. The judge compares the primary code only,
and the model predicts the same code. Table replay reports a recorded view as unsupported.

`native_replay.prepare` derives schema and statements using today's frontend on
every replay. Unsupported cases retain their original native record. Admitted
cases cross-check the frozen PRAGMA metadata independently and reach the existing
Lean classifier. No native trace is regenerated or edited during model replay.
The model case format is [version 3](conformance-format-v1.md).
