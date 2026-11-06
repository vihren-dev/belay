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
Absent application callbacks are acquisition failures, except a view that names a callback that
is not defined, such as a function or a collation: SQLite reports an SQL error when the view is read, and
the entry below records it.

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

## Execution profiles

These rules apply to the native recorder and to native replay. The user view of
profiles is in [execution profiles](execution-profile.md).

Native C-API connections verify the library-default DQS_DML=1 and DQS_DDL=1
without overriding them. The shell runner explicitly enables both settings,
because the shell starts with DQS off.

Explicit native evidence carries a named, versioned profile with measured engine
version, source ID and the complete sorted compile-option list. Behavioral
settings include foreign-key enforcement and recursive triggers; they
are established and read back before case SQL runs. The profile names the
deferred or immediate transaction convention; SQL must use that convention.
Ignored settings carry reasons, and assumptions about other writers are recorded.

Clock input is either excluded or `unix-milliseconds-v1`. In the latter mode,
recording requires a setup timestamp and one timestamp per reached statement.
A private VFS delegates native filesystem operations and supplies both SQLite
time callbacks. Defaults, trigger bodies and supplementary probes therefore see
the same engine time. Replay supplies the recorded inputs and refuses a different
profile. Valid explicit-profile evidence stays model-unsupported when its profile
has a setting that the model does not implement (`conformance/profile_scope.py`). Existing frozen records retain their old path.
Controlled profiles also record `timezone: UTC`: recording/replay temporarily
establish UTC for native `localtime` conversion and restore the caller's timezone.
Recording is serialized while this process-global setting is active; parallel
recording should use worker processes. Other timezone profiles are refused.
Setting PRAGMAs outside the profile are refused during case SQL. Explicit boolean
writes that already match the profile are accepted. Foreign-key writes inside
an open transaction are also accepted: SQLite leaves that setting unchanged.
The recorder reads back the settings after each case statement.

Setup can temporarily change `foreign_keys` through its original SQL. Setup must
finish outside a transaction with the selected profile restored. The recorder
checks this boundary without repairing settings or resetting the database.
Fresh replay uses the same setup commands; upstream acquisition also checks
their outcomes and results against the captured Tcl execution. A source reset
clears its prefix only when `reset_db` succeeds. A failed reset leaves a named
refusal because it can have partial effects. Resets with nonempty `SETUP_SQL`
also stay refused because the reset boundary does not retain their initialization
SQL. A later plain successful reset clears those refusals. Restoration in the
same database retains the prefix and its data dependencies. Ignored settings may name
`journal_mode`, `synchronous`, `cache_size`, `temp_store`, `mmap_size` and
`busy_timeout`, each with a reason; behavioral settings cannot be labelled ignored.
Corpus manifests declare full records in `executionProfiles`; every v4 case
must match one declaration exactly. Missing/conflicting records and duplicate
name/version identities are refused. Legacy manifests retain implicit profiles.

Profiles using the original field set retain trusted schema on, DQS_DML=1,
DQS_DDL=1 and read-write/create access. Their transport remains byte-for-byte
unchanged. Profile transport `formatVersion: 2` adds four required fields:
`trustedSchema`, `dqsDml`, `dqsDdl` (booleans), and `accessMode` (`read-write` or
`read-only`). This format version is separate from the named profile's `version`,
native record version 4 and snapshot/shard storage versions. Unknown fields,
partial field sets and unsupported formats are refused.

Profile transport `formatVersion: 3` adds `limits`: the effective limits of the
connection, as `sqlite3_limit(db, id, -1)` reports them, with the fields
`columns`, `expressionDepth`, `compoundSelect`, `functionArguments`,
`variableNumber`, `length` and `triggerDepth` (`conformance/native_limits.py`).
Establishing such a profile lowers the connection's limits to these values and
reads them back. A profile of format 1 or 2 has no limits field; its recorder
kept every limit at the compile-time value, so its limits are the `SQLITE_MAX_*`
values of its compile options. No frozen record changes. Native connections no
longer set a limit of their own: a new connection keeps the build's
compile-time limits until a profile or fixture lowers them. SQLite cannot read
its schema table with fewer than 5 columns, so the recorder refuses to lower
the column limit below 5. A profile record itself accepts any natural number.

The recorder establishes trusted schema and both DQS modes on each connection,
then verifies the settings and SQLite's actual database access flag. It checks
them again after SQL, before initialization reopens and on committed-state
observers. Read-only cases initialize and commit their fixtures on a separate
writable connection with the same behavioral settings, then open the case
database with `SQLITE_OPEN_READONLY`. A query guard or `query_only` setting
cannot stand in for this access mode. Ordinary primary/extended code 8 write
denial is evidence only under a verified read-only profile; extended READONLY
recovery, locking and filesystem errors remain harness failures.

An additional native-only engine, `sqlite3-3.53.4`, uses the official source ID
`2026-07-24 19:02:57 bf7c7f30031888f4e796e429ab3978879485813aaca6f641c7b33e4e09459bcc`
and source archive SHA256
`0e9483900e92cd5de8fd48d16bf9200145a61f7fd5be542a5ac81d8a9516eb9c`.
This independent source build retains its complete actual compile options. It
does not add production parser/model support or establish equivalence with an
application's driver build. Driver/native differences still need scoped external
measurement and disposition before the workload gate can complete.
