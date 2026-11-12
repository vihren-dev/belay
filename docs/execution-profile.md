# Execution profiles

An execution profile describes the SQLite build and the connection settings
under which the model runs SQL. The model's results agree with SQLite only for
a connection that has the profile's settings and that satisfies the assumptions
on this page.

## The profile in Lean

A profile is a value of `Belay.Sqlite.Model.Profile`
(`packages/belay-sqlite-model/Belay/Sqlite/Model/Shared/Resolved/Profile.lean`).
It has these fields:

| Field | Meaning | Default |
| --- | --- | --- |
| `release` | The release, as `sqlite_version()` reports it | none |
| `sourceId` | The build, as `sqlite_source_id()` reports it | none |
| `limits` | The effective limits of the connection (`Limits`) | none |
| `dqsDml` | `SQLITE_DBCONFIG_DQS_DML`: a double-quoted name that names no column is a string literal in DML | none |
| `dqsDdl` | `SQLITE_DBCONFIG_DQS_DDL`: the same setting for DDL | none |
| `foreignKeys` | `PRAGMA foreign_keys` at the start of the script | `false` |
| `recursiveTriggers` | `PRAGMA recursive_triggers` at the start of the script | `false` |

Name resolution reads the limits and the two double-quoted-string settings.
The execution semantics reads the foreign-key and recursive-trigger settings.
The model does not read `release` and `sourceId`: they record which build the
profile describes, and they do not select or check the semantics.

`Limits` holds the values that `sqlite3_limit(db, id, -1)` reports: columns,
expression depth, compound SELECT terms, function arguments, the highest
parameter number, the length of one value and the trigger depth. A
compile-time option sets the highest value of each limit, and a connection can
lower it. `Limits.documentedDefaults` has the defaults that SQLite documents,
for example 2,000 columns.

Use these profiles:

- `Profile.pinned`: SQLite 3.51.0 with its source ID, the documented default
  limits, both double-quoted-string settings on, and foreign keys and recursive
  triggers off. The surface library runs statements with this profile.
- `Profile.documented release sourceId`: the same settings for another build.
  Use it until you have measured the build.
- A full `Profile` value: the measured limits and settings of a connection.

## SQLite releases

The conformance evidence compares the model with native SQLite 3.51.0, source
ID `fb2c931ae597f8d00a37574ff67aeed3eced4e5547f9120744ae4bfa8e74527b`.
Some tests also compare the model with native SQLite 3.46.0, source ID
`96c92aba00c8375bc32fafcdf12429c58bd8aabfcadab6683e35bbb9cdebf19e`. The source
archive hashes are in `parser/dialects.json`.

The parser library has the grammar of more releases (`parser/dialects.json`).
A grammar gives the syntax of a release. It does not mean that the model
describes the semantics of that release.

The conformance tools can also record evidence with a native-only SQLite
3.53.4 build. The model has no support for that build. It does not show that
SQLite 3.53.4, or the build in an application's driver, behaves as 3.51.0 does.

## Assumptions

The model runs SQL under these assumptions. The model does not run SQL on a
live connection, so it cannot check them. A theorem about a script tells you
about a real connection only when the assumptions hold for it.

The database and the connection:

- One main database on one connection. No attached or temporary schemas.
- Valid SQLite storage that contains only the schema objects that the
  [supported subset](semantic-subset.md) admits.
- No transaction is open when the script starts.
- The connection has the profile's limits and settings.
- Writable-schema mode is off, trusted-schema mode is on and the access is
  read-write.
- No extensions, custom authorizers, application callbacks or custom
  collations change what a statement does.
- No other connection or process writes to the database.

How the script runs:

- Each complete statement runs in script order on the same connection, as an
  application sends it. A statement after a failed statement also runs.
- A statement outside an explicit transaction runs in autocommit mode.
- Each transaction statement is in the supplied SQL. Nothing else adds a
  rollback, bookkeeping, cache handling or work when the connection closes.
- Only the pragmas that the supported subset names change a setting.
- Each statement reads the clock value that the run supplies for it. The
  time zone is UTC.

The outcomes:

- The model gives the SQLite errors of the supported subset, for example
  `table exists`, `no such table`, `duplicate column`, `too many columns`,
  the transaction errors and the constraint errors.
- The model has no outcome for an interruption, an exhausted resource
  (memory, disk or a limit that the profile does not record), corruption, an
  I/O error, a process crash, a power loss or interference by another
  process.
- The model does not guarantee a rollback of the whole script after an error,
  and it makes no guarantee about the state after a crash.

## Double-quoted strings

In SQLite, a double-quoted token in an expression can be a string literal. When
`dqsDml` is on, a double-quoted name that names no column in a DML statement is
a string literal. `dqsDdl` gives the same rule for DDL. A double-quoted name
that names a declared column stays a column name. SQLite's default build and
`Profile.pinned` have both settings on. The `sqlite3` shell starts with both
settings off, so a shell session can give a different result.

## Storage

A `Database` has a catalog and the rows of each catalog object:

- The catalog has each schema object in creation order. A table records its
  name as written, its columns in order with their declared type text,
  nullability and defaults, and its keys and indexes.
- Name lookup folds ASCII letters, as SQLite does. The affinity of a column
  comes from its type text by SQLite's rules.
- The rows of a table are stored at its catalog position. Each row has a
  rowid field and its cells in column order.
- In a table with a rowid, the rowid field is the physical rowid, a signed
  64-bit value. A `WITHOUT ROWID` table has no rowid: its primary key
  identifies its rows, and the rowid field of its rows is not a SQLite value.
- A cell is NULL, an integer, a REAL (its exact IEEE bits), text bytes or a
  BLOB. The model does not convert the encoding of text.

The model does not describe physical page layouts, schema text identity or the
schema cookie. The SQLite C code is not formally verified: the agreement of
the model with SQLite comes from the conformance evidence, which is
[upstream fixture evidence](conformance-fixtures.md) and
[derived model comparisons](conformance-model.md).

## Measure the engine build of an application

An application uses the SQLite build that its driver links. That build can
differ from the build that a profile describes. To measure it:

1. For each driver that the application ships, build a small command with the
   exact module version, build tags and connection setup of the driver.
2. Run the command on each platform that the application ships.
3. On the driver connection, collect `SELECT sqlite_version(),
   sqlite_source_id();` and all rows of `PRAGMA compile_options;`, sorted.
4. After the application's own setup, read back the behavioral settings, for
   example `PRAGMA foreign_keys;` and `PRAGMA recursive_triggers;`.
5. On the same connection, read each effective limit of `Limits` with the
   driver's limit API or `sqlite3_limit(db, id, -1)`, with the ID of that
   limit, for example `SQLITE_LIMIT_COLUMN` for the column limit. Do not
   change a limit while you read it. A `MAX_*` value in the compile options,
   for example `MAX_COLUMN`, is only the highest value; it does not show
   whether the application lowered the limit.
6. Keep the driver's dependency lock, the command, its build configuration and
   its outputs with the application's profile.

A system `sqlite3` shell or a package version does not measure the engine that
a driver links.

Then compare the measurements with the profile that your proofs use:

- A different release, source ID or compile option is an open gap until you
  have checked its effect on the application's SQL.
- If the difference affects that SQL, the evidence needs a build with that
  source. Do not label evidence from one build as evidence for another build.
- Until the measurements exist, say that the evidence uses the pinned build
  and that the difference to the application's build is not measured.

The conformance tools record native evidence under recorded execution profiles.
The team documentation of those records is in
[native corpus records](native-corpus-format.md#execution-profiles).
