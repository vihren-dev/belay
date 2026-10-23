# Status: the connection counters (ADR 0024, slice 1)

Created 2026-10-23. Status: OPEN (task file written; implementation not started; three owner
decisions open).
Task file: [task](20261023-connection-counters.task.md).
Specification: [ADR 0024](../docs/adr-0024-connection-state-and-random-values.md) (ACCEPTED
2026-10-23), D1 to D3, D5, D6 slice 1.

## Relevant files

- Model: `Model/SqlState.lean`, `Model/ScriptRun.lean`, `Model/StatementStep.lean`,
  `Model/StatementRun.lean`, `Model/StatementOutput.lean`, `Model/Output.lean`,
  `Model/ExprFault.lean`, `Model/StatementClock.lean`, `Model/SqlExecution.lean`,
  `Model/ForeignKeyPhases.lean`, `Model/ForeignKeyRows.lean`, `Model/ForeignKeyWrites.lean`,
  `Model/TriggerRun.lean`,
  `Model/LiteralData.lean`; resolution: `FunctionCatalog.lean`, `FunctionCalls.lean`,
  `GeneratedColumns.lean`, `IndexTerms.lean`, `TableChecks.lean`, `ParameterOrder.lean`,
  `TriggerBodies.lean` (all under `packages/belay-sqlite-model/Belay/Sqlite/`).
- Surface: `packages/belay/Belay/Sqlite/Env.lean`, `Run.lean`, `ProgramRun.lean`,
  `ProgramLaws.lean`, `RunLaws.lean`.
- Conformance: `packages/verifier-conformance/VerifierConformance/Pass.lean`, `Case.lean`,
  `Predict.lean`; `conformance/predict.py`, `record_versions.py`, `native_replay.py`.
- Recorder and judge (PR B): `conformance/native_record.py`, `native_statements.py`,
  `native_library.py`, `judge/records.py`, `judge/claims.json`.

## Progress

- 2026-10-23: the task file, from the code of this tree, the ADR's facts, the native probes
  below and the measurement below.
- 2026-10-23: review round 1 (R19, must): outcome 3 gave the plain INSERT's rule to every
  failed INSERT. Fixed: a write that runs row by row has its own rule, with new probes.
- 2026-10-23: review round 2 (R19, must): a one-row INSERT fails a foreign key before its
  insert. Fixed: outcome 3 gives SQLite's rule (`isMultiWrite`), from `fkey.c`, `build.c`
  and `insert.c` of the pinned sources and new probes.
- 2026-10-23: review round 3: finding 1 (R19, must): a `RESTRICT` action of a REPLACE fails
  when it runs, not at the end of the statement. Fixed in outcome 3, with a new probe.
  Finding 2 (R19, must) is rejected: it says that the trigger probe gives 0, 3, 60; a new run
  of the probe gives 1, 1, 1 after `INSERT INTO p VALUES (1)` and 0, 2, 60 after the failed
  INSERT (the trigger's row counts, the statement's own row does not).
- 2026-10-23: review round 4 (R19, must): the probe list did not say which probes ran in a new
  session, so the rejection of round 3 compared two histories. Fixed: each item of the probes
  of failed writes that run row by row is a new session, with the counters before it. This is
  the fourth round in a row with a must finding, so the fix has no review; the owner decides.

## Native probes (3.51.0, dev shell `sqlite3`, one statement per line)

The ADR's table of facts and its examples are not repeated here. New facts for the task file:

- Generated column, `CREATE TABLE g(a, b AS (E))`: `changes()`, `total_changes()`,
  `last_insert_rowid()`, `random()` and `randomblob(2)` each give `non-deterministic functions
  prohibited in generated columns`. `changes() + nosuch` and `nosuch + changes()` give `no such
  column: nosuch`. `changes() + count(a)` gives `misuse of aggregate function count()`;
  `count(a) + changes()` the non-deterministic error. `changes() + nosuchfn(1)` gives `no such
  function: nosuchfn`; `nosuchfn(1) + changes()` the non-deterministic error. `abs(changes())`
  gives the non-deterministic error; `changes(1)` gives `wrong number of arguments to function
  changes()`; `changes() + ?` gives `parameters prohibited in generated columns`.
  `count(a) + CURRENT_TIME` gives the non-deterministic error.
- Index, table `t(a, b)` with one row, and an empty table `e(a)`: `CREATE INDEX i ON t(changes())`,
  `t(a + total_changes())`, `t(random())` and `e(changes())` give `non-deterministic functions
  prohibited in index expressions`; `WHERE last_insert_rowid() > 0` and
  `WHERE randomblob(1) IS NOT NULL` give `... in partial index WHERE clauses`.
  `e(a + nosuch, changes())` gives `no such column: nosuch`; `e(changes(), a + nosuch)` the
  non-deterministic error. `t(changes() + count(a))` gives the misuse; `WHERE changes() + nosuch`
  and `WHERE nosuch + changes()` give `no such column`; `t(abs(changes()))` the
  non-deterministic error.
- `CREATE TABLE c1(a CHECK (changes() >= 0), b DEFAULT (changes()))` and
  `CREATE TABLE c2(a DEFAULT (last_insert_rowid()), b DEFAULT (total_changes()), c DEFAULT (random()))`
  succeed.
- Reads, on `t(id INTEGER PRIMARY KEY, v, w)` after `INSERT INTO t(v) VALUES (1), (2), (3)`
  (counters 3, 3, 3): `UPDATE t SET w = total_changes(), v = changes() WHERE id <=
  last_insert_rowid() RETURNING id, v, w, changes(), total_changes(), last_insert_rowid()` gives
  `1|3|3|3|3|3`, `2|3|3|3|3|3`, `3|3|3|3|3|3`, then 3, 6, 3. `DELETE FROM t WHERE id = 1
  RETURNING changes(), total_changes(), last_insert_rowid()` gives `3|6|3`, then 1, 7, 3.
  `SELECT (SELECT changes()), total_changes() FROM t WHERE changes() = 1` gives `1|7` twice.
  `INSERT INTO t(id, v) VALUES (2, 9) ON CONFLICT(id) DO UPDATE SET w = changes() RETURNING id, w`
  gives `2|1`, then 1, 8, 3. `DELETE FROM t` (2 rows) gives 2, 10, 3.
- `r(id INTEGER PRIMARY KEY, u UNIQUE)` with rows 1 and 2: `INSERT OR REPLACE INTO r VALUES (3, 'a')`
  gives 1, 13, 3 (13 = 10 + 2 + 1); `INSERT OR IGNORE INTO r VALUES (4, 'b')` gives 0, 13, 3.
  An INSERT into a `WITHOUT ROWID` table gives 1, 14, 3. `BEGIN`, an INSERT of rowid 10 and
  `ROLLBACK` give 1, 15, 10.
- Without triggers: `INSERT INTO t(v, w) VALUES (total_changes(), changes()), (total_changes(),
  changes())` after counters 2, 2, 2 stores 2 and 2 in both rows; an upsert of two DO UPDATE
  rows and one new row with `SET w = total_changes() + 100` stores 104 in both updated rows,
  then 3, 7, 9.
- After `INSERT INTO t VALUES (1), (2)` (2, 2, 2): `PRAGMA integrity_check`,
  `PRAGMA foreign_key_check`, `PRAGMA table_info(t)`, `PRAGMA recursive_triggers = 1` and
  `PRAGMA foreign_keys = 1` leave 2, 2, 2. `ALTER TABLE t ADD COLUMN b DEFAULT 3`,
  `CREATE INDEX`, `DROP INDEX`, `CREATE TABLE u(x)`, an INSERT into `u` and `DROP TABLE u` with
  foreign keys on and no reference give 1, 3, 1.
- Failed plain INSERTs, `t(id INTEGER PRIMARY KEY, v UNIQUE, n NOT NULL DEFAULT 0, c CHECK (c IS
  NULL OR c > 0))` with row (1, 1), counters 1, 1, 1: `INSERT INTO t(v) VALUES (10), (11), (1)`
  fails, then 0, 1, 3; `(20), (20)` fails, then 0, 1, 2; `INSERT INTO t(v, n) VALUES (30, 1),
  (31, NULL)` fails, then 0, 1, 2; `INSERT INTO t(v, c) VALUES (40, 1), (41, 1), (42, -1)` fails,
  then 0, 1, 3; `INSERT INTO t(id, v) VALUES (50, 50), ('x', 51)` fails with `datatype mismatch`,
  then 0, 1, 50; `INSERT INTO t(id, v) VALUES (1, 60)` fails, then 0, 1, 50.
- Failed writes that run row by row. Each item is a new session; the counters before the first
  failed statement are 1, 1, 1.
  - `t(id INTEGER PRIMARY KEY, v)` with row (1, 1) and `CREATE TRIGGER tr AFTER INSERT ON t WHEN
    new.v < 0 BEGIN SELECT RAISE(ABORT, 'fail'); END`: `INSERT INTO t VALUES (10, -1)` fails,
    then 0, 1, 10; `INSERT INTO t VALUES (20, 1), (21, -1), (22, 1)` fails, then 0, 1, 21. With a
    BEFORE INSERT trigger of the same form on `b`, `INSERT INTO b VALUES (40, 1), (41, -1)`
    fails, then 0, 1, 40.
  - Foreign keys on, `p(id INTEGER PRIMARY KEY)` with row 1, `c(id INTEGER PRIMARY KEY, pid
    REFERENCES p(id))`: `INSERT INTO c VALUES (30, 1), (31, 2), (32, 1)` fails with `FOREIGN KEY
    constraint failed`, then 0, 1, 32.
  - The same tables: `INSERT INTO c VALUES (30, 2)` fails, then 0, 1, 1 (the value before);
    `INSERT INTO c SELECT 40, 2` fails, then 0, 1, 40; `INSERT INTO c VALUES (50, 1)` succeeds,
    and `INSERT INTO c VALUES (51, 1), (52, 2)` fails, then 0, 2, 52.
  - The same tables, `log(x)` and `CREATE TRIGGER ct AFTER INSERT ON c BEGIN INSERT INTO log
    VALUES (new.id); END`: `INSERT INTO c VALUES (60, 2)` fails, then 0, 2, 60.
- `p(id INTEGER PRIMARY KEY, u UNIQUE)` with rows (1, 1) and (2, 2), foreign keys on, and
  `c(id INTEGER PRIMARY KEY, pid REFERENCES p(id) ON DELETE RESTRICT)` with row (5, 1)
  (counters 1, 3, 5): `INSERT OR REPLACE INTO p VALUES (7, 7), (8, 1)` fails with `FOREIGN KEY
  constraint failed`, then 0, 3, 7; `INSERT OR REPLACE INTO p VALUES (9, 1)` fails, then 0, 3, 7.

## Measurement

The scan of the task file's "Measurement", run in this workspace with `python3 -I`: for each
corpus of `judge/claims.json`, read each record of `shards/*.jsonl.gz` (the record or its
`native` member) and match `\b(changes|total_changes|last_insert_rowid|random|randomblob)\s*\(`,
ignoring case, against `migrationSql` and `setupSql`. `synthetic-workload` has no shards at its
top; a `grep` of its `corpus/shards` found no match. `mustAgree` of corpus-v4 and corpus-v5
was read from `judge/claims.json`.

## Coordination with the work in flight

- **The evidence after an error** (workspace `errev`): record version 6 and corpus-v51. This
  task's corpus needs both the run that continues and the counters at the start, so it takes
  version 7 and corpus-v52 (decision 1). Its PR A needs the version 6 readers of errev's PR A.
- **The pragmas of ADR 0019 slice 2** (workspace `adr19s2`): corpus-v50 and new statement
  forms, which leave the counters.
- **The keys-unique theorems of ADR 0022 slice 2** (workspace `adr22s2`): theorems over
  `runStatement` and `runSqlFrom`. A new field of `SqlState` or `StatementRun` changes proofs
  that take them apart; the theorem statements stay, because the effect databases stay.
- Order (decision 3): pragmas (v50); errev PR A and PR B (v51); keys-unique; this task's PR A;
  this task's PR B (v52).

## Owner decisions

On 2026-10-23, the owner accepted the recommendation of each decision below: record version 7
(version 6 and the counters) for corpus-v52; the hypothesis that the run of `q` does not end
early in `Script.run_append`; and the pull request order of "Coordination with the work in
flight". A fifth review, of the last fix of the status file, had no findings.

1. **The record of corpus-v52.**
   - A (recommended): version 7 is version 6 with the three counters at the start of the
     migration. The cases can read the counters after a failed statement, so the mutants of the
     failed rows get native evidence in this slice. Cost: PR B waits for errev's PR B.
   - B: version 7 is version 5 with the counters, recorded now. The failed rows keep Lean
     examples only, and their mutants wait for a later corpus.
   - C: a field on version 6 instead of a version. errev's owner decision 2 chose a version
     over a field for the same reason: each reader would have to check the field.
2. **`Script.run_append`** (`RunLaws.lean`), which becomes false (task file, key points).
   - A (recommended): the law gets a second hypothesis: no output of the run of `q` on the
     database that `p` gives ends the run (`Output.endsRun`). Then `q` reads no unknown counter
     there, and it gives the same outputs with the counters that `p` left. The guide's form stays
     an equation of outputs.
   - B: the law runs `q` on the connection at the end of `p`
     (`Script.runOn (db.run p).connection q`), with no new hypothesis. The guide's form then
     names a connection, which the guide does not use.
3. **The order of the pull requests**: as in "Coordination" (recommended), or this task first
   with version 6 and corpus-v51, which would make errev move to version 7 and corpus-v52.
   Cost of the second: errev is in progress and its task file names version 6 and v51.

## Review records

None yet.
