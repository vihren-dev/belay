# Status: enforced foreign keys (ADR 0018, slice 4)

Created 2026-10-21. Status: DONE (pull requests #204 and #205).
Task file: [task](20261021-foreign-keys.task.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D4.

## Progress

- 2026-10-21: the task file, from native probes and the measurement of the cases that turn
  foreign keys on.

- 2026-10-21: the model. Syntax: `PRAGMA foreign_keys` (`belay/sqlite/syntax_pragmas.py`,
  `Syntax.Statement.pragmaForeignKeys`) and the deferral clause as a constraint of its own
  (`deferral`, after the constraint that it follows, as SQLite's grammar has it). Resolution:
  `Resolution/ResolveState.lean` keeps the setting, which the profile's `foreignKeys` starts;
  `Resolution/ParentKeys.lean` locates each parent key as `sqlite3FkLocateIndex` does;
  `Resolution/ForeignKeyPlan.lean` gives the keys that a write processes and the writes of their
  actions, for the prepare errors and the restrictions (`Resolution/ForeignKeyResolution.lean`);
  a write with a key to check carries the trigger depth limit (`foreignKeys`). Execution:
  `ForeignKeyMatch.lean` (the three comparisons of `fkey.c`), `ForeignKeyPhases.lean` (the
  counter steps of `sqlite3FkCheck`), `ForeignKeyRows.lean` (the rows of DELETE and UPDATE in
  scan order with the actions as nested writes, fuel the trigger depth limit) and
  `ForeignKeyWrites.lean` (INSERT, UPDATE, DELETE and DROP TABLE, with SQLite's end of
  statement). The catalog is a parameter of the run, so the catalog laws hold by construction.
  Checked natively while implementing: UPDATE of a table that references itself keeps the old
  row's record while it checks the new row when SQLite's `sqlite3FkRequired` gives 1 and the
  rowid stays, so `UPDATE t SET k = '01' WHERE k = 'a'` over `t(k TEXT UNIQUE, p INTEGER
  REFERENCES t(k))` leaves a violation and succeeds; the model follows it (`staleRows`).
  Not described, by the support check: actions deeper than the trigger depth limit, a REPLACE
  that deletes more than one row of a table with keys, `SET DEFAULT` of a time default, and a
  write with subqueries whose actions change rows. Found on the way: `UPDATE t SET rowid = 5`
  resolved to `no such column: rowid`; SQLite assigns the rowid, so a rowid name as a `SET`
  column now assigns the `INTEGER PRIMARY KEY` and is the restriction `rowid-name` for a table
  without one (corpus case `fkey2-1.1.4.16.1`).
- 2026-10-21: the authored corpus `conformance/authored_foreign_keys.py` (35 cases; a case with an
  expected failure stops at that statement, under a measured profile with foreign keys on), its writer
  `conformance/foreign_key_evidence.py` (corpus 45), the mutants `conformance/foreign_key_mutants.py`,
  the restriction examples, `docs/semantic-subset.md`, and Lean examples with kernel proofs
  (`ForeignKeyExamples.lean`). Kernel proofs of the corpus: 10.7 s. Local verdict over every
  corpus, with the rowid fix: no case leaves AGREE and none disagrees; 97 cases of v5, 4 of v3
  and 1 each of v1, v2 and v4 newly agree. The four mutants change their verdicts (43.9 s).

## Done

- 2026-10-22: corpus 45 (`conformance/corpus-v45`) and its claim in `judge/claims.json` were
  merged in pull request #205, after the model in #204.
