# Enforced foreign keys (ADR 0018, slice 4)

Created 2026-10-21. Status: open.
Status file: [status](20261021-foreign-keys.status.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D4.

## Process

As for slices 1 to 3: local jj commits with the tests that touch each one; at the end of the
slice the local verdict, the corpus, and `just test-full`.

## Outcome

1. **The setting.** Foreign keys are off at the start of a script, as in SQLite.
   `PRAGMA foreign_keys = ON` and `= OFF` (also with `1`, `0`, `true`, `false`, `yes`, `no`)
   change the setting outside a transaction, and do nothing inside one. `PRAGMA foreign_keys`
   gives one row, 1 or 0, in the column `foreign_keys`.
2. **Checks, as SQLite counts them.** With the setting on, a write keeps a count of violations
   over its row changes, in the order in which it makes them, as `fkey.c` counts immediate
   constraints: a child row that it inserts, or the new key of a child row that an update
   changes, adds one when no column of the key is NULL and no parent row matches it; a child
   row that it deletes, or the old key of an updated one, removes one when that key had no
   parent and the count is above zero; a parent row that it inserts removes one for each child
   row that its key matches, while the count is above zero; a parent row that it deletes, or
   whose key an update changes, adds one for each child row of the old key, before the action of
   the foreign key runs on those rows. The rows that `REPLACE` deletes and the implicit `DELETE`
   of `DROP TABLE` count as deletes. A statement whose count is above zero at its end is
   SQLite's `FOREIGN KEY constraint failed` and changes nothing. A child or parent key compares
   under the parent key's affinity and collation. So violations that are older than the
   statement, such as rows written with foreign keys off, make no write fail unless the write
   changes one of those rows.
3. **Actions.** `ON DELETE` and `ON UPDATE` with `CASCADE`, `SET NULL`, `SET DEFAULT`,
   `RESTRICT` and `NO ACTION`, as SQLite runs them, also in a chain of foreign keys and for a
   table that references itself. `RESTRICT` fails when the parent row changes, also when the
   statement would leave no violation.
4. **Prepare errors.** With the setting on, a write that uses a foreign key whose parent key
   is not the parent's primary key or a `UNIQUE` index is SQLite's
   `foreign key mismatch - "child" referencing "parent"`, and one whose parent table does not
   exist is `no such table: main.parent`. A write uses a foreign key when it inserts into the
   child, updates a column of the child's key, deletes from the parent, or updates a column of
   the parent key; other writes to either table, such as an insert into the parent or an
   update of another child column, do not, and succeed.
5. **Restrictions.** A foreign key with `DEFERRABLE INITIALLY DEFERRED`, and
   `PRAGMA defer_foreign_keys`, stay restrictions: the slice's measurement (below) shows 11 of
   the 307 out-of-scope cases of v5 that turn foreign keys on use them, and they need a count of
   open violations across statements until `COMMIT`. An action that would run a trigger waits
   for slice 5.

## Measurement

Over the local verdict after slice 3 (2026-10-21): 307 cases of v5 that are out of scope turn
foreign keys on; 21 use `CASCADE`, 46 `SET NULL`, 20 `SET DEFAULT`, 1 `RESTRICT`, 34 `DROP
TABLE`, 15 `REPLACE`, 22 a trigger, and 11 a deferred constraint. Corpus v4 has none.

## Tests

- Lean examples of each outcome, with kernel proofs.
- An authored corpus (`conformance/authored_foreign_keys.py`), each case with a kernel proof,
  recorded as corpus 45: the setting and the pragma inside a transaction; a missing parent on
  `INSERT` and `UPDATE` of a child; each action on `DELETE` and `UPDATE` of a parent, a chain of
  `CASCADE` and a table that references itself; `REPLACE` and `DROP TABLE` of a parent; affinity
  and collation of the parent key; NULL child keys; composite keys; foreign keys turned on over
  existing violations, with writes that do not change those rows and one that does; the prepare
  errors, and the writes to the same tables that SQLite permits.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a check that ignores a NULL in a composite child key the wrong way (a key with one
  NULL column must not be checked), `SET NULL` that deletes the child row, `CASCADE` on update
  that keeps the old child key, and a check that compares the child value without the parent
  key's affinity; each killed by an authored case.

## Key points

- **The setting is a function of the script.** A `PRAGMA foreign_keys` statement never fails
  and is a no-op inside a transaction, and `ROLLBACK` does not undo it, so resolution can track
  the setting statement by statement, as it tracks the catalog, and give each write the foreign
  keys that it must keep. Execution then needs no connection setting.
- **Checked natively: the count.** With orphan child rows written while foreign keys were
  off, `INSERT INTO p VALUES (1)` and a child insert with a parent succeed, but
  `UPDATE c SET x = 9 WHERE x = 9` fails: the old orphan key removes nothing while the count is
  zero, and the new one adds one. With the parent key `p(b)` not unique, `INSERT INTO p`,
  `UPDATE c SET y = 3`, `DELETE FROM c` and `UPDATE p SET a = 1` succeed, and
  `INSERT INTO c`, `DELETE FROM p` and `UPDATE p SET b = 1` are `foreign key mismatch`.
- **Checked natively** over `p(id INTEGER PRIMARY KEY, k TEXT UNIQUE)` and
  `c(x REFERENCES p(id) ON DELETE CASCADE, y REFERENCES p(k) ON DELETE SET NULL ON UPDATE CASCADE)`:
  a child with a missing parent fails; `DELETE` of a parent cascades and sets NULL;
  `UPDATE p SET k = 'B'` cascades to `y`; `UPDATE p SET id = 5` with a child fails (`NO ACTION`);
  `DROP TABLE p` succeeds and runs the actions; `INSERT INTO c VALUES ('1', NULL)` is satisfied
  (the parent key's INTEGER affinity applies to the child value, which is stored as TEXT);
  `PRAGMA foreign_keys = OFF` inside a transaction leaves it on; a parent column that does not
  exist is `foreign key mismatch`.
- **Files.** `Resolution/ForeignKeys.lean` and `Resolution/Catalog.lean` (the catalog's foreign
  keys of ADR 0014), `Resolution/Resolve.lean` (the resolution state), the resolved writes and
  `StatementStep.lean`, `LiteralData.lean` (the constraints of a write), the frontend
  `belay/sqlite/syntax.py` (a new `PRAGMA` statement), and the conformance outputs of a query
  statement for `PRAGMA foreign_keys`.
