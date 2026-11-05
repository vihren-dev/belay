# `#sql_check` on the tables a developer has

Created: 2026-11-05. Status: DONE (2026-11-05).
Source: issue #318 ("Counterexample search finds the NOCASE pair only on a one-column table
without constraints"); issue #293 (a schema with a primary key discards a certified
counterexample). Design: [ADR 0031](../docs/adr-0031-fast-sql-check.md), D3 and D6 as
amended for #318. Audience: the team.

## Observable behavior

With the default `sql.checkBudget`, for the claim "the unique `NOCASE` index on
`customers(email)` succeeds where no two rows have the same email" and each schema `S` of
#318 (`onePlain`, `oneChecked`, `twoPlain`, `twoChecked`: an email column, with or without an
INTEGER PRIMARY KEY, with or without a CHECK, and one supplied row `'ann@x.io'`):

- `Succeeds uniqueEmail (fun db => db.raw.catalog = S.raw.catalog ∧ Holds noDuplicateEmails db)
  with (schema := S)` is `false`.
- `uniqueEmail succeeds where noDuplicateEmails with (db := S)` is `false` with a database of
  `S`'s catalog: the developer's table and row, and one more row that collides with it under
  `NOCASE`, for example `'ann@x.io'` and `'Ann@x.io'`.
- The replay builds the database from `S`'s SQL text, with its constraints, and fails in
  native SQLite with the UNIQUE error.

The changes:

1. **Construction from the schema's text.** A candidate that the checker generates on a
   schema with SQL text (a `db!` constant) is built by that text without its INSERT
   statements, with the candidate's rows of each table right after the statement that creates
   the table. The model validates the text as today (`constructionMatches`). A schema text with
   other statements (ALTER TABLE, UPDATE, ...) gives no such construction.
2. **Variants of supplied rows.** After the supplied database, the targeted candidates have,
   for each table with rows, the database with one more row: the first row with the first
   ASCII letter of each text in the other case, the same row again, and the row with NULL in
   each column that allows NULL. The INTEGER PRIMARY KEY column gets the new rowid.
3. **`db :=` gives the schema.** Without `(schema := …)`, the first `(db := …)` is also the
   search schema.

## Tests

- A new fixture with the four schemas of #318 and the claims above, run by a pytest test in
  the surface check suite: each answer is `false`; the test runs the replay of `twoChecked` in
  native SQLite 3.51.0, which builds the table with its CHECK and gives the UNIQUE error.
- The claim of #293 (`INSERT INTO customers (id, name) VALUES (1, 'Grace')` on a schema with
  an INTEGER PRIMARY KEY) is `false`, with a replay.
- `#guard`s of `Sampling.caseVariant` and `Sampling.rowVariants`.
- The existing surface check suites give the same results. A fixture whose answer changes
  because `db :=` now gives the schema is a capability change and is listed in the status
  file.

## Tricky points

- The schema text is metadata on the generated database term (`schemaSourceKey`), as the
  `db!` source is; it is a hint, and the construction is validated.
- The rows go in right after their CREATE TABLE, so that the triggers and indexes that later
  statements create do not see the INSERTs. A trigger is created after its table, so no
  trigger on a table exists when that table's rows are inserted.
- Rowids: the construction inserts without explicit rowids except through an INTEGER PRIMARY
  KEY column. The supplied rows and their variants must have the rowids that SQLite assigns,
  or the validation rejects the candidate.
- The candidate loop counts targeted candidates by index; its bound grows by the number of
  variants (`suppliedVariantBound`).
- #318's first cause (rows that repeat one value across columns) does not apply to an
  INTEGER PRIMARY KEY, which gets the rowid; the replay construction was the cause for
  `twoPlain`.
