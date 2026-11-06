# `#sql_check` fills only the touched tables, with rows that satisfy constraints

Created: 2026-11-06. Status: OPEN.
Design: [ADR 0031](../docs/adr-0031-fast-sql-check.md), slice 3: D4, D7, and the consumer-size
fixture and acceptance records of D9. Slice 2 (D2, D3 without D4, D5, D6, D8) is DONE in
[20261106-check-compiled-screen](20261106-check-compiled-screen.task.md). Audience: the team.

## Observable behavior

The trust rule does not change: `proved` and `false` come only from kernel-checked proofs, and a
`false` result needs a replay that native SQLite runs.

1. **Touched tables (D4).** The generated candidates of the search (`Sampling.candidates`: the
   targeted databases, the table contents and the seeded random databases, steps 2 and 3 of D3)
   fill only the touched tables; the other tables are empty in them. The touched tables are the
   tables that the claim's statements read or write, closed under:
   - the triggers on a touched table: the tables that their bodies read or write;
   - the foreign keys: the parent tables of a touched table, and the child tables whose foreign
     keys refer to a touched table (their actions and checks run when the parent changes).
   A claim whose statements the checker cannot find (a plain Lean predicate, or no SQL sites)
   touches every table, and so does a statement whose tables the collection does not name.
   Explicit witnesses, the empty database and the named databases are not changed.
2. **Rows that satisfy constraints (D4).** A row of the table contents and of the seeded random
   databases has no NULL in a NOT NULL column. A column with a foreign key gets one of the
   parent's key values when the parent has rows in that candidate. A row that repeats a UNIQUE or
   PRIMARY KEY value of an earlier row of its table is left out (the rowid alias of an INTEGER
   PRIMARY KEY is distinct in every row). CHECK constraints and the other rules stay with
   `Sampling.validated`. The rows of the targeted databases are not changed: ADR D3 applies the
   changes of D4 to the table contents, and the targeted rows test the edges of the constraints on
   purpose (duplicates, NULL cells). Amended 2026-11-06; before, the rule named every generated
   row.
3. **The schema as the domain (D7).** `db.HasCatalog schema` (`Database.HasCatalog db schema`)
   is a decidable proposition: the catalog of `db` is the catalog of `schema`. The ADR writes the
   parameters as `(schema db)` and the use as `db.HasCatalog schema`; with dot notation the first
   parameter is `db`, and the equality is the same either way (amended 2026-11-06). The search
   reads a premise `db.HasCatalog schema`, also as a conjunct and in the predicate of
   `Succeeds s (·.HasCatalog schema)`, as it reads `db = sample`: it uses `schema` as the schema
   of the candidates, with its schema text for the replay. A supplied `(schema := …)` still takes
   priority.

## Tests

Each test has a timeout and runs in the suites of the surface checks (`surfaceChecks`,
`surfaceS6`).

- Candidate order (`tests/surface/CounterexampleSearchBudget.lean`): on a schema with an
  untouched table that has rows, the targeted databases, the contents and the seeded databases
  leave it empty; a
  NOT NULL column gets no NULL; a foreign key column gets a parent key; no two rows of a table
  repeat a UNIQUE or PRIMARY KEY value; the trigger and foreign-key closures add their tables.
- `Database.HasCatalog`: `decide` proves it for a database and its schema and refutes it for
  another catalog; a claim with the premise and no `(schema := …)` is `false` with a candidate
  on that schema.
- The consumer-size fixture (D9): an authored schema of the consumer's size and kind, not the
  consumer's text: more than 8,192 nodes, triggers that write another table, CHECK constraints
  and foreign keys, and a statement besides CREATE in its text (for example ALTER TABLE ADD
  COLUMN). Its claim `∀ id, Succeeds (deleteMessage id) (·.HasCatalog consumer)` is `false` at
  the default options; the counterexample has at most two rows in each touched table; its
  construction uses `.dbconfig enable_trigger off`; native SQLite rebuilds the candidate's rows
  and the replay fails with the same CHECK error. The same fixture shows that a counterexample
  supplied with `db!` is reported.
- The existing fixtures of S5 and S6 give the same results. Each fixture whose result changes is
  a capability change: the status file lists it with the reason, and the pull request names it
  for the owner.

Acceptance records in the status file (records, not test assertions): for the claim of #316, its
true variant and the consumer-size claim, the time of each phase as in the Context section of
the ADR; the time of the surface check suites in `just test-full` before and after (the slice 2
results are the "before"); the defaults of `sql.checkCandidates` and `sql.checkTimeLimit`
measured again with the consumer-size claim.

## Tricky points

- The claim's statements: `querySites` finds the script sites. `Sampling.scriptHints`
  (`SchemaHints.sources`) names the tables of queries and write targets, but `statementHints`
  gives no sources for other statements, for example ALTER TABLE and DROP TABLE. The touched
  tables need a collection that names the tables of every statement kind, or that counts every
  table as touched for a kind that it does not handle. Trigger bodies
  are `CatalogTrigger.body` (`Syntax.BodyStatement`); the foreign keys are on `CatalogTable` and
  `CatalogColumn` (`foreignKeys`). Table names compare as SQLite identifiers (folded case).
- `visitContents` enumerates contents over every table of the catalog; with dozens of tables and
  no touched-table filter the order "fewest rows first" never reaches two rows in the table that
  matters within `sql.checkCandidates`. Untouched tables must not multiply the contents.
- `withCells` applies affinity and assigns rowids after the selection, so two selections can
  give the same database, and the uniqueness rule must hold on the stored values (an INTEGER
  PRIMARY KEY column is the rowid alias, `CatalogTable.rowidAlias`).
- A foreign key value depends on the rows of the parent in the same candidate, so the
  generation order of the tables matters: parents first, where the keys allow it.
- The data limits of `CheckBudget.lean` must admit the consumer-size schema (9,561 nodes);
  the screen compares catalogs for `HasCatalog` on each candidate, and must stay fast.
- The construction of a candidate on a schema text with triggers needs the trigger-off form of
  slice 2 (`Replay.SchemaConstruction.triggersOff`), else the triggers write rows while the
  candidate is built.
