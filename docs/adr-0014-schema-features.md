# ADR 0014: Schema features: index forms, CHECK, collations and table options

Date: 2026-10-19. Status: ACCEPTED on 2026-10-19 (#170).
Audience: designers and reviewers.
Evidence: [the schema features measurement](../experiments/schema-features/README.md).
Related: [ADR 0008](adr-0008-syntax-and-resolution-in-lean.md) (catalog and resolution),
[ADR 0012](adr-0012-query-semantics.md) (keys, conflict algorithms and queries),
[ADR 0013](adr-0013-model-structure.md) (one catalog in execution, comparisons that carry
their affinity), [ADR 0011](adr-0011-product-trust-and-development-integrity.md) (claims and
the judge).

## Overview

Today the model refuses a schema that has any of these features: a partial or expression
index, an index built over existing rows, CHECK, COLLATE, a generated column,
`WITHOUT ROWID` or `STRICT`. Real application schemas use them, so the migration checker
refuses those schemas before it looks at the migration. This ADR adds them to the
catalog, to resolution and to execution, in six slices that the measurement orders, and
adds `DROP INDEX` and `DROP TABLE` as a seventh. Foreign-key enforcement, `AUTOINCREMENT`
and `CREATE TABLE ... AS SELECT` stay out of scope (see "Not decided here").

## Context

The measurement reads the out-of-scope cases of corpus v5: 3,398 of its 4,376 cases.

- **Scale.** 1,529 of these cases use at least one schema feature. 532 of them use no
  feature outside the schema features ("clean"). For those 532, support for the schema
  features is the only missing piece that a lexical scan can see.
- **Order.** Ordered by the clean cases that each feature adds, the features bring in:
  - partial index 120, then `WITHOUT ROWID` (252 in total), collations (307),
    expression index (358) and CHECK (402);
  - an index built over existing rows (435), generated columns (465), and a CREATE TABLE
    with constraints that runs in the script (490);
  - everything else adds 42 more.
- **What else blocks them.** The other 997 cases also use a feature outside this ADR.
  The most common is a `PRAGMA` (342 cases). In the 273 cases where it is the only other
  feature, the pragmas are `foreign_keys=` and `foreign_key_check`, so foreign-key
  enforcement is the main blocker. Then come `DROP INDEX` and `DROP TABLE` (110 cases
  where DROP is the only other feature), and `ALTER TABLE ... RENAME` or `DROP COLUMN`
  (76 cases).
- **Upper bounds.** The clean counts are upper bounds: a restriction that a lexical scan
  does not see, such as an unmodeled function, can still stop a case. Each slice measures
  its real effect with the verdict, as earlier slices did.

The recorder already captures what these features need: a table's `withoutRowid` flag,
its row key (`rowKey`), and the collation of each index column. The frozen corpora
therefore need no new recording. Only the conformance harness reads more of each
snapshot.

The model has the structure for this since ADR 0013:

- one catalog function per definition, shared by resolution and execution;
- resolved comparisons that carry their affinity;
- one write path with its readiness check;
- a restriction registry, which each slice shrinks.

## Decision

### D1. Index keys are expressions, with an optional filter

A catalog index has a list of key terms and an optional `WHERE` filter.

- **Key terms.** A key term is a column position or a resolved expression over the
  table's row. Each term has a collation (D3) and a sort order.
- **Resolution.** The terms and the filter resolve in the scope of the indexed table
  alone. SQLite's prepare errors apply to these forms, for example a non-deterministic
  function or a subquery in an index expression. A form that the model cannot evaluate
  stays a restriction.
- **Uniqueness.** A unique index constrains only the rows whose filter is true (NULL is
  not true). Two rows conflict when every key term is equal under its collation, and
  neither has a NULL key term, as today.
- **Sort order.** The sort order changes no result that the model observes, so the model
  keeps it only to describe the index.
- **Building over existing rows.** A CREATE INDEX that runs over existing rows builds the
  index. For a unique index, a conflict among those rows fails the statement with
  SQLite's constraint error, and the catalog stays the same.

The unique keys of a table (`Catalog.uniqueKeys`) become this one form. The primary key,
UNIQUE constraints and unique indexes are then checked by one function.

### D2. CHECK constraints and named constraints

- **Where CHECK constraints live.** A table has a list of CHECK constraints, from columns
  and from table constraints, in written order. Each is a resolved expression over the
  row and the label that SQLite reports: the constraint's name, or else the expression
  text as written.
- **When they are checked.** INSERT, UPDATE and the DO UPDATE of an UPSERT check them in
  SQLite's order: NOT NULL, then CHECK, then the unique keys.
- **Result.** A CHECK fails when its value is false. NULL passes.
- **Conflict algorithms.** `OR IGNORE` skips the row. `REPLACE` acts as `ABORT`, because
  SQLite replaces only for unique keys. The other algorithms keep their meaning.
- **Named constraints.** `CONSTRAINT name` may come before any constraint. Only CHECK
  reports the name.
- **Inert `REFERENCES`** (owner decision 3). A `REFERENCES` clause or a `FOREIGN KEY`
  table constraint is admitted under a profile that does not enforce foreign keys, where
  SQLite ignores it apart from its prepare errors. The catalog keeps no foreign key.
  Under a profile that enforces them, it stays a restriction.
- **ADD COLUMN.** An `ADD COLUMN` with a CHECK follows SQLite's check of the existing
  rows. The slice confirms the exact rule natively first.
- **CREATE TABLE in the script.** A CREATE TABLE with constraints that runs in the script
  uses the same catalog function as a described one. The restriction
  `create-table-constraints` goes.

### D3. Collations are resolved once, like affinity

- **Which collations.** A collation is `BINARY`, `NOCASE` or `RTRIM`, SQLite's built-in
  sequences. Any other name is SQLite's prepare error `no such collation sequence`.
- **Where they are declared.** A catalog column has a collation (`BINARY` by default).
  An index term or key term may name another.
- **Resolution assigns them.** Resolution gives each of these its collation by SQLite's
  rules (`sqlite3ExprCollSeq` and `sqlite3BinaryCompareCollSeq`): a comparison, `IN`, an
  `ORDER BY` or `GROUP BY` term, `DISTINCT`, and `min` and `max`.
- **SQLite's rule for a comparison:**
  1. an explicit `COLLATE` on the left operand;
  2. else one on the right operand;
  3. else the column collation of the left operand;
  4. else that of the right operand;
  5. else `BINARY`.
- **Stored in the resolved node.** The collation is stored where it is used, as ADR 0013
  stores affinity on a comparison.
- **Execution.** Text compares through the collation. `NOCASE` folds ASCII letters with
  `lowerAscii`, and `RTRIM` ignores trailing spaces. Values that are not text compare as
  they do today.
- **The `COLLATE` operator.** `x COLLATE NOCASE` in an expression becomes a Syntax form.
  It changes the collation and not the value.
- **Kernel cost.** `BINARY` keeps today's comparison, so a model without collations costs
  no more kernel time.

### D4. `WITHOUT ROWID` tables

A table has a `withoutRowid` flag, with these rules:

- **Primary key required.** The table must have a PRIMARY KEY. SQLite's prepare error is
  `PRIMARY KEY missing on table t`.
- **Key columns.** Its key columns are NOT NULL.
- **No rowid.** No column is a rowid alias, and `rowid`, `_rowid_` and `oid` are ordinary
  names. With no such column they are `no such column`.
- **Scan order.** The table keeps its rows in primary-key order under the key
  collations, which is the order of a full scan.
- **Representation.** A row of such a table keeps the `rowid` field with the value 0.
  `Table.Valid` states the key order and distinct keys in place of distinct rowids.
- **Harness.** The harness compares these tables by the native `rowKey` and not by
  rowid.
- **Proof of the invariant.** The write path inserts by key. The proof that writes keep
  `Table.Valid` gets one case for the ordered insertion.

### D5. Generated columns

- **Declaration.** A catalog column may be generated: `VIRTUAL` or `STORED`, with a
  resolved expression over the other columns of the row.
- **Values.** The model computes the value when it writes a row and stores it for both
  kinds. The two kinds read the same values, so the model need not tell them apart for
  reads.
- **Writes.** An INSERT or UPDATE that names a generated column is SQLite's prepare
  error, for example `cannot INSERT into generated column "b"`.
- **SQLite's rules on definitions** are prepare errors:
  - a generated column may not be part of the primary key;
  - it may not have a default;
  - `ADD COLUMN` may not add a `STORED` one.

### D6. `STRICT` tables

- **Declared types.** A `STRICT` table admits only the declared types `INT`, `INTEGER`,
  `REAL`, `TEXT`, `BLOB` and `ANY`.
- **Writes.** After the column's affinity applies, a value whose storage class does not
  fit the type fails the statement with SQLite's constraint error, for example
  `cannot store TEXT value in INTEGER column s.a`. NULL fits every type. `ANY` keeps
  the value as written, with no affinity.

### D7. `DROP INDEX` and `DROP TABLE`

- **What they do.** `DROP INDEX` removes an index from the catalog. `DROP TABLE` removes a
  table and its indexes, and its rows.
- **Errors.**
  - SQLite's prepare errors apply, for example `no such table` and `no such index`.
  - `IF EXISTS` turns those two into no-ops.
  - An index that belongs to a constraint (`sqlite_autoindex_...`) cannot be dropped:
    `index associated with UNIQUE or PRIMARY KEY constraint cannot be dropped`.
  - Each of these was checked natively.
- **Catalog positions.** A removal changes the positions of later objects. The catalog
  function of DROP is shared by resolution and execution, as ADR 0013 requires for every
  definition, and resolved statements refer to positions after the DROP.
- **Scope.** A table that a trigger, a view or an enforced foreign key refers to stays a
  restriction, since the model has none of these.

### Order and pull requests

The slices follow the measured order, and each has its own task file:

1. index terms, filters and indexes built over existing rows (D1);
2. `WITHOUT ROWID` (D4);
3. collations (D3);
4. CHECK and named constraints, and CREATE TABLE with constraints in the script (D2);
5. generated columns (D5);
6. `STRICT` (D6);
7. `DROP INDEX` and `DROP TABLE` (D7).

The order differs from the measured one in two places:

- **Expression indexes come with partial indexes,** because both need resolved
  expressions over one row.
- **`STRICT` comes last.** It brings in only 4 corpus cases, but real schemas use it.

Each slice works in this way:

- It adds an authored corpus that covers its feature.
- It lifts its restrictions from the registry.
- It measures the verdict of every corpus.
- A slice whose verdict changes has a pull request B that claims the cases
  (`judge/claims.json`).
- A judge change, such as the comparison of `WITHOUT ROWID` rows, has its own pull
  request A with a new judge lock, under ADR 0011.

### Implementation notes

- Slice 1 (2026-10-19): the key forms and the catalog index live in
  `Resolution/Keys.lean`, and `Catalog.uniqueKeys` gives every key as terms with an optional
  filter. An index may repeat a column, as SQLite allows. The time keywords in an index
  are covered by Lean examples only: the recorder refuses them outside a controlled clock.
- Slice 2 (2026-10-19), a change of D4's representation: the rows of a `WITHOUT ROWID`
  table keep distinct hidden rowids, which the writes allocate as for any table and no
  result shows, and `Table.scanRows` orders a full scan by the primary key. So the write
  path, `Table.Valid` and its proofs stay as they are. Queries and the `RETURNING` rows of
  UPDATE and DELETE read the scan; the harness compares such a table by its cells in key
  order, and the prediction gives each row the primary-key cells as its identity.
- Slice 3 (2026-10-19), details checked natively that D3 does not state:
  - SQLite looks a collation name up only where it uses the collation, and its query
    planner decides some of those uses: `SELECT x COLLATE foo` runs, and
    `WHERE 'a' COLLATE NOCASE = x COLLATE foo` fails. So an unknown name is SQLite's prepare
    error in a column definition and an index term only, and the restriction
    `unknown-collation` in any other expression.
  - The equality of `USING` and `NATURAL` has the collation of the left-most left column of
    the name: SQLite gives a coalesce of left columns the collation of its first argument,
    and a column always has a collation.
  - An `ON CONFLICT` target without `COLLATE` matches a key of any collation; `COLLATE` in a
    target stays a frontend refusal.

## Consequences

- **Catalog and Syntax grow.**
  - Index terms, filters, CHECK constraints, collations, generated columns and two table
    flags join the catalog and the Syntax IR.
  - The codec, the structural record and the generated input modules change format
    version once per slice that adds a field.
  - Approved files that build catalog values by hand (`examples/`) change when a field
    has no default value.
- **Comparisons carry a collation.** Every comparison and sort carries a collation. A
  model without collations keeps today's behaviour and kernel cost.
- **One unique-key function** replaces the three paths for the primary key, UNIQUE
  constraints and unique indexes.
- **Row order of `WITHOUT ROWID` tables** is a new invariant of `Table.Valid`, with its
  proof in the write path.
- **The measured gain is an upper bound,** about 500 cases of corpus v5. Most of the
  other schema-feature cases need foreign-key enforcement or `DROP` first.

## Alternatives considered

- **Admit the features and ignore their semantics**, for example accept COLLATE and
  compare with `BINARY`. Rejected: native SQLite gives other answers, and the
  conformance suite would show disagreements instead of restrictions.
- **Collations decided at execution**, from the values compared. Rejected: SQLite
  decides them at prepare time from the expression forms, and resolution already has
  those forms.
- **A separate structure for `WITHOUT ROWID` tables.** Rejected: every write and query
  would need two paths. One flag, the key order and a rowid field that is 0 keep one
  path.
- **Generated columns computed on each read** (`VIRTUAL`). Rejected for the model: the
  values are the same, and stored values keep reads simple. The two kinds differ only
  in what SQLite allows (`ADD COLUMN` of a `STORED` column) and in storage, which the
  model does not observe.

## Not decided here

- **Foreign keys.** Enforcement (`PRAGMA foreign_keys`), `foreign_key_check` and the
  actions of `ON DELETE` and `ON UPDATE` need nested writes. They get their own ADR,
  with triggers. This ADR admits only an inert `REFERENCES` clause (D2).
- **`AUTOINCREMENT`**, which needs the `sqlite_sequence` table, and
  **`CREATE TABLE ... AS SELECT`**, which needs a query as a statement source.
- **User-defined collations** and the `ICU` collations. The model has none.

## Owner decisions

Decided on 2026-10-19:

1. **Collations stay in this ADR** (D3, slice 3). Collations bring in 55 clean cases and
   appear in 330 cases in all.
2. **`DROP INDEX` and `DROP TABLE` join this ADR** as slice 7 (D7), for tables and
   indexes that no trigger, view or enforced foreign key refers to. DROP is the only
   other blocker of 110 schema-feature cases.
3. **An inert `REFERENCES` is admitted** under profiles that do not enforce foreign keys
   (D2, slice 4).
