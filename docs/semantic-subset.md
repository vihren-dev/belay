# Supported subset

The verifier handles SQL in three layers (ADR 0008). The frontend maps the pinned
SQLite syntax tree to statement syntax. Lean resolves the syntax against the
catalog. The execution semantics runs the resolved statements. Each layer has a
boundary of its own.

## Statement syntax

The frontend maps these statements, and refuses every other statement as
`UNSUPPORTED` at its byte range:

- `CREATE TABLE` with column definitions (name, declared type text, `NOT NULL`,
  `PRIMARY KEY` with its sort order, `UNIQUE`, and `DEFAULT` with a literal, a
  signed number, a time keyword or a name) and table `PRIMARY KEY` and `UNIQUE`
  constraints over plain column names;
- `CREATE [UNIQUE] INDEX` over plain column names;
- `ALTER TABLE … ADD [COLUMN]` with one column definition;
- `BEGIN` (optionally `DEFERRED`), `COMMIT`/`END` and `ROLLBACK`, optionally with
  `TRANSACTION`;
- `INSERT INTO table [(columns)] VALUES` with one or more rows;
- `UPDATE table SET column = value, … [WHERE expression]`;
- `SELECT columns FROM table [WHERE …] [GROUP BY …] [ORDER BY … [ASC|DESC]]
  [LIMIT n [OFFSET m]]` from one table, whose result columns are `*` or
  expressions with an optional alias (ADR 0012, slice 1).

Expressions are `NULL`, numeric, string and blob literals, the time keywords,
names, unary `-` and `+`, and `=`. Inside a `SELECT`, they may also be the other
comparisons, `IS` and `IS NOT`, `AND`, `OR`, `NOT`, `IS NULL` and its forms,
parentheses, `COUNT(*)`, and `COUNT`, `MIN` and `MAX` of one argument. Named
constraints, collations, `CHECK`, `REFERENCES`, generated columns, conflict
clauses, `RETURNING`, `UPSERT`, `WITH`, `FROM` in writes, sort modifiers in keys,
partial and expression indexes, `IF NOT EXISTS`, `TEMP`, schema names, table
options, `AS SELECT`, views, triggers, virtual tables, `EXPLAIN`, `PRAGMA`,
compound `SELECT`, `DISTINCT`, `HAVING`, joins, table aliases, `table.*`,
`NULLS FIRST` and `NULLS LAST`, and other functions are refused. Names keep
their case as written; quotes are removed as SQLite removes them. Numeric literals
and declared types keep their text.

Every command retains its original half-open UTF-8 byte span; semicolons in names
and trigger bodies cannot split commands. The CLI requires at least one migration
statement. An empty starting schema is allowed.

## Schema description

`schema.sql` describes the starting catalog. It may contain only `CREATE TABLE`
and `CREATE INDEX`, in an order that SQLite can run: an index follows its table.
A schema statement that SQLite refuses to prepare, for example a second table
with the same name, is `INPUT_ERROR` with SQLite's message. The description may
contain keys, `NOT NULL`, the `CURRENT_TIMESTAMP` default, indexes and the exact
native `sqlite_stat1` and `sqlite_stat4` tables. Other defaults, other reserved
names and `INTEGER PRIMARY KEY` rowid aliases are model restrictions.

## Resolution

Lean's `resolve` follows SQLite's name resolution: ASCII-only case folding, one
namespace for tables and indexes, SQLite's affinity rules on the declared type
text, column positions, defaults of omitted INSERT columns, and SQLite's
numeric-literal conversion. Limits come from the execution profile. A statement
that SQLite refuses to prepare becomes its prepare error at its position, for
example `no such table`, `table already exists`, `duplicate column name` or
`too many columns`. The script stops there under autocommit and keeps the
successful prefix. Predicting an error alone never establishes `VIOLATED`.

SQL that SQLite accepts but the model does not describe is a model restriction:
the whole request is `UNSUPPORTED` at the byte range of the refused node. In the
migration these are, among others: `CREATE INDEX`; `CREATE TABLE` with
constraints or defaults; `ADD COLUMN` with a constraint or default; rowid column
names; REAL values; time values; values that the column affinity would convert;
column references in values; a filter other than `column = integer` on an
INTEGER, NUMERIC or BLOB column; a column named twice; writes to a table with a
unique key over a TEXT or REAL column; and key values other than integers and
NULL. In a `SELECT`: a comparison whose affinity rule would convert a value; a
value used as a condition; an aggregate inside an expression; a result column
outside `GROUP BY` in an aggregate query; `ORDER BY` terms of an aggregate query
other than result column numbers and aliases; a result column alias in `WHERE`
or inside an `ORDER BY` expression; a query of SQLite's own tables, such as
`sqlite_schema`; and `LIMIT` or `OFFSET` other than
an integer literal, or a negative `OFFSET`. Each restriction message says what to
change.

## Execution

The execution semantics runs the resolved statements on a database keyed by
catalog position. Transactions and data changes are supplied as SQL, not implied
by a profile. INSERT appends its rows with ordinary automatic rowid allocation;
UPDATE sets its assignments in each row that its filter selects. A `SELECT`
changes nothing; its result rows follow ADR 0012: rows in rowid order, the
`WHERE` filter with three-valued logic, groups, result columns, a stable sort by
the `ORDER BY` terms with SQLite's comparison of values, then the window. Literal writes
have checked data-domain obligations: existing key cells and filter cells must
be integers or NULL, existing constraints must hold, and the random-search branch
at the maximum rowid is outside the admitted domain. New NOT NULL and uniqueness
violations are modeled statement failures; unsupported coercions or comparison
classes are not invented SQLite error outcomes.

An error inside a transaction does not imply rollback. The model distinguishes
the connection-visible state from its committed snapshot when a transaction
remains open. A final uncommitted transaction cannot be reported as a committed
successful migration. Resource, concurrency and crash failures remain outside
the fixed execution assumptions. See [execution profiles](execution-profile.md)
and [profile input](profile-inputs.md).

`SqlInputs.lean` contains only literal statement syntax, resolved statements and
the resulting catalog. The driver seals it separately from candidate definitions,
and the gates resolve the record again to check it. A resolution result is not
proof acceptance or evidence of native execution.

The [Atuin example](../examples/atuin/README.md) supplies only the upstream
nullable shell-column ALTER payload and proves recovery of the approved old
histories. It does not use transaction or literal DML wrappers; SQLx catalog
maintenance and invocation remain trusted and outside the verified payload.
