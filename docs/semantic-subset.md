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
- `RETURNING columns` after `INSERT … VALUES` and `UPDATE`, with result columns as in
  `SELECT`, over each written row (slice 3a); an aggregate is SQLite's prepare error,
  and a rowid name in `RETURNING` is a model restriction;
- `SELECT columns FROM table [WHERE …] [GROUP BY …] [ORDER BY … [ASC|DESC]]
  [LIMIT n [OFFSET m]]` from one table, whose result columns are `*` or
  expressions with an optional alias (ADR 0012, slice 1).

Expressions are `NULL`, numeric, string and blob literals, the time keywords,
names, unary `-` and `+`, and `=`. Inside a `SELECT`, they may also be the other
comparisons, `IS` and `IS NOT`, `AND`, `OR`, `NOT`, `IS NULL` and its forms,
parentheses, `COUNT(*)`, `COUNT`, `MIN`, `MAX`, `SUM` and `AVG` of one argument, the arithmetic
operators `+`, `-`, `*`, `/` and `%`, unary `-` and `+` of any expression,
`CAST(expression AS type)`, and `COALESCE` of two or more arguments (ADR 0012,
slice 2). In a write, a `VALUES` item, a `SET` value and the value of a
`column = value` filter may be any of these expressions that names no column:
resolution computes its value (slice 3a). The value is then stored as SQLite
stores it in a column of that affinity (slice 3b): for example, the text `'12'`
becomes the integer 12 in an INTEGER column, and an integer becomes text in a TEXT
column. A REAL value can be stored in any column that is not part of a unique key. Named
constraints, collations, `CHECK`, `REFERENCES`, generated columns, conflict
clauses, `UPSERT`, `WITH`, `FROM` in writes, sort modifiers in keys,
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
names; time values; column references in values; a filter other than `column = integer` on an
INTEGER, NUMERIC or BLOB column; a column named twice; writes to a table with a
unique key over a TEXT or REAL column; and key values other than integers and
NULL. In a `SELECT`: a comparison whose affinity rule would convert a value; a
column, literal, `COALESCE`, or `CAST` to TEXT or BLOB used as a condition; an aggregate inside an expression; a result column
outside `GROUP BY` in an aggregate query; `ORDER BY` terms of an aggregate query
other than result column numbers and aliases; a result column alias in `WHERE`
or inside an `ORDER BY` expression; a query of SQLite's own tables, such as
`sqlite_schema`; `SUM` in a query with `GROUP BY` and `LIMIT` or `OFFSET`; and
`LIMIT` or `OFFSET` other than
an integer literal, or a negative `OFFSET`. Each restriction message says what to
change.

### Restriction registry

Each model restriction has a stable id. A rejection reports it in the field
`restriction`, next to its message, and the conformance predictions record it too.
The registry is `RestrictionKind` in
`packages/belay-sqlite/Belay/Sqlite/Resolution/Restrictions.lean`, with the ids and
messages in `RestrictionText.lean`. Every id has one row in this table;
`tests/restriction_registry_test.py` checks that the table and the registry list the
same ids. `conformance/restriction_examples.py` has, for every id, a schema and a
migration that the resolver refuses with that id, and a test runs each one. The
exception is `returning-target`: the frontend refuses its example (DELETE ...
RETURNING) before resolution, and the test checks that refusal. Syntax
that the frontend refuses before resolution, such as `DISTINCT` or
an UPSERT, has no id. `just restriction-costs` counts, for each id and for each kind
of frontend refusal, the cases of the claimed corpora that it keeps out of scope.

| Id | Restriction | Introduced by |
| --- | --- | --- |
| `schema-statement` | A schema contains only CREATE TABLE and CREATE INDEX statements | ADR 0008 |
| `engine-table` | Engine-managed tables other than sqlite_stat1 and sqlite_stat4 are not modeled | ADR 0008 |
| `rowid-column-name` | Column names `rowid`, `_rowid_` and `oid` are not modeled | ADR 0008 |
| `rowid-alias` | INTEGER PRIMARY KEY rowid aliases are not modeled | ADR 0008 |
| `create-table-constraints` | Constraints and defaults in a CREATE TABLE that runs are not modeled | ADR 0008 |
| `unmodeled-default` | Only the `CURRENT_TIMESTAMP` default is modeled | ADR 0008 |
| `create-index-runs` | A CREATE INDEX that runs is not modeled | ADR 0008 |
| `add-column-constraint` | Only a nullable column without a default can be added | ADR 0008 |
| `time-value` | Time values are not modeled | ADR 0008 |
| `key-affinity` | Unique keys over TEXT or REAL columns are not modeled | ADR 0008 |
| `key-value` | Only integer and NULL values are modeled in unique key columns | ADR 0008 |
| `column-in-value` | Column references in values are not modeled | ADR 0012 slice 3a |
| `insert-column-twice` | A column named twice in INSERT is not modeled | ADR 0008 |
| `update-column-twice` | A column assigned twice in UPDATE is not modeled | ADR 0008 |
| `literal-comparison` | A comparison of two literals is not modeled | ADR 0008 |
| `non-integer-filter` | Only an integer equality with an INTEGER, NUMERIC or BLOB column is modeled | ADR 0008 |
| `filter-form` | Only a column equality filter is modeled | ADR 0008 |
| `rowid-in-returning` | A rowid in RETURNING is not modeled | ADR 0012 slice 3a |
| `returning-target` | RETURNING is modeled only on INSERT and UPDATE | ADR 0012 slice 3a |
| `system-table` | Queries of SQLite's own tables, such as `sqlite_schema`, are not modeled | ADR 0012 slice 1 |
| `unmodeled-function` | Only `COUNT(*)`, `COUNT`, `MIN`, `MAX`, `SUM` and `AVG` of one argument, and `COALESCE` of two or more arguments are modeled as functions | ADR 0012 slices 1 and 2 |
| `aggregate-in-expression` | An aggregate inside an expression is not modeled | ADR 0012 slice 1 |
| `alias-in-expression` | A result column alias inside WHERE or an ORDER BY expression is not modeled | ADR 0012 slice 1 |
| `value-as-condition` | A value used as a condition is not modeled | ADR 0012 slice 1 |
| `mixed-affinity-comparison` | A comparison of columns with different kinds of affinity is not modeled | ADR 0012 slice 1 |
| `text-to-number` | A text value compared with a numeric column would be converted to a number | ADR 0012 slice 1 |
| `number-to-text` | A number compared with a TEXT column would be converted to text | ADR 0012 slice 1 |
| `group-by-term` | Only a column name or a result column number is modeled in GROUP BY | ADR 0012 slice 1 |
| `bare-column` | A result column outside GROUP BY in an aggregate query is not modeled | ADR 0012 slice 1 |
| `aggregate-order-by` | An aggregate query is modeled with ORDER BY result column numbers or aliases only | ADR 0012 slice 1 |
| `window-value` | Only an integer literal is modeled as LIMIT or OFFSET | ADR 0012 slice 1 |
| `negative-offset` | A negative OFFSET is not modeled | ADR 0012 slice 1 |
| `windowed-group-sum` | SUM in a grouped query with LIMIT or OFFSET is not modeled, because SQLite may stop before an overflowing group | ADR 0012 slice 2 |

## Execution

The execution semantics runs the resolved statements on a database keyed by
catalog position. Transactions and data changes are supplied as SQL, not implied
by a profile. INSERT appends its rows with ordinary automatic rowid allocation;
UPDATE sets its assignments in each row that its filter selects. A `SELECT`
changes nothing; its result rows follow ADR 0012: rows in rowid order, the
`WHERE` filter with three-valued logic, groups, result columns, a stable sort by
the `ORDER BY` terms with SQLite's comparison of values, then the window.
Arithmetic, `CAST` and the conversions between text and numbers follow the pinned
SQLite source step by step: integer arithmetic while the result fits in 64 bits,
else double arithmetic; NULL for a division by zero or a NaN result; SQLite's own
text-to-REAL conversion and its 15-digit text of a REAL, which are not correctly
rounded; and `SUM` and `AVG` with SQLite's summation. A `SUM` that overflows the
64-bit integers stops the query with `integer overflow`, unless a later REAL input
makes the sum approximate. Literal writes
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
