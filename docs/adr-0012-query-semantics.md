# ADR 0012: Query semantics in the SQLite model

Date: 2026-10-13. Status: ACCEPTED on 2026-10-13.
Audience: designers and reviewers.
Related: [ADR 0005](adr-0005-conformance-corpus-scale.md),
[ADR 0006](adr-0006-model-boundary-and-execution-levels.md),
[ADR 0008](adr-0008-syntax-and-resolution-in-lean.md),
[ADR 0011](adr-0011-product-trust-and-development-integrity.md),
[conformance format v1](conformance-format-v1.md).

## Context

ADR 0008 moved statement syntax and name resolution into Lean. Its step 3 adds
`Syntax` and `resolve` for the query and expression syntax of the reference
workload of ADR 0005, section 1.3: `SELECT` with `ORDER BY`, `LIMIT` and
`GROUP BY`; `COUNT`, `SUM`, `AVG` and `MAX`; `COALESCE` and `CAST`; `RETURNING`;
`JOIN`; `ON CONFLICT`; time and JSON functions; and `REAL` arithmetic.

Resolution alone does not make this SQL useful. The frontend refuses syntax that
the model cannot run, and the model cannot run a query today:

- ADR 0006 reserves three levels for this work, "Values", "Expressions" and
  "Queries", but defines none of them. The model compares values only as integer
  equality, for unique keys and for the `WHERE column = integer` filter of an
  `UPDATE`.
- ADR 0005, section 3.1, defines how the conformance suite compares the outputs
  of a statement: result shape, typed rows, tie groups for `ORDER BY`, and the
  rules for `LIMIT` and `OFFSET` that cut a tie group. The judge implements
  these rules (`judge/outputs.py`). The model produces outputs only for literal
  `INSERT` and `UPDATE`: their change counts.

This ADR defines the semantics of the three levels, the order in which the
workload SQL enters the model, and the first slice in detail.

## Decision

### Levels

The levels of ADR 0006 get these responsibilities. Each level uses only the
levels above it in this list.

| Level | Reads and produces | First slice |
| --- | --- | --- |
| Values | Two values to an ordering; a value to a truth value | Comparison with affinity, storage-class order and BINARY collation |
| Expressions | One row to a value | Literals, columns, comparisons, `AND`, `OR`, `NOT`, `IS`, `IS NULL` |
| Queries | One table to a result: column names and rows | One table, `WHERE`, `GROUP BY`, `ORDER BY`, `LIMIT`, `OFFSET`, `COUNT`, `MIN`, `MAX` |
| Statements | A query statement to an output, with no state effect | `SELECT` in a script |

The levels are model code in `Belay.Sqlite`, beside the statement semantics.
They do not depend on the verification application (ADR 0006).

### Syntax and resolution

The layering of ADR 0008 applies without change.

- **Syntax.** `Syntax.Statement` gets a `select` constructor. `Syntax.Expr` gets
  binary and unary operators, `IS`, `IS NULL`, function calls with a name and
  arguments, and `*` as a function argument. Each result column keeps its source
  text, because SQLite uses that text as the column name (see "Output").
- **Resolution.** `resolve` turns a `select` into `Resolved.query`. It folds
  names, puts each column reference at its table position, decides if the query
  is an aggregate query, and checks the rules that SQLite checks while it
  prepares the statement. A violated rule is a prepare error with its message
  format; SQL that the model does not describe is a model restriction (R7).
- **Specification.** Each new rule of `resolve` gets a declarative statement and
  a proof that `resolve` meets it, as ADR 0008 requires.

The prepare errors of the first slice are `no such column: %s`,
`misuse of aggregate function %s()` (an aggregate in `WHERE`, or nested
aggregates), `%r ORDER BY term out of range - should be between 1 and %d`, and
`%r GROUP BY term out of range - should be between 1 and %d`.

### Values

The comparison follows "Comparison Expressions" and "Sort Order" of the pinned
`datatype3.html`. Each rule names its requirement identifier.

- **Storage classes.** NULL is less than every other value (R-08551-61977). An
  INTEGER or REAL is less than any TEXT or BLOB (R-14505-63184). A TEXT is less
  than a BLOB (R-64324-28127).
- **Numbers.** An INTEGER and a REAL compare by their exact numeric values. The
  model does not convert the integer to a double: a 64-bit integer and the
  nearest double can compare as unequal in SQLite.
- **Text.** The BINARY collation compares the UTF-8 bytes (R-53528-47027).
  Other collations are model restrictions in the first slice.
- **Affinity before a comparison.** The rules of R-10393-27560, R-58138-64688
  and R-29161-32953 apply to the operands of `=`, `<`, `<=`, `>`, `>=`, `<>`,
  `IS` and `IS NOT`. They use the affinity of a column reference and the absence
  of affinity of a literal, which `resolve` already knows.
- **NULL.** `=`, `<` and the other comparisons give NULL when an operand is NULL.
  `IS` and `IS NOT` treat two NULLs as equal (R-24731-45773).
- **Truth value.** `WHERE` keeps a row when its expression is true: a non-zero
  number. In the first slice, a `WHERE` expression is a comparison, a logical
  operator or `IS NULL`, whose value is 0, 1 or NULL. A bare column or literal
  as a condition, which needs SQLite's text-to-number conversion, is a model
  restriction.

The comparison is one Lean function. Its proofs show that it is a total
preorder on values, which the sort and the grouping need.

### Expressions

An expression evaluates against one row of one table, to a value. The first
slice has literals, column references, the six comparison operators, `IS`,
`IS NOT`, `IS NULL`, `IS NOT NULL`, `AND`, `OR` and `NOT`, with SQLite's
three-valued logic. Arithmetic, `CAST`, `COALESCE` and other functions are later
slices. No expression of the first slice can fail at run time.

### Queries

A query of the first slice reads one table and runs these steps in order:

1. **Source.** The rows of the table, in rowid order.
2. **Filter.** The rows for which the `WHERE` expression is true (R-60775-64916).
3. **Groups.** For an aggregate query (R-20637-43463), the rows are put in groups
   by the values of the `GROUP BY` terms, with the comparison above. Without
   `GROUP BY`, all rows form one group, also when there are no rows
   (R-02223-49279).
4. **Projection.** One output row per row, or per group of an aggregate query.
   `COUNT(*)` counts the rows of a group (R-13776-21310), `COUNT(x)` the rows
   where `x` is not NULL (R-34280-42283). `MIN` and `MAX` give the least and the
   greatest non-NULL value (R-16028-39081, R-52585-35928), or NULL when there is
   none.
5. **Order.** With `ORDER BY`, a stable sort by the terms, each ascending by
   default (R-18705-33393) or descending, with NULL first in ascending order
   (R-12881-55998).
6. **Window.** `OFFSET` rows are skipped and at most `LIMIT` rows are kept.

The model returns its rows in one fixed order: the rowid order of the source,
sorted stably by the `ORDER BY` terms. SQLite gives no order for rows without
`ORDER BY`, or for rows that tie under it. ADR 0005 compares such rows as
multisets and tie groups, and it compares a `LIMIT` or `OFFSET` that cuts a tie
group as a submultiset. So the fixed order of the model is not a claim about
SQLite's order, and the comparison does not depend on it.

These are model restrictions in the first slice: more than one table, `JOIN`,
subqueries, `DISTINCT`, compound `SELECT`, `HAVING`, window functions, a column
in an aggregate query that is not in `GROUP BY` and not in an aggregate (SQLite's
"bare column" rule), `LIMIT` and `OFFSET` that are not integer literals, and a
negative `OFFSET`.

### Output

A query statement produces a `StatementOutput` (conformance format v1): the
column names, the rows, and no change count. The column name of a result column
is its `AS` alias. Without an alias, it is the column name for a bare column
reference, as written in the table definition; otherwise it is the source text of
the expression, as written. These are the rules of the pinned release for the
first slice. A case where they would differ from SQLite's name is found by the
conformance suite.

### Statements and the verification target

A `SELECT` in a script has no effect on the database. The execution semantics
returns the incoming state and the output. The script semantics, positions,
first-error stopping and transactions of ADR 0006 do not change. Because a
query changes no state, `VerificationConditions` keeps its formulas: a migration
that contains a `SELECT` is verified about its state effects, as before. A
`SELECT` that fails at prepare time stops the script, as other prepare errors
do. The trust boundary does not change: resolution and evaluation are model
code that the kernel checks through the agent's proof, and the gate compares the
resolved script as before.

### Testing

The rules are checked in the ways ADR 0008 uses for resolution:

- **Conformance.** Corpus records of version 3 and later carry statement
  outputs. Once the model produces outputs for queries, the judge compares them
  with the rules of ADR 0005, section 3.1. Cases that agree become `mustAgree`
  claims in an owner-approved judge change (ADR 0011).
- **Authored coverage cases.** For each rule: a case where it applies, a
  neighbor where it does not, and boundary values: integer and real ties,
  storage-class order between NULL, numbers, text and blobs, NULL in each
  operand of each operator, an empty table with and without `GROUP BY`, a
  `LIMIT` that cuts a tie group, and each prepare error.
- **Mutants.** Each must change the verdict of a case: NULL equal to NULL under
  `=`; an integer compared with a real through a double; text compared without
  case; `DESC` ignored; NULL last in ascending order; `COUNT(x)` counting NULL;
  `MIN` over NULL; an empty table giving no row for `COUNT(*)`; `LIMIT` one too
  high; `OFFSET` ignored; and each prepare error removed.
- **Proofs.** The filter keeps exactly the rows whose condition is true. The
  result of `ORDER BY` is sorted by the terms and is a permutation of its input.
  The window has the length that `LIMIT` and `OFFSET` give. `COUNT(*)` of a
  group equals its number of rows.

### Slices

Each slice is one task with the work of ADR 0008: syntax, resolution with its
specification, semantics, conformance cases, mutants and a judge change.

1. **Single-table queries.** As this ADR describes.
2. **Numbers.** `REAL` and integer arithmetic, with SQLite's integer overflow to
   REAL; `CAST`; `COALESCE`; `SUM` and `AVG`, with the `integer overflow` error
   of `SUM` and the summation of the pinned release.
3. **Writes with output.** `RETURNING` (compared as a multiset, ADR 0005), and
   `INSERT` and `UPDATE` with expressions instead of literals.
4. **Joins.** Inner and left joins of tables, with qualified names and the
   `ambiguous column name` error.
5. **Conflicts.** `ON CONFLICT` of `INSERT`.
6. **Functions.** Time and date functions, which need the controlled clock of
   ADR 0005, section 3.2, and the JSON functions `json_extract` and `json_each`.

The order puts the shared value and expression work first and the functions
with the most separate rules last. A slice may change the order of later slices
when its evidence shows a reason.

## Consequences

- **Model.** The Values, Expressions and Queries levels of ADR 0006 exist, with
  proofs. Later slices extend them instead of adding parallel evaluators.
- **Frontend.** The mapping to `Syntax` grows by one constructor per form, and
  keeps the source text of each result column. It still refuses every form that
  the model does not run.
- **Conformance.** Queries in the frozen corpora move from `MODEL_UNSUPPORTED`
  to compared, slice by slice. A disagreement found this way is a model bug or a
  wrong rule of this ADR; each one is fixed before its cases are claimed.
- **Verification.** Migrations that contain queries become admissible; their
  verification targets are unchanged.
- **Cost.** Kernel proofs of conformance cases with queries evaluate the query
  in the kernel. Cases stay small, as for resolution.

## Alternatives considered

**Evaluate queries in Python.** Rejected for the reasons of ADR 0008: it would
be trusted code with no formal statement, outside the model that the proofs use.

**Use SQLite as the oracle at verification time.** Rejected: the verifier does
not run the application's SQL, and the model must say what a query returns for
every admitted database, not for one recorded state.

**All workload SQL in one step.** Rejected: the value and expression rules are
shared by all later forms, and each form has rules of its own. One step would
delay the first evidence and make each review larger.

**Model SQLite's order of rows without `ORDER BY`.** Rejected: SQLite does not
specify it, it depends on the query plan, and ADR 0005 already compares such
results without it.

## Not decided here

- Collations other than BINARY, and the `COLLATE` operator.
- The text-to-number conversion of a bare value used as a condition.
- Subqueries, compound `SELECT`, `DISTINCT`, `HAVING` and window functions.
- Triggers and foreign-key actions, which run statements inside statements and
  need the fuel and transaction rules that ADR 0006 asks for.
