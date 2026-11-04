# ADR 0030: Conditional table and index creation, and grouping by expressions

Date: 2026-11-04. Status: PROPOSED (owner decisions below are open).
Implementation: three slices (D8), each with its own task file, as local commits, after the
owner accepts this ADR.
Audience: designers and reviewers.
Related: [ADR 0012](adr-0012-query-semantics.md) ("Queries": groups, the fixed order of the
model), [ADR 0014](adr-0014-schema-features.md) (D3: the collation of a `GROUP BY` term),
[ADR 0018](adr-0018-surface-sql.md) (D3: grouped and bare expressions; D6: the results that
SQLite may give), [ADR 0024](adr-0024-connection-state-and-random-values.md) (the counters
and random values in `GROUP BY`), [ADR 0026](adr-0026-semantic-proof-boundaries.md) (D1: the
grouping premises of the query laws), [ADR 0011](adr-0011-product-trust-and-development-integrity.md)
(claims and the judge). Issue: [#301](https://github.com/vihren-dev/belay/issues/301).

## Overview

Issue #301 asks for the specification of two forms that a consumer's migrations and queries
use and that the model refuses:

- `CREATE TABLE IF NOT EXISTS` and `CREATE [UNIQUE] INDEX IF NOT EXISTS`. The translation
  refuses both with `IF NOT EXISTS is not modeled; remove it`. `CREATE VIEW IF NOT EXISTS` and
  `CREATE TRIGGER IF NOT EXISTS` are already in the model.
- `GROUP BY` with a written expression, such as `GROUP BY date(created_at, 'unixepoch')` in the
  consumer's queries `GetUsageByDay` and `GetRecentActivity`. Resolution refuses it with the
  restriction `group-by-term`, or with `unmodeled-function` for a call with one argument.

This ADR gives both forms SQLite 3.51.0's meaning. It does not remove the clause from the
text, and it does not make a special case of `date`.

The research for the second form found a defect in the model that already exists: the value
that a group gives for a column, or for an expression of columns, is not always SQLite's. The
model reads such values from the first row of the group in rowid order. SQLite reads them from
the row with the minimum or maximum of the last `min()` or `max()` call of the query, and
from the first row that it reads when the query has no such call, in an order that its query plan chooses. Where the
rows of a group compare as equal but differ, for example `'a'` and `'A'` under `NOCASE`, or
`1` and `1.0`, the model and SQLite give different rows today. Grouping by expressions makes
such groups more frequent, so this ADR decides the rule for both (D5, owner decision 2).

## Context

Measured on this tree (main at `528ea92`) on 2026-11-04. The facts about SQLite come from the
dev shell's `sqlite3` 3.51.0, one statement per line, and from the sources of the pinned
release (`src/build.c`, `src/expr.c`). The model's predictions come from the built packages of
the same model, evaluated with `Database.run` (`#eval`). The verdicts come from the verdict
job of this model's tree.

### Conditional creation: the code

- **Syntax.** The parser gives the `ifnotexists` node in each CREATE header, with no children
  when the clause is absent. `Syntax.Statement.createView` and `createTrigger` have a field
  `ifNotExists : Bool` (`Resolution/Syntax.lean`). `createTable` and `createIndex` have none.
- **Translation.** `createTable` refuses the clause with `absent header[3]! "IF NOT EXISTS"`
  (`Translation/Tables.lean`), and `createIndex` with `absent parts[3]! "IF NOT EXISTS"`
  (`Translation/Schema.lean`). `absent` (`Translation/Shapes.lean`) makes a frontend refusal
  `IF NOT EXISTS is not modeled; remove it` with no restriction id. The translation also
  refuses `TEMP`, a schema name and `AS SELECT` in `CREATE TABLE`.
- **The precedent of views and triggers.** The translation only records the flag. The resolver
  decides: when the name is taken by an object that makes the statement a no-op,
  `resolveCreateView` and `resolveCreateTrigger` give `.drop []` and `catalog.drop []`, which
  keep the catalog and the rows. The step of `.drop []` keeps the database, the output is
  `.done 0`, and the counters do not change (the theorem `counters` in
  `tests/surface/ClaimsViewCreate.lean`).
- **Resolution order.** `resolveCreateTable` (`Resolution/Definitions.lean`) checks the reserved
  name first, then the name: a table gives `table %s already exists`, a view
  `view %s already exists`, an index `there is already an index named %s`. Only then does it
  read the column definitions, the constraints and the table options. `resolveCreateIndex`
  checks the table (`.noSuchTable`, `.viewNotIndexed`), the reserved table name
  (`.tableMayNotBeIndexed`), the reserved index name, then the name: a table or a view gives `there is already a table named %s`, an index `index %s already exists`. Only
  then does it read the terms and the filter. `Catalog.find` searches tables, views and
  indexes in one namespace with ASCII case folding; triggers have their own.
- **Execution.** The step of `.createIndex` checks a `UNIQUE` index against the existing rows
  (`LiteralData.uniqueRows`, `Execution.lean`) and fails with a constraint violation.
- **Proofs.** These statements are about the two resolvers and assume, by their form, that a
  CREATE never resolves to `.drop []`:
  `resolveCreateTable_step`, `resolveCreateIndex_step` (`Resolution/NamesSpec.lean`),
  `resolveCreateTable_applyCatalog`, `resolveCreateIndex_applyCatalog`
  (`Resolution/ApplyCatalogSpec.lean`), `resolveCreateTable_named`, `resolveCreateTable_used`
  (`Resolution/PrepareSpec.lean`), `resolveCreateIndex_named`, `_missing`, `_used`
  (`Resolution/DefinitionSpec.lean`), `resolveCreateTable_form` and
  `runScriptStep_createTable_failed` (`SchemaFailureLaws.lean`), `resolveCreateTable_single`,
  `resolveCreateIndex_single` (`Resolution/ResolveStatementSingleWrites.lean`), and
  `CreateIndexConditions` with `runScriptStep_createIndex_ok_iff`
  (`CreateIndexSuccessLaws.lean`) and their public forms `Script.createIndex_allOk_iff` and
  `Succeeds.iff_createIndex` (`packages/belay/Belay/Sqlite/CreateIndexSuccess.lean`). The
  trigger laws `createTrigger_resolution_cases` and `createTrigger_step`
  (`CreateTriggerStep.lean`) show the pattern: they assume `ifNotExists = false`.
- **Documentation.** `docs/semantic-subset.md` lists `IF NOT EXISTS` among the refused forms
  and documents it for views and triggers. The registry of restrictions has no entry for it.

### Conditional creation: SQLite

From `sqlite3StartTable` and `sqlite3CreateIndex` (`build.c`) and probes:

| Statement | Name is free | Name is a table | Name is a view | Name is an index | Name is a trigger |
| --- | --- | --- | --- | --- | --- |
| `CREATE TABLE IF NOT EXISTS n ...` | creates, as without the clause | no-op | no-op | `there is already an index named n` | creates (separate namespace) |
| `CREATE [UNIQUE] INDEX IF NOT EXISTS n ON t(...)` | creates, as without the clause | `there is already a table named n` | `there is already a table named n` | no-op, whatever the existing index's table, terms or `UNIQUE` | creates |

- **The order of the checks.** For a table: the reserved name (`object name reserved for
  internal use: sqlite_x`, also for `sqlite_master` and `sqlite_sequence`), then the name. For
  an index: the table (`no such table: main.x`, `table sqlite_master may not be indexed`,
  `views may not be indexed`), then the reserved name, then the name. Every check after the
  name does not run when the statement is a no-op: SQLite stops building the statement
  (`pParse->pNewTable` is 0, and `sqlite3AddColumn`, `sqlite3AddPrimaryKey`,
  `sqlite3AddGenerated` and `sqlite3EndTable` return early). So these statements are no-ops
  on an existing table `t`: `CREATE TABLE IF NOT EXISTS t(a, a)`, `... t(a TEXT PRIMARY KEY
  AUTOINCREMENT)`, `... t(a, CHECK (nosuch > 0))`, `... t(a) WITHOUT ROWID`, `... t(a FOO)
  STRICT`, `... t AS SELECT nosuch FROM nosuch`. On an existing index `i`:
  `CREATE INDEX IF NOT EXISTS i ON u(nosuch)`, `... ON u(c) WHERE nosuch > 0`,
  `... ON u(random())`, `... ON u(c COLLATE nosuchcoll)`. A syntax error is still an error.
- **`UNIQUE`.** `CREATE UNIQUE INDEX IF NOT EXISTS i ON t(a)` over duplicate values of `a` is a
  no-op when `i` exists and fails with `UNIQUE constraint failed: t.a` (code 19) when it does
  not.
- **Effects of a no-op.** The schema, the rows, `PRAGMA schema_version`, `changes()`,
  `total_changes()` and `last_insert_rowid()` do not change. A no-op inside a transaction that
  rolls back leaves nothing. `sqlite3_stmt_readonly()` is false for it (R-50998-48593); the
  model has no such observation.
- **Names.** Names compare with ASCII case folding only: `CREATE TABLE IF NOT EXISTS "ä"`
  creates a table beside `"Ä"`, and `CREATE INDEX IF NOT EXISTS "iX"` is a no-op beside `"Ix"`.
- **Requirements.** R-33917-24086 (a table or view makes CREATE TABLE IF NOT EXISTS a no-op),
  R-16465-40078 (an existing index is still an error), R-16085-53730 (an existing index makes
  CREATE INDEX IF NOT EXISTS a no-op).

### Grouping: the code

- **Syntax.** Every `GROUP BY` item is a `Syntax.Expr` (`Statement.select`, `Subquery.groupBy`,
  `SelectBody.groupBy`). The resolved query has `Query.groupBy : List (Expr × Collation)`
  (`Resolution/QueryForm.lean`).
- **Resolution.** `resolveGroupTermTraced` (`Resolution/QueryAggregates.lean`) admits a column
  name, a column under one `COLLATE`, a qualified name, a parameter, and an integer literal or
  an alias that names a result column. An aggregate is SQLite's
  `aggregate functions are not allowed in the GROUP BY clause`, and a number out of range is
  `%s GROUP BY term out of range - should be between 1 and %d`. A call with no or one
  argument that is not an aggregate goes to `callIssue`, so `GROUP BY LOWER(artist)` is
  `unmodeled-function`. Every other form is the restriction `group-by-term` ("only a column
  name or a result column number is modeled in GROUP BY").
- **Expression grouping exists through result columns.** An alias or a number names a result
  column, and the grouping term is that column's resolved expression. So
  `SELECT b*a AS p, ... GROUP BY p` and `... GROUP BY 2` already work, and the consumer's query
  with `GROUP BY day` resolves (its run needs a clock: `date` of a column counts as a read of
  the clock, `DateFunction.readsNow` in `ClockReads.lean`).
- **Evaluation is generic.** `groups` (`QueryEval.lean`) evaluates each term on each row and
  puts two rows in one group when every term's values compare as equal under the term's
  collation (`Collation.compare`, `Value.compare`: NULLs are equal, an integer and a real are
  equal when their values are). The key expressions are part of `Query.keptExpressions`, so a
  key that can fail makes the query's fault `may` (`QueryRun.lean`).
- **Values of a group.** `records` (`QueryResults.lean`) evaluates each scalar result column,
  each `HAVING` condition and each `ORDER BY` expression on `group.headD []`: the first row of
  the group in the order of the source, which is rowid order for a table. `possibleResults`
  (`PossibleResults.lean`) gives the results that SQLite may give for the order of rows only;
  it does not vary the row of a group.
- **Grouped and bare expressions.** `Resolved.Expr.grouped` (`Resolution/QueryTerms.lean`)
  admits a result expression when it is one of the grouping terms, by structural equality, or
  when its parts are grouping terms, values or aggregates. A column outside the terms is the
  restriction `bare-column`.
- **Collation.** `Syntax.Expr.collationIn` gives an explicit `COLLATE`, else the column's
  collation, else `BINARY`. `docs/semantic-subset.md` says that `COLLATE` passes through unary
  plus and `CAST`.
- **Proofs.** The duplicate-key laws (`DuplicateKeyQuery.lean`, `FilteredDuplicateKeyQuery.lean`)
  take any resolved key, but their premise `GroupTermResolves` is an equation on
  `resolveGroupTerm` that an expression makes false today (`DuplicateKeyGroupTerm.lean`).
  `LiteralData.uniqueRows_of_column_groups` (`GroupKeyConflictLaws.lean`) needs a column key.
  `resolveGroupTerm_identifier_found` and `resolveGroupTerm_collate`
  (`Resolution/QueryAggregatesArms.lean`) and `resolveQueryBody_arm`
  (`Resolution/QueryBodyArms.lean`) follow the case split of the resolver. The count,
  aggregate and simple query laws require `groupBy = []` and do not change.

### Grouping: SQLite

From probes, and from `findOrCreateAggInfoColumn` and `analyzeAggregate` (`expr.c`):

- **Terms.** A `GROUP BY` item can be any expression (R-25883-55063) except an aggregate
  (R-63573-50730: `GROUP BY count(*)`, `GROUP BY max(a)+1` and an alias of an aggregate give
  `aggregate functions are not allowed in the GROUP BY clause`) and a window function
  (`misuse of window function row_number()`). A scalar subquery is allowed.
- **Names.** An identifier is a column of the sources first and a result alias second: with a
  column `a`, `SELECT b AS a ... GROUP BY a` groups by the column. An alias can be part of an
  expression: `SELECT a+1 AS k ... GROUP BY k+1`.
- **Numbers.** An integer literal is a result column number, also under parentheses or unary
  plus (`GROUP BY (1)`, `GROUP BY +1`). `GROUP BY 0`, `GROUP BY 3` with two result columns and
  `GROUP BY -1` give `1st GROUP BY term out of range - should be between 1 and 2`. `GROUP BY 1.0`,
  `GROUP BY '1'` and `GROUP BY 1+0` are constant expressions: one group.
- **Equality.** Each term is evaluated for each row (R-40855-36147). Values of different
  storage classes are distinct, except an integer and a real that are numerically equal
  (R-51848-06142). No affinity is applied (R-40564-64233): `GROUP BY a` puts `1` and `1.0` in
  one group and `'1'` and `x'31'` each in their own; `GROUP BY a+0` puts all four in one group,
  because `+` converts them. NULLs form one group.
- **Collation** (R-10470-30318). A column's collation passes through unary plus and `CAST`:
  with `c TEXT COLLATE NOCASE`, `GROUP BY c`, `GROUP BY +c` and `GROUP BY CAST(c AS TEXT)` put
  `'A'` and `'a'` in one group. A function call, `||` and arithmetic give `BINARY`:
  `GROUP BY c || ''` and `GROUP BY rtrim(c)` separate them. An explicit `COLLATE` decides:
  `GROUP BY b COLLATE NOCASE`, `GROUP BY (c || '') COLLATE NOCASE`, `GROUP BY c COLLATE RTRIM`.
- **Failures.** A term that fails for a row that the filter keeps fails the statement:
  `GROUP BY abs(-9223372036854775808 + a - a)` gives `integer overflow`, and the same query with
  `WHERE 0` gives no row and no error.
- **The row of a group.** SQLite's documentation says that a non-aggregate expression is
  evaluated against "a single arbitrarily chosen row from within the group" (R-62913-19830).
  The implementation is more exact, and the probes show three rules. With rows
  `(1.0,'a',1), (1,'A',3), (1,'A',2)` of `t(a, c TEXT COLLATE NOCASE, n)`:
  1. **No `min()` or `max()`.** Every value comes from the first row that SQLite reads:
     `SELECT c, count(*) ... GROUP BY c` gives `'a'`; `SELECT a+0, typeof(a) ... GROUP BY a+0`
     gives `1.0` and `real`. `HAVING` reads the same row.
  2. **One or more `min()` or `max()` calls** (in the result, in `ORDER BY` or in `HAVING`,
     also with other aggregates such as `count` and `sum`). The last distinct call decides, in
     the order result, `ORDER BY`, `HAVING`; a call that is written again counts at its first
     place. A column reference, also a grouped column and also under `COLLATE`, comes from the
     first row that gave that call's minimum or maximum: `SELECT c, max(n) ... GROUP BY c`
     gives `'A'`, `SELECT c || '', max(n) ... GROUP BY c` gives `'A'`,
     `SELECT c, min(n), max(n) ... GROUP BY c` gives `'A'`, and
     `SELECT c, max(n), min(n) ... GROUP BY c` gives `'a'`. With `min(n)` in `HAVING` and
     `max(n)` in `ORDER BY`, `SELECT c` gives `'a'`. The reason is in SQLite's code: each
     `min` or `max` step resets one shared register and sets it when the row is not a new
     extremum, and the columns load when the register is clear after all steps.
  3. **A result column that is a grouping term but not a column.** SQLite associates each
     `GROUP BY` term with the last result column that is the same expression, `COLLATE` included
     (`resolve.c` compares every result column and keeps the last match). That result column,
     when it is not a column under at most `COLLATE`, gives the term's value from the first row,
     also under rule 2. Other result columns are evaluated as usual:
     - `SELECT a+0, typeof(a), max(n) ... GROUP BY a+0` gives `1.0` and `integer`, so the two
       values come from different rows.
     - `SELECT a+0, a+0, max(n) ... GROUP BY a+0` gives `1` and `1.0`: only the second column
       is associated.
     - A part of a larger expression does not count: `SELECT (a+0)*1, max(n) ... GROUP BY a+0`
       gives `1`.
     - The comparison ignores the case of names (`A + 0` matches `a+0`) and does not reorder
       operands (`0 + a` does not match).
     - `COLLATE` must be the same on both sides. `SELECT CAST(c AS TEXT) COLLATE NOCASE, max(n)`
       with `GROUP BY CAST(c AS TEXT) COLLATE NOCASE` gives the first row's `'a'`, and
       `SELECT CAST(c AS TEXT), max(n)` with the same `GROUP BY` gives the maximum's `'A'`.
       The same holds with `COLLATE` in the result and not in the term.
- **The first row depends on the plan.** With rows `('A',3), ('a',1), ('a',2)` and an index on
  `n`, `SELECT c, count(*) FROM t GROUP BY c` gives `'A'`, and the same query with
  `WHERE n > 0` gives `'a'`, because SQLite reads the rows through the index.

### What the model gives today

Evaluated with `Database.run` on this tree:

| Query (rows of the facts above) | Model | SQLite 3.51.0 |
| --- | --- | --- |
| `SELECT c, max(n) FROM t GROUP BY c` | `'a'` | `'A'` |
| `SELECT c \|\| '', max(n) FROM t GROUP BY c` | `'a'` | `'A'` |
| `SELECT c FROM t GROUP BY c HAVING max(n) > 0` | `'a'` | `'A'` |
| `SELECT k, min(v) FROM u GROUP BY k`, rows `(1.0,'z'), (1,'a'), (1.0,'m')` | `1.0` | `1` |
| `SELECT c, count(*) FROM t WHERE n > 0 GROUP BY c`, the index case | `'A'` | `'a'` |
| `SELECT c, max(n), min(n) FROM t GROUP BY c` | `'a'` | `'a'` |

Every case of the claimed corpora agrees or is unsupported on this tree (the verdict has no
`DISAGREE`), so no claimed case exercises the first five rows. The `mustAgree` case
`collate-group-by-value` (`conformance/authored_collations.py`) groups `'a'` and `'A'` without
`min` or `max`, and agrees.

### The corpus

A scan of the migrations of all corpora finds `IF NOT EXISTS` in 10 cases and `GROUP BY` in
224. The candidates that issue #301 names, with their verdicts on this tree:

| Case | Today | What blocks it after this ADR |
| --- | --- | --- |
| v4, v5 `index-if-not-exists` (R-16085-53730) | unsupported: IF NOT EXISTS | nothing: promote |
| v4, v5 `index:index-6.1c:32` | unsupported: IF NOT EXISTS | nothing (the index exists in the initial snapshot): promote |
| v5 `index6:index6-14.1:57` | unsupported: IF NOT EXISTS | nothing: the model runs the migration without the clauses and gives SQLite's outputs: promote |
| v5 `fkey5:fkey5-10.1:51` | unsupported: IF NOT EXISTS | nothing: as for `index6-14.1`: promote |
| v5 `trigger1:trigger1-1.2.0:3`, v46 `trigger-exists`, v53 `view-create-if-not-exists`, `view-create-if-not-exists-over-table` | agree | already supported |
| v5 `select5:select5-5.11:21` (`GROUP BY b*a, b, a`) | unsupported: `group-by-term` | nothing: the same query with `GROUP BY p` or `GROUP BY 2` gives SQLite's rows: promote |
| v5 `select8:select8-1.1:0`, `-1.2:1`, `-1.3:2` (`GROUP BY LOWER(artist)`) | unsupported: `unmodeled-function` | `bare-column`: `artist` is not a grouping term. Retained |
| v55 `insert-query-group-by` | out of the subject's scope (`tests/conformance_insert_queries_test.py`) | the order of the rows that INSERT reads from a grouped source. Retained |

Issue #301 says that the archived reports of corpus v5 gave a generic blocker of the execution profile for these
cases. The verdicts of this tree give the specific reasons above, so the profile no longer
blocks them.

## Decision

### D1. Syntax: the flag in the statement

`Syntax.Statement.createTable` and `createIndex` get the field `ifNotExists : Bool`, in the
place that views and triggers use (after the name). The translation records the flag and
refuses nothing for it. The paths of restrictions and the spans of the composite nodes move
with the field.

### D2. Translation refusals stay

The translation refuses forms of the body before any state is known (`TEMP`, a schema name,
`AS SELECT`, and the column and table forms that it does not model). These refusals stay,
also with `IF NOT EXISTS`, although SQLite does not read the body when the object exists. A
refused statement is not a wrong answer: the model says that it does not describe it. Owner
decision 1 has the alternative.

### D3. Resolution decides the no-op

Resolution keeps its order, which is SQLite's. When the clause is present and the name check
finds the object that makes the statement a no-op, the statement resolves to `.drop []` with
`catalog.drop []`, as for views and triggers:

- `CREATE TABLE IF NOT EXISTS`: a table or a view of the name (any definition).
- `CREATE INDEX IF NOT EXISTS`: an index of the name (any table, terms, filter or `UNIQUE`).

Every check before the name check gives its error as today, and an index name with a table or a
view, or a table name with an index, gives its error also with the clause. No check after the
name check runs for a no-op, so its errors and restrictions do not apply. When the name is
free, the statement resolves and runs as without the clause, with every error, every
restriction and the `UNIQUE` check of the step of `.createIndex`.

The no-op gives `.done 0`, and keeps the database, the transaction state and the counters. A
schema description (`resolveSchema`) accepts the flag.

### D4. Grouping terms are expressions

`resolveGroupTermTraced` keeps its cases for an identifier and for a number, and resolves every
other term as an expression of the query's scope:

- **Identifier.** A column of the scope, else a result alias, as today.
- **Number.** An integer literal, also under parentheses or unary plus, names a result column;
  out of range is SQLite's error; a negative integer is out of range. Any other literal is a
  constant expression.
- **Alias inside an expression.** A result alias in a larger term (`GROUP BY k+1`) stays a
  model restriction, `alias-in-expression`, as in `HAVING` and `ORDER BY` today. SQLite
  substitutes the result column's expression; the alias alone (`GROUP BY k`) already gives
  that.
- **Every other term** resolves with the operand resolver that `WHERE` uses, so every
  expression that the model resolves in `WHERE` is a grouping term, with that resolver's
  restrictions (for example `unmodeled-function` for a function that the model does not have).
  An aggregate is SQLite's `aggregate functions are not allowed in the GROUP BY clause`. A
  window function stays refused by the translation, as in every other position. A subquery stays the
  restriction `group-by-term`: no corpus case needs it, and `Resolved.Expr.grouped` treats a
  subquery as bare. The counter functions and random values stay restricted in `GROUP BY`
  (ADR 0024).
- **Collation.** The term's collation is SQLite's: explicit `COLLATE`, else the column's
  collation through unary plus and `CAST`, else `BINARY`. `collationIn` already gives these
  (`Syntax.Expr.columnCollation` passes through `.positive`, `.cast` and `.collate`); the
  probes of the context are its test cases.

The restriction `group-by-term` keeps its id for subqueries and gets the text "a subquery is
not modeled in GROUP BY".

Evaluation does not change: `groups` already compares the term values under their collations,
with SQLite's equality and without affinity. A key that can fail makes the query's fault
`may`, as for any kept expression. A more exact fault (a key that must fail for a kept row)
is not required by this ADR.

### D5. The values of a group

The value that a group gives for a non-aggregate expression follows SQLite's three rules
(Context, "The row of a group"), and the model does not decide the plan-dependent choice:

- **Deciding call.** The deciding call is the last distinct `min` or `max` aggregate of the
  query in the order result columns, `ORDER BY`, `HAVING`, where a call that is written again
  counts at its first place. A query without such a call has no deciding call.
- **Representative rows.** For each group, the candidate first rows are all rows of the group.
  With a deciding call, the candidate rows for column references are the rows whose value of
  that call's operand gives the result (the ties of the minimum or maximum). When a `min` or
  `max` call of the query has `FILTER`, every row of the group is a candidate: the probes show
  that SQLite then loads the columns on rows that the simple rule does not give
  (`SELECT c, max(n), min(n) FILTER (WHERE n > 9)` gives `'a'`, not the maximum's `'A'`), and
  this ADR does not describe that rule more exactly.
- **Evaluation.** A result column, a `HAVING` condition and an `ORDER BY` expression read their
  column references from one chosen candidate row, the same row for the whole group.
- **Association.** For each grouping term, the resolver records the last result column that
  is the same expression as the term, as SQLite's `resolve.c` does. Two expressions are the
  same when their resolved forms are equal and their explicit `COLLATE` clauses are at the
  same places with the same names, compared without case. The resolver compares while it
  still has the written expressions, because the resolved form does not keep `COLLATE`
  (`resolveOperandTraced` gives the operand's resolved form). The associated result column, when it is not
  a column under at most `COLLATE` (a column under unary plus or `CAST` is not a column),
  reads the term's value on one chosen candidate first row. Every other result column reads
  its column references as the item before says, also when it is equal to a term.
- **Possible results.** `possibleResults` gives the results for every choice, as it gives the
  results for every order today (ADR 0018, D6). `Query.results`, which proofs use, keeps one
  choice: the first row in the order of the source, and for a deciding call the first row
  that gives the result.
- **Consumers of one result.** A subquery, a derived table and a compound term read one result
  (`Query.subqueryRun`, `Query.compoundRun`), not the possible results. They follow the
  precedent of `SELECT DISTINCT` (`Query.distinctCertain`): a new `Query.groupsCertain` is true
  when, for each group, every choice gives the same values, and `Query.run` gives the fault
  `may` when it is false. Through that fault a scalar subquery and `IN` give a value with the
  fault `may`, a derived table gives no rows to its query (`QuerySource.join` gives none), and a
  compound term ends with `may`, as for
  `DISTINCT` today. The index-dependent query of the context as a scalar subquery is then not
  a certain `'A'`.

This decision changes the meaning of grouped columns, also without D4. It is owner decision 2.

The number of results grows with the product of the choices of the groups. Most groups have
one distinct choice: their candidate rows give the same values. The implementation removes
equal choices per group before it forms products, and gives `unmodeled` with the reason "the
values of the groups depend on rows that SQLite chooses" above a limit that the task file
names. A limit that refuses a case of a claim is a capability loss and needs an owner decision.

### D6. Grouped expressions and bare columns

`Resolved.Expr.grouped` keeps its rule: a result expression is admitted when it is a grouping
term or is made of grouping terms, values and aggregates. With expression terms this admits
`SELECT date(c, 'unixepoch') ... GROUP BY date(c, 'unixepoch')` and
`SELECT lower(a) || '!' ... GROUP BY lower(a)`, and it refuses a column outside the terms, as
today (`SELECT a ... GROUP BY lower(a)` is `bare-column`). The comparison is on resolved
expressions, which makes it independent of the case of names, as SQLite's is. SQLite admits
bare columns; that restriction stays.

### D7. Proofs and API

- **Conditional creation.** Each theorem of the context that is about `resolveCreateTable` or
  `resolveCreateIndex` gets the no-op case, or the premise `ifNotExists = false` when the
  theorem is about creation only. Before writing the cases, the task analyses the most general
  form: one lemma that a statement that resolves to `.drop []` with `catalog.drop []` keeps the
  database and the counters and outputs `.done 0`, for all four CREATE forms, and one
  resolution lemma per form for the no-op condition. `Script.createIndex_allOk_iff` and
  `Succeeds.iff_createIndex` state the success of the index statement with the clause in
  their conditions.
- **Grouping.** `GroupTermResolves` covers an expression term: the resolved term of a written
  expression is its resolved operand. The duplicate-key laws then hold for expression keys with
  `key.Calm`; a `date` key is not calm (it can read the clock), so these laws do not cover the
  consumer's queries, and no new law is required for them. The laws that read the values of a
  group (`Query.results`) keep their statements, with D5's choice in `Query.results`. The
  resolution arms (`resolveGroupTerm_*`, `resolveQueryBody_arm`) follow the new case split.
- **Flexibility.** The resolved grouping term stays an arbitrary `Resolved.Expr` with its
  collation, so a user's proof states facts about any grouping, not only about the consumer's
  form (AGENTS.md section 19).

### D8. Slices, evidence and acceptance

Three slices, in this order, each with its own task file and the two pull requests of a claim
change (ADR 0011):

1. **Conditional creation** (D1 to D3, D7 first item).
2. **The values of a group** (D5) for the grouping that the model has today.
3. **Expression grouping** (D4, D6, D7 second item).

Evidence, reused before new cases:

- **Promotions.** Slice 1 adds to `mustAgree`: v4 and v5 `index-if-not-exists`,
  `index:index-6.1c:32`, v5 `index6:index6-14.1:57` and `fkey5:fkey5-10.1:51`. Slice 3 adds v5
  `select5:select5-5.11:21`. The verdict of each other case of every claimed corpus stays.
- **Retained.** v5 `select8:select8-1.*` (`bare-column`), an alias inside a grouping term
  (`alias-in-expression`), v55 `insert-query-group-by` (order of
  an INSERT source), the authored aggregate-in-`GROUP BY` and out-of-range cases of
  `conformance/authored_queries.py` (SQLite errors, which stay negative cases).
- **New authored cases**, one corpus per slice, recorded with the native oracle, for the gaps
  that no case covers:
  - Slice 1: each row of the table of conditional creation; the error order (a reserved name,
    `no such table` before the index name, `views may not be indexed`); a body that SQLite does
    not read (duplicate column, unknown column in an index term or filter); `UNIQUE` over
    duplicates, existing and free; the counters after a no-op; a no-op in a transaction that
    rolls back; ASCII case folding of names.
  - Slice 2: the six rows of "What the model gives today", `min` and `max` in both orders and
    across the result, `ORDER BY` and `HAVING`, a repeated call, `FILTER` on the deciding call,
    a tie of the maximum whose rows differ, a result column written twice, `COLLATE` on one side
    only, and the index-dependent query as a scalar subquery, as a derived table and as a term
    of a compound.
  - Slice 3: the probes of "Grouping: SQLite": storage classes and `+0`, NULL keys, the
    collation cases, aliases and alias shadowing, numbers (`(1)`, `+1`, `-1`, `0`, `1.0`,
    `'1'`), aggregate and window terms, a failing key with and without kept rows, rule 3 with
    a single `max`, and a `date(x, 'unixepoch')` key with an explicit clock.
- **Kernel-checked examples** in `tests/surface`: the no-op keeps the database and the
  counters (as `ClaimsViewCreate.lean` does for views), creation with the clause equals
  creation without it when the name is free, and a grouped expression's result on a small
  database.
- **Tests** of the translation (`tests/syntax_mapping_test.py` drops the refusal and checks the
  flag) and of the registry (`tests/restriction_registry_test.py`). Each new test has a
  timeout, as the suites set it.

Documentation: `docs/semantic-subset.md` removes `IF NOT EXISTS` from the refused forms and
documents it with the CREATE forms, documents expression terms in `GROUP BY` and the values of
a group, and updates the text of `group-by-term`. Each slice changes the documentation in the
commit that changes the behavior.

## Consequences

- The consumer's migrations are no longer refused for `IF NOT EXISTS`. Its `GetUsageByDay` and
  `GetRecentActivity` resolve; their runs need an explicit clock, as every query that reads a
  date of a column does.
- A statement with `IF NOT EXISTS` and a body that the translation refuses stays refused,
  although SQLite runs it as a no-op when the object exists (D2).
- Queries whose groups hold rows that compare as equal but differ get the set of results that
  SQLite may give, instead of one result that SQLite does not always give. Predictions of such
  queries can become `oneOf` lists, and in rare cases `unmodeled` (D5).
- The CREATE theorems get a second case or a premise. Proofs that use them for creation keep
  their statements with `ifNotExists = false`.

## Alternatives considered

**Remove the clause in the text.** Rejected by the issue and by SQLite: a removed clause turns
a no-op into `table t already exists`, and it reads a body that SQLite does not read.

**Decide the no-op in the translation.** Rejected: the translation does not know the catalog;
the resolver does, and views and triggers already decide there.

**Keep the first row in rowid order (no D5).** Rejected as the recommendation, but it is option
(b) of owner decision 2: it is less work, and it keeps the disagreements of "What the model
gives today", which expression keys such as `a+0` and `lower(c)` make more frequent.

**Refuse a group whose candidate rows give different values.** Rejected: the `mustAgree` case
`collate-group-by-value` has such a group, so the refusal is a capability loss; D5 describes
it instead.

**A special case for `date`.** Rejected: D4 admits every expression that `WHERE` admits.

## Not decided here

- `TEMP` objects, schema names and `CREATE TABLE ... AS SELECT`, with or without the clause.
- Bare columns in aggregate queries (`bare-column`), and the order of the rows that an INSERT
  reads from a grouped source.
- Subqueries as grouping terms.
- `sqlite3_stmt_readonly()` and other observations that the model does not have.
- The consumer's own mismatches: the selection of migration sections, and a query that reads a
  column that the schema does not have.

## Owner decisions

1. **Refusals in the body of a no-op (D2).** OPEN. Options: (a) keep the translation's
   refusals, also when the object exists; (b) let the translation give an "unmodeled body" for
   a statement with the clause, and let resolution refuse it only when the name is free.
   Recommendation: (a). (b) needs a new form of statement for a body that the model does not
   describe, and no case or consumer statement needs it: the consumer's CREATE statements with
   the clause have bodies that the model translates.
2. **The values of a group (D5).** OPEN. Options: (a) D5 as written, in slice 2; (b) keep the
   first row in rowid order and record the disagreements as a known defect with its own issue;
   (c) D5 without the plan-dependent choice: the min/max rule only, and the first row in rowid
   order otherwise. Recommendation: (a). It is the only option that agrees with SQLite for
   every row of "What the model gives today". (c) fixes four of the five disagreements and
   keeps one result, but it keeps a rule that SQLite does not promise.
3. **The limit of D5.** OPEN. The task file of slice 2 proposes the limit from the corpora's
   largest number of choices; the owner accepts it with the task file.
