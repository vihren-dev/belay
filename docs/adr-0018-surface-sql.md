# ADR 0018: The SQL that the user surface needs

Date: 2026-10-20. Status: PROPOSED.
Implementation: slice by slice, each with its own task file, as local commits; the pull
requests come when the ADR is done.
Audience: designers and reviewers.
Related: [ADR 0017](adr-0017-user-surface.md) (the user surface; its D5 lists this
work, and its owner decision 2 asks for all of it, starting with subqueries),
[ADR 0012](adr-0012-query-semantics.md) (queries), [ADR 0014](adr-0014-schema-features.md)
(schema features), [ADR 0015](adr-0015-functions.md) (functions),
[ADR 0011](adr-0011-product-trust-and-development-integrity.md) (the judge).

## Overview

The user surface states facts as SQL queries, and its examples are the failures that
users report. Both need SQL that the model does not describe yet: subqueries, the
expression forms `IN`, `BETWEEN`, `CASE` and `||`, `DISTINCT` and `HAVING`, enforced
foreign keys, triggers, and the set of results that SQLite may give when a `LIMIT` does
not fix the rows. This ADR adds them to the model, in six slices. Each slice follows
SQLite 3.51.0 exactly and is checked against native SQLite, as ADRs 0012 to 0015 are.

## Context

Measured on `main` after ADR 0015 (2026-10-20), with
`experiments/model-gaps/measure.py` over the verdict of that commit. Corpus v5 has 2,331
cases out of scope. The measurement marks the features of each case lexically, so its
counts are upper bounds and estimates: ADR 0015's estimate of about 690 cases was close
to its gain of 680, but single groups differed (JSONB: about 170 estimated, 117
gained).

| Group | Cases of v5 that use it | Cases that it alone makes clean |
| --- | --- | --- |
| Triggers | 416 | 86 |
| Subqueries | 332 | 75 |
| `PRAGMA foreign_keys` | 307 | 79 |
| `DISTINCT` and `HAVING` | 185 | 52 |
| `\|\|` | 105 | 57 |
| `BETWEEN` | 84 | 37 |
| `IN (...)` | 39 | 8 |
| `CASE` | 27 | 5 |

All groups together make 519 cases of v5 clean and 163 of corpus v4. The marks that most
often remain on a case that one more feature would make clean are other pragmas (269),
compound `SELECT` (228), `ALTER TABLE ... RENAME` or `DROP COLUMN` (109) and views (96);
they are not part of this ADR.

What the code has today:

- **Expressions are evaluated over one row.** `Expr.evaluate clock row` has no database
  and no outer row, so an expression cannot read a table. A query is a separate type
  (`Resolution/QueryForm.lean`) that holds expressions; expressions do not hold queries.
  `Source.subquery` exists as a placeholder that resolution never gives.
- **An aggregate is a whole result column.** An aggregate inside an expression is the
  restriction `aggregate-in-expression`, so `HAVING count(*) > 1` and `count(*) + 1` are
  out of scope.
- **Foreign keys are in the catalog but not enforced.** SQLite enforces them only after
  `PRAGMA foreign_keys = ON`, which the model does not have; a case whose setup may have
  turned them on is out of scope.
- **Triggers, views and pragmas are not modeled.**
- **A query gives one result.** For a `LIMIT` or `OFFSET` that the `ORDER BY` does not
  fix, the harness compares the model's result with SQLite's tie groups
  (`conformance/native_ordering.py`); the model has no description of the other results
  that SQLite may give.

## Decision

### D1. Subqueries: the statement holds its queries, and evaluation gets a context

A resolved statement holds a list of its subqueries. An expression names a subquery by
its index in that list: `EXISTS (q)`, `x IN (q)` and a scalar subquery `(q)`. A
subquery's own expressions name only subqueries after it in the list, so evaluation
recurses on a list that gets shorter, which keeps the recursion structural and the
kernel able to reduce it. `Expr` and `Query` stay separate types.

Evaluation gets a context: the clock, the database's tables, the statement's subqueries
and the outer rows. A correlated reference names a cell of an outer row by its depth and
position. Resolution gives the scope of each enclosing query, as SQLite resolves a name
first in its own query and then outward.

The context changes the type of evaluation, so every caller changes in the slice that
adds it: the queries, the writes, CHECK constraints, generated columns, index terms and
their laws. A form outside SQLite's rules, or one whose result the model does not
describe, stays a restriction with its own id.

### D2. The expression forms `IN`, `BETWEEN`, `CASE` and `||`

- `x IN (a, b, ...)` and `NOT IN`, with SQLite's affinity and NULL rules for the list;
  `x IN (q)` comes with D1.
- `x BETWEEN a AND b` with SQLite's rules: `x` is evaluated once, and the comparisons use
  the affinity and collation of `x`.
- `CASE` with and without an operand. Only the branch that SQLite takes is certain to run,
  so the faults of the others are softened, as for `iif` (ADR 0015).
- `||`, with the text of each operand as `concat` writes it and NULL for a NULL operand.

### D3. `DISTINCT`, and aggregates inside expressions

- `SELECT DISTINCT` removes rows that compare equal under each column's collation, keeping
  the first of each.
- An aggregate inside an expression becomes one more cell of the group's row: the query
  lists its aggregates, evaluation computes them for each group, and an expression names
  the cell. With this, `HAVING`, `count(*) + 1` and an aggregate in `ORDER BY` follow, and
  the restriction `aggregate-in-expression` goes away where SQLite's rules allow the form.

### D4. Enforced foreign keys

- The connection has a foreign-key setting, off by default as in SQLite, and the model
  describes `PRAGMA foreign_keys = ON`, `= OFF` and the query form `PRAGMA foreign_keys`.
  Other pragmas stay unmodeled.
- With the setting on, `INSERT`, `UPDATE`, `DELETE`, `DROP TABLE` and conflict
  resolution check foreign keys, and the actions `CASCADE`, `SET NULL`, `SET DEFAULT`,
  `RESTRICT` and `NO ACTION` run as SQLite runs them. `foreign key mismatch` and the
  other prepare errors come with them.
- Constraints with `DEFERRABLE INITIALLY DEFERRED` are checked at `COMMIT`, with SQLite's
  count of open violations. If the slice's measurement shows that the deferred form costs
  much more than the immediate one for few cases, it becomes a restriction, and the task
  file records the measurement.

### D5. Triggers

- `CREATE TRIGGER` and `DROP TRIGGER` on tables, with `BEFORE` and `AFTER`, `INSERT`,
  `UPDATE` and `UPDATE OF` columns, and `DELETE`, `FOR EACH ROW` and `WHEN`.
- A trigger's body is a list of resolved statements whose expressions read `NEW` and `OLD`
  as an outer row, by the mechanism of D1. `RAISE(IGNORE)`, `RAISE(ABORT, ...)`,
  `RAISE(FAIL, ...)` and `RAISE(ROLLBACK, ...)` follow SQLite.
- The order of triggers, recursion only with `recursive_triggers` (off by default), the
  limit on trigger depth, and the interaction with `REPLACE` and with foreign-key actions
  follow SQLite. `INSTEAD OF` triggers need views and stay out of scope.

### D6. The results that SQLite may give

The model gives, for each query, the list of results that SQLite may give: one for each
way that `LIMIT` and `OFFSET` can cut the tie groups of the `ORDER BY`, as the harness
already observes them. A query without `ORDER BY` has the normal form of the guide: its
rows sorted. The surface's `Output.oneOf` uses this list (ADR 0017, D3). The list is a
model function with a law that relates it to the one result that the model computes
today, so the corpora keep checking that result.

### D7. Slices and order

| Slice | Content | Needed by (ADR 0017) |
| --- | --- | --- |
| 1 | D1, subqueries, with the evaluation context | S4 |
| 2 | D2, the expression forms | S4 to S6 examples |
| 3 | D3, `DISTINCT` and aggregates inside expressions | S4 (level 2 of the unique index) |
| 4 | D4, enforced foreign keys | S6 (the rebuild that cascades) |
| 5 | D5, triggers | S8 (expand/contract) |
| 6 | D6, the results that SQLite may give | S2's row order examples, S6 |

Subqueries come first, as ADR 0017's owner decision 2 asks, and because D5 needs their
outer rows. Each slice works as in ADR 0015: an authored corpus with kernel proofs,
mutants for the rules that are easy to get subtly wrong, the verdict of every corpus,
and `just test-full` at the slice's end. The frontend changes go into the current
translation; slice S1 of ADR 0017 then replaces it with all of them.

## Consequences

- **Evaluation changes once, in slice 1.** Every later slice uses the same context, so
  triggers need no second change of evaluation.
- **The verdict grows in each slice, by an estimate of 519 cases of v5 in all.**
- **Kernel time grows with subqueries.** A correlated subquery evaluates its query once per
  outer row. Slice 1 measures the kernel time of the corpora's proofs before and after.
- **Pragmas become statements.** `PRAGMA foreign_keys` is the first; the others stay
  unmodeled until a measurement shows a gain.

## Alternatives considered

**`Expr` and `Query` as one mutual inductive type.** It states subqueries directly, but
the derived equality and the structural recursion of evaluation over a mutual type with
structures, lists and options are where Lean's kernel reduction and `deriving` are most
fragile; the indexed list of D1 keeps both types as they are.

**Triggers before subqueries, by the measured gain.** Triggers make the most cases clean
(86), but the surface needs subqueries first, and the bodies of triggers need the outer
rows of D1.

**Compound `SELECT`, views and other pragmas in this ADR.** They are the next marks of
the measurement (228, 96 and 269 cases), but the surface does not need them; they can
come in their own ADR.

## Not decided here

- Compound `SELECT`, views, `WITH`, `INSERT ... SELECT` and the other pragmas.
- Window functions and `ORDER BY` inside an aggregate call.
- The details of each slice: its task file decides them from SQLite's code.

## Owner decisions

To be decided:

1. **The order of D7**, subqueries first.
2. **Deferred foreign keys (D4):** implement them, or make them a restriction if the
   slice's measurement shows a high cost for few cases.
