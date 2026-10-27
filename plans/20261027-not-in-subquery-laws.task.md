# NOT IN and correlated NOT EXISTS: general query laws

Created 2026-10-27. Status: DONE (2026-10-27).
Status: [progress](20261027-not-in-subquery-laws.status.md).
Specs: [ADR 0017](../docs/adr-0017-user-surface.md), S4 and S6;
[S6 automation](20261024-s6-automation.task.md), the outcome "The guide
examples have checked scripts";
[S4 task](20261024-surface-s4.task.md), the query laws.

## Purpose and boundary

The guide states the query equivalence `notBlockedIn ≈ notBlockedEx`:

```lean
-- customers (id INTEGER PRIMARY KEY, ...), blocked (customer_id ...)
def notBlockedIn := sql r"SELECT id FROM customers
  WHERE id NOT IN (SELECT customer_id FROM blocked)"
def notBlockedEx := sql r"SELECT id FROM customers c
  WHERE NOT EXISTS (SELECT 1 FROM blocked b WHERE b.customer_id = c.id)"
```

S6 automation part 2 (not yet on this base; it is a prerequisite of the
implementation) adds a `notBlocked` fixture. The fixture refutes the
equivalence in general with three counterexamples confirmed by native SQLite (a
NULL `blocked.customer_id`, a NULL `customers.id`, and a collation difference
between `IN` and `=`), and checks one database that satisfies the premises. It
cannot prove the equivalence for every database, because the model has no row laws that relate `x NOT IN (SELECT c
FROM u)` to a correlated `NOT EXISTS (SELECT 1 FROM u WHERE u.c = x)` over a
filtered scan. The owner decided on 2026-10-27 that a separate task adds these
laws as general laws. The guide claim is then proved as a fixture in
`tests/surface`.

The laws are general: they hold for any outer table and any subquery table
under explicit premises. They are not specific to `customers` or `blocked`
(owner decision of 2026-10-26: guide examples are test fixtures only). This
task changes no SQL meaning, no execution, no prediction, no corpus, no claim
and no judge file.

## Required outcomes

- **A value law relates IN to the comparison.** For a value `v` and candidate
  values `vs`, a law relates `inValue affinity collation true v vs` (the value
  of `NOT IN`) to the value of `NOT` applied to the disjunction of `v = c` over
  the candidates. Here `=` is compared with the affinity and collation of the
  correlated comparison. The law states its premises explicitly: `v` is not
  NULL, no candidate is NULL, and the two comparisons agree on `v` and each
  candidate. For example, both have the same affinity and collation, or `v` and
  every candidate are integers. The plain-words statement says which case
  gives NULL when a premise fails.
- **A filter law relates the two WHERE clauses.** For one row of an outer
  simple query, the condition `x NOT IN (q)` and the condition `NOT EXISTS (q')`
  keep the row equally. Here `q` selects column `c` of table `u` with no WHERE,
  and `q'` selects from `u` with the correlated condition `u.c = x`. The premises
  are the value-law premises over the rows of `u`, plus: `x` evaluates without
  a fault, and both subqueries run without a fault and with certain rows. The
  law follows the evaluation of `Resolved.Expr.inQuery` and `.exists` in
  `ExprEval.lean`, including `rowsCertain` and the fault join. A premise that
  can fail is never silently treated as true.
- **The query law lifts it to outputs.** For an outer simple one-table query,
  the two statements give the same rows in the same order, when the premises
  hold for every row of the outer table. Resolution is covered: a law states
  how each statement resolves in a catalog where both tables and the named
  columns exist, as the existing `ExistsStatementResolution` and
  `SubqueryExprResolutionLaws` do.
- **Sufficient structural premises.** A lemma derives the value-law premises
  from facts a user can check about a database: the outer key column is a rowid
  alias (an `INTEGER PRIMARY KEY` of a table that is not `WITHOUT ROWID`, so
  never NULL and always an integer), and no subquery-column value is NULL. The
  lemma shows that, with an integer probe, the `IN` comparison and the
  correlated `=` agree for every non-NULL candidate, whatever its type,
  affinity or collation. If the model or native SQLite shows a candidate where
  they differ, stop and report it. The other premise forms (same affinity and
  collation) stay usable without this lemma.
- **The surface has the lemma.** A belay lemma states the equivalence of the
  two statement forms as `Sql.EquivAt` (or the relation that the guide claim
  uses) over every database that meets the structural premises. It sits next to
  `NotExistsQuery.lean` and `ExistsQuery.lean`. It is general over table and
  column names.
- **The guide claim is proved.** In `tests/surface`, next to the S6 fixture of
  `notBlockedIn` and `notBlockedEx`, a theorem proves the guide's claim for
  every admitted database under the premises: `customers.id` is a rowid alias,
  and no row of `blocked` has a NULL `customer_id` (the guide's `where`
  condition, a premise on the rows). `Database.Admitted` does not make rows
  meet `NOT NULL`. The form with `NOT NULL` in the schema therefore also
  assumes `Database.NotNull` (or `Database.Valid`) and derives the row premise
  from it. The proof uses the general laws, through `sql_auto` or
  an explicit rule. The three counterexamples stay. The status file records
  the guide change: the guide's statement needs the rowid-alias premise and
  must mention the NULL `customers.id` and collation counterexamples.

## Tests and acceptance

- Kernel examples check the value and filter laws on concrete values:
  - no NULL, with a match and without one;
  - a NULL probe and a NULL candidate (premises fail; the law does not apply,
    and an example shows the different values);
  - an empty subquery;
  - text keys that are equal under `NOCASE` but not under `BINARY`.
- Native SQLite checks the concrete query results that the examples state,
  with the existing native helpers of the surface tests.
- The guide theorem and its counterexamples are checked through the S6 pytest
  driver of the `notBlocked` fixture, with axiom audits that allow only
  `propext`, `Classical.choice` and `Quot.sound`.
- All prediction files stay byte-identical to the base (`nix-build
  integrity/judge.nix -A predictions`, 55 files).

One acceptance part: each coherent commit gets focused checks, dev-build and
independent review. After the last review, run `just test-full` and `just
verdict`; at task end, run `just test-nix` and `just test-scheduled-checks`.
Only Nix results are acceptance evidence.

## Existing interfaces and tricky points

- Evaluation: `inValue` and the `.inQuery` and `.exists` arms of
  `Resolved.Expr.evaluate` (`ExprEval.lean`). `inValue` gives NULL when the probe
  is NULL and the candidates are not empty, and when no candidate matches but
  one is NULL. `.inQuery` softens the fault to `.may` when the subquery rows are
  not certain.
- `comparisonOperands` applies the affinity before the collation compares. `IN`
  and `=` take their affinity and collation from different operands. That is the
  source of the collation counterexample; the value law must take both
  comparisons as parameters, not assume that they agree.
- Existing laws to reuse:
  - the uncorrelated `EXISTS`/`NOT EXISTS` outputs (`ExistsSubqueryOutput.lean`,
    `NotExistsSubqueryOutput.lean`) and their surface forms (`ExistsQuery.lean`,
    `NotExistsQuery.lean`);
  - the simple-query results (`SimpleResultsLaws.lean`, `SimpleQueryLaws.lean`);
  - subquery resolution (`SubqueryExprResolutionLaws.lean`,
    `ExistsStatementResolution.lean`);
  - correlated subquery evaluation (`Subqueries.lean`, `SubqueryExamples.lean`).
- The correlated subquery reads the outer row as a cell position. The filter
  law needs the subquery run at each outer row
  (`context.subqueries index row`).
- The S6 `notBlocked` fixture and its native counterexample test come from S6
  automation part 2. Extend them; do not copy them.
- Parallel work: the table-rebuild agent owns the model run, statement and
  ALTER files (DROP COLUMN, the column remap of `Resolved.Expr`). This task owns
  new query-law modules and the `notBlocked` fixture. Keep edits of the barrels
  (`Belay/Sqlite/Model.lean`, `Belay/Sqlite.lean`, the lakefiles) to added lines.
- The private guide is not edited here.
- Files stay below 200 lines, with checked public docstrings, plain-words
  statements and proof sketches.
