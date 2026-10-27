# Status: NOT IN and correlated NOT EXISTS query laws

Created 2026-10-27. Status: OPEN (in progress).
Task: [task file](20261027-not-in-subquery-laws.task.md).
Specs: ADR 0017 S4 and S6; the S6 automation task and its part 2 open point
"notBlocked".

## Decisions

- 2026-10-27 (owner): the universal `notBlockedIn ≈ notBlockedEx` claim gets
  general NOT IN / correlated NOT EXISTS query laws in this separate task, not
  a guide change.

## Progress

- 2026-10-27: task specified on the open PR stack (after table rebuild part 2,
  PR #279). The implementation starts after S6 automation part 2 is published,
  because it extends that part's `notBlocked` fixture.
- 2026-10-27: spec reviews `20261027T054201Z-95604a1b` (1 must, 1 should, both fixed in the next commit;
  the resolution of finding 1 was recorded twice by mistake, both as fixed) and `20261027T054328Z-22df9c12`
  (no findings).
- 2026-10-27: commit 1, model laws in new modules (no change to SQL meaning or predictions); reviews
  `20261027T071151Z-17ae5c36` (1 must, 1 should, both fixed in the refactor commit `b5fb0684`) and
  `20261027T071359Z-b5fb0684` (no findings). These commits had narrow forms of the laws (a `NOT IN` value law, a filter
  law for a column probe, a subquery that selects one column of a table with no `WHERE`).
- 2026-10-27: review `20261027T073958Z-c085e7c9` of the generalization commit: 2 musts (R2: the query-law docstrings
  said scan order but the output is in normal form; the docstring of `Comparison.apply_congr_compare` was narrower than
  the formula), both fixed in the next `refactor:` commit.
- 2026-10-27: generalization commit (owner rule "Generalize every new statement"): the narrow forms were replaced in
  place and the modules were renamed. See "Generalization record" below. The modules are `InValueEqualsLaws`
  (`compareValue`, `equalsValue`, `inMatches`, `equalsAny`), `InValueEqualsAny` (value laws), `InIntegerProbe`
  (integer probe), `CorrelatedSubquerySource`, `CorrelatedSubqueryRun` (`Query.oneTable` and its run),
  `InSubqueryEvaluate`, `InSubqueryFilterLaw`, `InSubqueryEqualityLink`, `InSubqueryColumnLaw`,
  `InSubqueryRowidAlias`, `SimpleSubqueryRowsOutput`, `OneTableStatementOutput`, `InSubqueryQueryLaw`,
  `InSubqueryQueryInLaw`, `InSubqueryQueryRowidAlias`, `InSubqueryExamples` (kernel examples). The statements are calm
  without a premise: the condition, the columns and the subquery use no fallible call, clock or counter.

- 2026-10-27: resolution-law commit: `FromSourceResolution`,
  `FromSubquerySelectResolution`, `FromSubqueryStatementResolution`, `InSubqueryStatementResolution`,
  `CorrelatedExistsResolution`. The query laws now conclude `out1 = .rows rows` and `out2 = .rows rows` for one list.

## Deviations and decisions of the implementation

- The value law is stronger than the task text: it needs no NULL premise, only that the `IN` test and the `=`
  comparison match the same candidates for a non-NULL probe. With no candidate both sides are 0 (`IN`) or 1
  (`NOT IN`), also for a NULL probe. With at least one candidate and a NULL probe, or a NULL candidate without a match,
  both sides are NULL. The NULL premises appear in the filter-level `inValue_negated_eq_not_exists` (`NOT IN` against
  `NOT EXISTS`), where the difference is NULL against 1.
- The run laws take no premise on the length of the outer row: a subquery sees the outer row cut or filled with NULL to
  the width `outer` (`outerCells`). The check of faultless evaluation over the empty row is therefore covered.
- No candidate was found where the model's `IN` comparison and the correlated `=` differ for an integer probe and a
  non-NULL candidate (`inMatches_integer_collation_free`: any two collations, one non-TEXT affinity;
  `compareValue_integer_collation_free`: any comparison operator, integer on either side).

- The output of a statement without `ORDER BY` is in the normal form of the model (`Resolved.normalForm`), because
  SQLite does not promise an order. The query laws therefore say "same rows in normal form", which is the model's
  form of "same rows in the same order" for these statements.
- Merge note (coordinator message): the table-rebuild agent adds `Resolved.Statement.dropColumn`,
  `Syntax.Statement.dropColumn` and a `dropped` field of `RowLocalAtom` and `TableAtom`. The modules of this task
  match on no statement type exhaustively and build no instance of these structures, so the later merge needs no change.

## Generalization record

For each new public statement: the general form chosen, and what stays specific with the reason.

- `compareValue` (any operator), `equalsValue` (its `=` instance), `equalsAny`, `inMatches`: general over affinity,
  collation and values. `inMatches` stays the `IN` test, a separate definition, because `inValue` does not use
  `compareValue`.
- `inValue_eq_equalsAny`: both polarities (`IN` and `NOT IN`), any probe and candidates; the only premise is that the
  two tests agree on a non-NULL probe. `truthy_inValue_eq_any`: the truth of `IN`, no NULL premise.
  `inValue_negated_eq_not_exists` stays `NOT IN` because the values of `IN` and `EXISTS` differ (NULL against 0); the
  truth form covers `IN`.
- `compareValue_integer_collation_free` and `compareValue_collation_free_integer`: any comparison operator, integer
  on either side. `inMatches_integer_collation_free` is the `IN` test form (not an instance of the former, because
  `inMatches` is its own definition). Both need an affinity that is not TEXT.
- `Query.oneTable` and `Query.oneTable_subqueryRun`: any table, outer width, optional `WHERE` expression and
  result expressions (the builder covers `SELECT c FROM u`, `SELECT 1 FROM u WHERE u.c = x`, a subquery with a
  `WHERE`, and any projection). Premises: no fallible call, no fault over the empty row and the joined rows. It is
  specific to one table source with an inner join and no `GROUP BY`, `ORDER BY` or `LIMIT`; more sources need a new
  source-row law.
- `Expr.evaluate_inQuery_oneTable`, `evaluate_exists_oneTable`, `evaluate_notExists_oneTable`: any probe expression,
  any projection, any `WHERE`.
- `Expr.evaluate_notIn_eq_notExists` and `Expr.evaluate_in_truthy_eq_exists`: any probe expression, any result
  expression, any `WHERE` of the `IN` subquery, any condition of the correlated subquery. The link between the two
  subqueries is one semantic premise (`CorrelatedEquality`). The `IN` law gives the truth only, because the values
  differ.
- `correlatedEquality_of_compare` and `correlatedEquality_of_guarded_compare`: the syntactic links for
  `u.e = probe` and `w AND u.e = probe`, any expressions with a premise that the probe has its value in every joined
  row.
- `Expr.evaluate_notIn_eq_notExists_of_columns` and `evaluate_in_truthy_eq_exists_of_columns`: specific to a column
  probe of the outer row, a column of `u` as the result expression and no `WHERE` in the `IN` subquery. The reason:
  these are the forms of the guide claim, and the plain, fault and link premises are then proved instead of assumed.
  The general laws serve every other form.
- `Expr.evaluate_notIn_eq_notExists_of_rowidAlias` and `evaluate_in_truthy_eq_exists_of_rowidAlias`: specific to a
  column probe that is the rowid alias of the outer table, because the structural premise is a fact about a column.
- `Query.oneTable_calm`, `resolvedStepOutput_oneTable_rows`: any condition, any result expressions.
  `resolvedStepOutput_oneTable_congr`: any two conditions that keep the same rows; the result columns are columns of
  the outer table (positions), because a result expression that reads the subquery context needs a premise that both
  contexts give the same value.
- `resolvedStepOutput_notIn_eq_notExists`, `resolvedStepOutput_in_eq_exists` and the rowid-alias forms: specific to the
  column forms of the filter laws. The statement-level law for any probe, projection and `WHERE` is the composition of
  `resolvedStepOutput_oneTable_congr` with the general filter law; its premises name the contexts of both statements,
  so it was not stated as a separate theorem (about 120 lines of premises). A statement has one subquery.
- Resolution laws (`resolveStatement_selectFrom_subquery`, `resolveStatement_selectFrom_inQuery`,
  `resolveStatement_selectFrom_existsTest`, `FilterResolves.exists_only`, `FilterResolves.notExists_only`): general
  over the outer table, the subquery table, the probe expression, the polarity (`IN` and `NOT IN`, `EXISTS` and
  `NOT EXISTS`), the projections and the conditions. The resolution of names inside the conditions stays a hypothesis
  (`FilterResolves`, as in `ExistsStatementResolution`), because the model has no law for qualified names in an
  enclosed scope (`correlatedScope`); a user proves it for a given catalog by computation. One outer table with no
  join and one subquery table with no join stay specific: other source shapes need new source-resolution laws.
