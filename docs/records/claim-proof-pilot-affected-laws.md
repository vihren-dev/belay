# Claim proof pilot: laws that the recommendation affects

Date: 2026-11-25. Audience: the team. This record answers the question of
the owner: if the project adopts the recommendation of [the pilot
findings](claim-proof-pilot-findings.md), which laws of today change. It
lists each law by name.

Paths: `M/` is `packages/belay-sqlite-model/Belay/Sqlite/Model/`, `S/` is
`packages/belay/Belay/Sqlite/`, and `T/` is `tests/surface/`. "Today" is
revision `1e8dfd8d`, the top of the pull requests of ADR 0033. The numbers
of this record come from local scripts and from readers; they are not
results of the Nix checks.

## Result

The packages have 2,759 theorems today. The recommendation affects 112
package declarations, in four groups:

1. The pilot branch already changes 19 declarations: it deletes 15 and
   changes 4. This group is exact.
2. 91 more declarations belong to one form of query (78 laws and 13
   definitions that only these laws use). The point "the laws of one query
   form are deleted" applies to them. 41 of them are resolution laws, which
   go only with decision 1. 10 are equivalence laws (decision 3). 3 are
   facts about unique keys, whose statement changes (decision 4). 13 are the
   definitions. The other 24 are evaluation laws and no-fault laws: the laws
   of the branch replace some of them now, and the others go after an
   operator law that the pilot did not write.
3. 2 laws of the rows of an `INSERT`, for exactly two and exactly three
   parameters, become cases of the fact that point 4 adds. Points 4 and 5
   delete no other package law: point 4 adds one fact for each kind of
   write, and point 5 changes the tactic `sql_run`.
4. In the test fixtures, 45 support laws of the same forms go with the
   package laws, 71 proofs that use them change, and the structures that
   carry the resolution of a write for one schema go (decision 1).

Of the 2,759 package theorems, 93 are in these groups and 2,666 stay as they
are. 14 of the 99 theorems that the readers put in the class "law of one
query form" stay; the section of group 2 gives the reason for each.

Two findings matter for the decision:

- The laws of one query form have no user in the packages other than laws of
  the same class. Their users are the test fixtures. Their removal changes
  no other law of the model.
- 41 of the 91 are resolution laws. The tactic computes the resolution on a
  known catalog and needs none of them. They are necessary only for a claim
  over each database that has one table, which is how the older fixtures
  state their claims. Decision 1 thus decides the largest part of the list.

## Method and limits

Three sources give the list:

- A comparison of the declarations of today with the tactic branch of the
  pilot (`5bc3c323`), for each declaration: deleted, added, moved, statement
  changed. This gives group 1.
- A classification of each theorem of today. Twelve readers read all 2,759
  theorems of the packages and all 1,208 theorems of `tests/surface`, and
  gave each a class: law of one query form (99 in the packages, 49 in the
  tests), law of one simple `SELECT` (36, 1), law of one kind of write (177,
  36), premise of a write rule (46, 10), checker with its soundness law (17,
  2), law of a script pattern (36, 11), or none of these. The author of this
  record read the statement of each law of one query form again.
- A search by name for the users of each law.

Limits:

- The class of a law is a judgment of a reader. A law of one query form is a
  law whose statement fixes a composition of two or more operators. A law
  that a reader put in a different class by mistake is not in the list.
- The search by name does not find a use through dot notation when the last
  part of the name is not unique. A user count can thus be low.
- For the laws outside group 1, "replaced" is a conclusion from the
  recommendation. The pilot proved two claims of one form. No build shows
  that each law of groups 2 and 3 can go.

## Rule for each deletion

The simplification goal gives full credit for a deleted law when its
statement stays derivable from general laws, and none when the premise
becomes stronger or the conclusion weaker. The pilot branch follows this
rule for group 1: test fixtures prove, from the laws that remain, the
statement of each deleted law that a fixture used. The same proof is
necessary for each law of group 2 before it goes, or the owner accepts the
loss. Decisions 1 and 2 are the two places where a loss can occur.

## Decisions that the list depends on

1. **Claims over a part of the catalog.** The older fixtures state a claim
   for each database that has a table with given columns, or for each table.
   The tactic computes the resolution of a claim on the full catalog, which
   the premise `HasCatalog` gives. If each claim uses the full catalog as
   premise, the resolution laws of the forms have no use and go. If claims
   over a part of the catalog stay, the resolution laws stay, or one general
   law replaces them: the resolution of a statement depends only on the
   tables that the statement names. The pilot did not examine that law. A
   claim with the full catalog as premise has a stronger assumption than the
   claim of today. By the rules of the [simplification
   goal](../development/lean-simplification-goal.md), that is a loss of
   capability and needs a decision of the owner for each group that it
   touches.
2. **`Empty` and `Fails`.** The support laws of the fixtures give three
   facts for a claim: when it holds, when it is empty, and that it does not
   fail. The tactic gives the first. The support laws can go when the tactic
   gives all three. A fixture that keeps only the first fact has a weaker
   conclusion, which is also a loss of capability.
3. **Equivalence of two queries.** The laws of `IN` and `EXISTS` prove that
   two queries return the same rows. They are client theorems of a different
   type than a claim. They can stay as they are, with shorter proofs from
   the operator laws, or the library keeps only the operator laws and a
   client proves the equivalence.
4. **Facts about unique keys.** Three laws state "at most one row matches"
   as a bound on the count of the form. Without the definition of the form,
   the statement is a bound on the rows that the condition keeps.

## Group 1: changed on the pilot branch

These changes are on the tactic branch (`5bc3c323`). They are exact. The
column "Users" gives the number of package declarations and the number of
test declarations of today that name the declaration.

### Deleted

The frame form `SELECT 1 WHERE NOT EXISTS (q1 EXCEPT q2)`:

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.notExistsExcept` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 2 / 1 |
| `Resolved.notExistsExceptSubqueries` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 4 / 0 |
| `Resolved.currentTerm` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 5 / 0 |
| `Resolved.initialTerm` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 6 / 0 |
| `Resolved.currentTerm_mem_results` | `M/Queries/Evaluation/TwoStateKeptRows.lean` | 1 / 0 |
| `Resolved.initialTerm_mem_results` | `M/Queries/Evaluation/TwoStateKeptRows.lean` | 2 / 0 |
| `Resolved.notExistsExcept_calm` | `M/Queries/Evaluation/TwoStateNotExistsExceptOutput.lean` | 1 / 0 |
| `Resolved.notExistsExcept_context_zero` | `M/Schema/Dispatch/TwoStateNotExistsExcept.lean` | 1 / 0 |
| `Resolved.notExistsExcept_identical` | `M/Schema/Columns/TwoStateKeptRows.lean` | 0 / 1 |
| `Resolved.notExistsExcept_subset` | `M/Schema/Columns/TwoStateKeptRows.lean` | 0 / 1 |
| `resolvedStepOutput_notExistsExcept_hasRows` | `M/Tooling/Counterexamples/TwoStateNotExistsExceptOutput.lean` | 0 / 1 |
| `resolvedStepOutput_query_hasRows_of_clean_from` | `M/Tooling/Counterexamples/TwoStateQuerySteps.lean` | 1 / 0 |

Replaced by the law of the subquery of a simple query
(`Resolved.Query.simple_subqueryRun`,
`Resolved.Query.simple_subqueryRun_rowwise`), the laws of `EXISTS`
(`Resolved.Expr.truthy_exists`, `Resolved.Expr.truthy_notExists`), the
identity of rows that compare equal
(`Resolved.equalRowsIdentical_rowidFirst`), the no-fault check
(`Resolved.Statement.calm_of_calmCheck`), the output laws
`resolvedStepOutput_calm_hasRows` and
`resolvedStepOutput_selectOneWhere_hasRows`, and the fact of the rows that a
delete keeps (`LiteralData.mem_deleted`).

The condition `(a AND b) IS NOT 1`:

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Expr.truthy_isNot_one_and` | `M/Queries/Evaluation/RowwiseExpr.lean` | 0 / 1 |
| `Resolved.Value.and_cases` | `M/Queries/Evaluation/RowwiseExpr.lean` | 1 / 0 |
| `Resolved.truthy_isNot_one_of_cases` | `M/Queries/Evaluation/RowwiseExpr.lean` | 1 / 0 |

Replaced by the property that a value is NULL, 0 or 1 (`Value.IsLogical`,
`Resolved.Expr.isLogical`, `Resolved.Expr.eval_isLogical`) and one law of
`IS NOT 1` for each such value (`Value.truthy_isNot_one`,
`Resolved.Expr.truthy_isNot_one`).

The six modules that contain only these declarations are deleted:
`M/Queries/Evaluation/TwoStateNotExistsExcept.lean`,
`M/Queries/Evaluation/TwoStateKeptRows.lean`,
`M/Queries/Evaluation/TwoStateNotExistsExceptOutput.lean`,
`M/Schema/Dispatch/TwoStateNotExistsExcept.lean`,
`M/Schema/Columns/TwoStateKeptRows.lean` and
`M/Tooling/Counterexamples/TwoStateNotExistsExceptOutput.lean`.

### Changed

- `Connection.queryContextFrom`,
  `M/Schema/Dispatch/TwoStateQuerySteps.lean`. The start database is now
  optional, so that one definition serves a claim on one database and a
  claim that reads the start.
- `Select.evaluationProof?`, `S/Programs/Automation/SqlSelectEval.lean`. The
  check of the equation is now synchronous. Before, an asynchronous check
  accepted a false equation. This is a fault fix that does not depend on the
  decision.
- `Resolved.Query.simple_expressions_rowwise`,
  `M/Queries/Evaluation/TwoStateNotExistsExcept.lean`. Moved to
  `M/Queries/Evaluation/RowwiseExpr.lean`, with a more general statement.
- `Resolved.Query.simple_results_congr`,
  `M/Queries/Evaluation/TwoStateNotExistsExcept.lean`. Moved to
  `M/Queries/Evaluation/RowwiseExpr.lean`, with a more general statement.

The branch adds 58 package declarations: 3 laws of the base form, the
operator laws, and the definitions and bridge laws of the tactic. The
findings record gives the line counts.

### Test fixtures

Deleted, in `T/Schema/Tests/PurgeFrameInstances.lean`:

`AssertionExamples.fiftySite`, `AssertionExamples.modeledAtFifty`,
`AssertionExamples.null_customer_has_a_site`,
`AssertionExamples.null_time_has_a_site`,
`AssertionExamples.text_time_has_a_site`.

Statement changed or moved: the structure `PurgeFrameSite` loses the two
fields of the resolution of the claim; the three definitions of the schema
move to `T/Schema/Tests/PurgeFrameSchema.lean`:

`AssertionExamples.PurgeFrameSite`, `AssertionExamples.purge_keeps_rows`,
`AssertionExamples.purge_frame`, `AssertionExamples.purge_frame_typed`,
`AssertionExamples.sessions`, `AssertionExamples.sessionsEntry`,
`AssertionExamples.sessionsSite`.

The branch adds 35 test declarations. Ten of them, in the namespace
`PurgeLawRetention`, prove, from the laws that remain, the statements of the
four deleted laws that a fixture used: `Resolved.Expr.truthy_isNot_one_and`,
`Resolved.notExistsExcept_identical`, `Resolved.notExistsExcept_subset` and
`resolvedStepOutput_notExistsExcept_hasRows`. They show that the deletion
loses no capability. The other deleted declarations were steps of the proofs
of these four.

## Group 2: laws of one query form

Each family is one form. The column "Users" gives the number of package
declarations and the number of test declarations that name the declaration,
as found by the search. "Decision 1" marks a resolution law. The no-fault
check is `Resolved.Statement.calm_of_calmCheck` of the branch.

### Resolution blocks that more than one form uses

These two laws resolve a part that the forms below share: a `SELECT` with no
`FROM` and one subquery, and the result column `1`.

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `resolveSelect_noFrom_one_subquery` | `M/Queries/Select/SubquerySelectResolution.lean` | 4 / 0 |
| `resolveColumns_one` | `M/Queries/Select/SimpleSourceResolution.lean` | 8 / 2 |

Test declarations that use these laws (1); their proofs change:

`BalanceExample.main_body`.

### `EXISTS` claim on one table

Form: `SELECT 1 WHERE [NOT] EXISTS (SELECT 1 FROM t WHERE p)`.

The effect claim of the pilot has this form, and the tactic `sql_holds`
proves it on the pilot branch. The replacement laws are on the branch. The
tactic gives `Holds` only (decision 2).

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `resolveStatement_selectOne_subquery` | `M/Schema/Dispatch/ExistsStatementResolution.lean` | 2 / 0 |
| `resolveStatement_selectOne_exists` | `M/Schema/Dispatch/ExistsStatementResolution.lean` | 0 / 2 |
| `resolveStatement_selectOne_notExists` | `M/Schema/Dispatch/ExistsStatementResolution.lean` | 0 / 3 |

No-fault laws. Replaced by `Resolved.Statement.calm_of_calmCheck`, which is
on the branch. The branch has no such check for `Quiet`; the law for `Quiet`
goes when one exists.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Statement.Calm.selectOne_subquery` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | 0 / 7 |
| `Resolved.Statement.Quiet.selectOne_subquery` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | 0 / 1 |
| `Resolved.Query.simple_first_expressions` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | 2 / 0 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `tableOne_run` | `T/Queries/Evaluation/SelectOneWhereSupport.lean` | 0 / 4 |
| `whereOne_claims` | `T/Queries/Evaluation/SelectOneWhereSupport.lean` | 0 / 7 |
| `BalanceExample.one_run` | `T/Queries/Evaluation/SuccessBalanceSubqueries.lean` | 0 / 2 |
| `BalanceExample.one_body` | `T/Queries/Select/SuccessBalanceResolution.lean` | 0 / 2 |

Test declarations that use these laws (9); their proofs change:

`AssertionExamples.no_customer_has_the_id_iff`,
`BalanceExample.guard_bodies`, `BalanceExample.metadata_run`,
`BalanceExample.range_body`, `BalanceExample.range_run`,
`abs_exists_unmodeled`, `exists_invoice_observations`,
`no_invoice_is_negative`, `not_exists_invoice_observations`.

### `SELECT 1 FROM t WHERE p` as the claim

Form: `SELECT 1 FROM t WHERE p`.

The laws of a simple query on one table give the evaluation. The tactic
needs a case for a claim that is a query with a `FROM` clause; the branch
has the case for `SELECT 1 WHERE c` only.

Resolution law. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `resolveStatement_select_one_from` | `M/Schema/Dispatch/SelectOneResolution.lean` | 0 / 4 |

No-fault laws. Replaced by the no-fault check, after the case of the tactic.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Statement.Calm.selectOne` | `M/Queries/Evaluation/SelectOneResolution.lean` | 0 / 3 |
| `Resolved.Statement.Quiet.selectOne` | `M/Queries/Evaluation/SelectOneResolution.lean` | 0 / 1 |

Test declarations that use these laws (4); their proofs change:

`AssertionExamples.a_customer_has_the_id_and_name_iff`,
`AssertionExamples.a_customer_named_iff`,
`SelectExistenceCases.zeroAmount_results`, `abs_where_unmodeled`.

### `count(*)` of the rows that a condition selects

Form: `SELECT 1 WHERE c`, where `c` reads `(SELECT count(*) FROM t WHERE p)`.

An operator law for `count(*)` must exist first: the value of the subquery
is the number of the rows that the condition keeps. The pilot did not write
it.

Definitions of the form. Deleted with the laws.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.countMatching` | `M/Queries/Evaluation/CountOf.lean` | 6 / 5 |
| `Resolved.Query.countOf` | `M/Queries/Evaluation/CountOf.lean` | 4 / 6 |
| `Resolved.SubqueryRun.count` | `M/Queries/Evaluation/CountOf.lean` | 1 / 9 |
| `countShape` | `M/Queries/Select/CountStatementResolution.lean` | 2 / 10 |
| `equalsParameter` | `M/Queries/Evaluation/PlainInsertRows.lean` | 1 / 5 |

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `resolveColumns_countStar` | `M/Queries/Preparation/CountSelectResolution.lean` | 1 / 0 |
| `resolveQueryBody_count` | `M/Queries/Preparation/CountSelectResolution.lean` | 1 / 1 |
| `subqueryShape_count` | `M/Queries/Select/CountStatementResolution.lean` | 1 / 0 |
| `resolveStatement_selectOne_count` | `M/Schema/Dispatch/CountStatementResolution.lean` | 0 / 1 |

Evaluation and no-fault laws. Replaced by the operator law for `count(*)`,
the law of a comparison and the no-fault check.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.countMatching_eq` | `M/Queries/Evaluation/CountMatchingLaws.lean` | 3 / 1 |
| `Resolved.countMatching_none` | `M/Queries/Evaluation/CountMatchingLaws.lean` | 0 / 1 |
| `Resolved.Query.countOf_expressions` | `M/Queries/Evaluation/CountOf.lean` | 1 / 2 |
| `Resolved.Statement.Calm.selectOne_count` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | 0 / 1 |
| `Resolved.truthy_count_le_one` | `M/Queries/Evaluation/UniqueLookupCount.lean` | 0 / 2 |
| `countMatching_appended` | `M/Queries/Evaluation/PlainInsertRows.lean` | 0 / 1 |
| `equalsParameter_true` | `M/Queries/Evaluation/PlainInsertRows.lean` | 0 / 3 |

Facts about unique keys that are stated through the count. The fact stays: a
unique key lets at most one row match. The statement changes, to a bound on
the rows that the condition keeps (decision 4).

| Declaration | File | Users |
| --- | --- | --- |
| `Table.KeysUnique.countMatching_le_one` | `M/Schema/Rows/UniqueLookupCount.lean` | 0 / 1 |
| `Table.KeysUnique.countMatching_partial_le_one` | `M/Schema/Rows/PartialUniqueCount.lean` | 1 / 0 |
| `Database.Valid.countMatching_partial_le_one` | `M/Schema/Rows/ValidUniqueKeys.lean` | 0 / 0 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `countOne_run` | `T/Queries/Evaluation/SelectCountWhereSupport.lean` | 0 / 1 |
| `whereCount_claims` | `T/Queries/Evaluation/SelectCountWhereSupport.lean` | 0 / 7 |
| `BalanceExample.count_run` | `T/Queries/Evaluation/SuccessBalanceSubqueries.lean` | 0 / 1 |
| `unique_lookup_holds` | `T/Schema/Tests/ClaimsUniqueLookup.lean` | 0 / 2 |

Test declarations that use these laws (19); their proofs change:

`AssertionExamples.a_customer_has_the_id_and_name_iff`,
`AssertionExamples.a_customer_named_iff`,
`AssertionExamples.at_most_one_live_account_iff`,
`AssertionExamples.customer_count_is_iff`,
`AssertionExamples.customer_named_after_insert`,
`AssertionExamples.inserted_customer_has_the_name`,
`AssertionExamples.inserted_customer_is_unique`,
`AssertionExamples.no_customer_has_the_id_iff`,
`AssertionExamples.one_customer_has_the_id_iff`,
`BalanceExample.guardQueries`, `BalanceExample.guard_bodies`,
`BalanceExample.guard_calm`, `BalanceExample.guard_context`,
`BalanceExample.guard_from_runs`, `an_email_matches_at_most_one_user`,
`an_id_matches_at_most_one_user`, `invoice_count_empty_and_safe`,
`invoices_has_n_rows`, `invoices_with_negative_amount_are_n`.

### Scalar subquery in the condition

Form: `SELECT 1 WHERE c`, where `c` reads `(SELECT e FROM t WHERE p)`.

An operator law for the value of a scalar subquery must exist first: the
first row of the subquery, or NULL.

Definition of the form. Deleted with the laws.

| Declaration | File | Users |
| --- | --- | --- |
| `scalarShape` | `M/Queries/Select/ScalarSubqueryResolution.lean` | 2 / 3 |

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `subqueryShape_scalar` | `M/Queries/Select/ScalarSubqueryResolution.lean` | 1 / 0 |
| `resolveStatement_selectOne_scalar` | `M/Schema/Dispatch/ScalarSubqueryResolution.lean` | 0 / 1 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `columnOne_run` | `T/Queries/Tests/SelectColumnWhereSupport.lean` | 0 / 1 |
| `whereColumn_claims` | `T/Queries/Tests/SelectColumnWhereSupport.lean` | 0 / 2 |

Test declarations that use these laws (2); their proofs change:

`invoice_membership_empty_and_safe`, `x_is_an_invoice_id`.

### One column of one table

Form: `SELECT c FROM t WHERE f`.

The laws of a simple query on one table, which stay, give the rows. These
laws state the same for a result list of exactly one column.

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `resolveColumns_identifier_at` | `M/Queries/Preparation/SelectColumnResolution.lean` | 1 / 1 |
| `resolveStatement_select_column` | `M/Schema/Dispatch/SelectColumnResolution.lean` | 0 / 9 |

No-fault law. Replaced by the no-fault check.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Statement.simpleColumn_calm` | `M/Queries/Evaluation/SimpleTableCalm.lean` | 0 / 5 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `SelectAutomation.schema_projection` | `T/Queries/Tests/SelectAutomationSchema.lean` | 0 / 1 |
| `SelectAutomation.collection_count` | `T/Queries/Evaluation/SelectAutomationCore.lean` | 0 / 0 |
| `SelectAutomation.where_fact` | `T/Queries/Evaluation/SelectAutomationCore.lean` | 0 / 1 |
| `SelectAutomation.where_nonnull` | `T/Queries/Evaluation/SelectAutomationCore.lean` | 0 / 0 |
| `S6RulesQuerySites.resolve_column_lookup` | `T/Queries/Tests/S6ColumnLookups.lean` | 0 / 1 |
| `LowercaseFixture.resolve_original_filter_at` | `T/Queries/Tests/LowercaseLookups.lean` | 0 / 1 |
| `LowercaseFixture.resolve_stored_filter_at` | `T/Queries/Tests/LowercaseLookups.lean` | 0 / 1 |
| `LowercaseFixture.resolve_original_lookup` | `T/Queries/Tests/LowercaseLookups.lean` | 0 / 2 |
| `LowercaseFixture.resolve_stored_lookup` | `T/Queries/Tests/LowercaseLookups.lean` | 0 / 2 |
| `LowercaseFixture.originalFilter_calm` | `T/Queries/Tests/LowercaseLookups.lean` | 0 / 2 |
| `LowercaseFixture.storedFilter_calm` | `T/Queries/Tests/LowercaseLookups.lean` | 0 / 2 |
| `LowercaseFixture.simpleColumn_calm` | `T/Queries/Tests/LowercaseLookups.lean` | 0 / 0 |
| `LowercaseFixture.storedFilter_append` | `T/Schema/Columns/LowercaseFilters.lean` | 0 / 2 |
| `LowercaseFixture.originalFilter_append` | `T/Schema/Columns/LowercaseFilters.lean` | 0 / 1 |
| `LowercaseFixture.results_translate` | `T/Schema/Columns/LowercaseFilters.lean` | 0 / 1 |
| `LowercaseFixture.results_preserve` | `T/Schema/Columns/LowercaseFilters.lean` | 0 / 0 |
| `ConcatFixture.storedFilter_append_pipes` | `T/Queries/Tests/ConcatFilters.lean` | 0 / 1 |
| `ConcatFixture.pipesFilter_append` | `T/Queries/Tests/ConcatFilters.lean` | 0 / 0 |
| `ConcatFixture.resolve_pipes_filter_at` | `T/Queries/Tests/ConcatFilters.lean` | 0 / 1 |
| `ConcatFixture.pipesFilter_calm` | `T/Queries/Tests/ConcatFilters.lean` | 0 / 1 |
| `ConcatFixture.resolve_pipes_lookup` | `T/Queries/Tests/ConcatFilters.lean` | 0 / 1 |

Test declarations that use these laws (12); their proofs change:

`AssertionExamples.one_live_iff`, `ConcatFixture.ConcatSite.lookupMove`,
`LowercaseFixture.LowercaseSite.lookupMove`,
`LowercaseFixture.LowercaseSite.originalPreserved`,
`NormalizedFieldFixture.lookup_for_every_parameter`,
`S6RulesQuerySites.columnPreserved`, `SelectAutomation.schema_instances`,
`SelectCardinalityCases.customers_perm`,
`SelectCardinalityCases.paying_length_le`,
`SelectComparisonCases.amounts_above`, `SelectFilterCases.present_notes`,
`SelectProjectionCases.customer_present_of_columns`.

### One aggregate of one table

Form: `SELECT agg(x) FROM t WHERE p`.

An operator law for an aggregate over the kept rows must exist first.

Definition of the form. Deleted with the laws.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Query.aggregateOf` | `M/Queries/Select/AggregateSelectResolution.lean` | 3 / 4 |

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `resolveColumns_aggregate` | `M/Queries/Select/AggregateSelectResolution.lean` | 1 / 0 |
| `decidingCall_aggregateColumn` | `M/Queries/Select/AggregateSelectResolution.lean` | 1 / 0 |
| `resolveQueryBody_aggregate` | `M/Queries/Select/AggregateSelectResolution.lean` | 1 / 0 |
| `resolveStatement_select_aggregate` | `M/Schema/Dispatch/AggregateSelectResolution.lean` | 0 / 2 |

No-fault law. Replaced by the no-fault check.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Statement.Calm.aggregateOf_first` | `M/Queries/Select/AggregateSelectResolution.lean` | 0 / 2 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `SelectSumCases.sumQuery_calm` | `T/Queries/Evaluation/SelectSumCases.lean` | 0 / 2 |
| `SelectGroupCases.result_ungrouped` | `T/Queries/Tests/SelectGroupSupport.lean` | 0 / 6 |

Test declarations that use these laws (11); their proofs change:

`BalanceExample.balance_of_bounds`, `SelectCountCases.count_customers`,
`SelectCountCases.count_rows`, `SelectExtremumCases.joined_customers`,
`SelectExtremumCases.min_amount`,
`SelectNullAggregateCases.empty_aggregates`,
`SelectNullAggregateCases.null_customers`,
`SelectSumCases.sumCents_overflow`, `SelectSumCases.sumCents_resolved`,
`SelectSumCases.sumCents_results`, `SelectSumCases.sumQuery`.

### Duplicate keys

Form: `SELECT 1 WHERE NOT EXISTS (SELECT e FROM t WHERE w GROUP BY k HAVING count(*) > 1)`.

Operator laws for `GROUP BY` and `HAVING` must exist first. The package has
the resolution of this form; its evaluation laws are in the test fixtures.

Definitions of the form. Deleted with the laws.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Query.duplicateKeys` | `M/Queries/Evaluation/DuplicateKeyQuery.lean` | 2 / 2 |
| `GroupTermResolvesIn` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | 6 / 2 |
| `GroupTermResolves` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | 2 / 1 |

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `GroupTermResolvesIn.expression` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | 0 / 0 |
| `GroupTermResolves.toIn` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | 0 / 2 |
| `GroupTermResolvesIn.identifier_table` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | 1 / 1 |
| `GroupTermResolves.identifier_table` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | 0 / 1 |
| `resolveOperand_moreThanOne` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | 1 / 0 |
| `decidingCall_duplicateKeys` | `M/Queries/Select/DuplicateKeyResolution.lean` | 1 / 0 |
| `resolveQueryBody_duplicateKeys` | `M/Queries/Select/DuplicateKeyResolution.lean` | 1 / 0 |
| `resultColumn_one_facts` | `M/Queries/Select/DuplicateKeyResolution.lean` | 0 / 2 |
| `resolveStatement_selectOne_notExists_duplicateKeys` | `M/Schema/Dispatch/DuplicateKeyResolution.lean` | 0 / 1 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `duplicateKeys_calm` | `T/Queries/Tests/SelectDuplicateKeySupport.lean` | 0 / 2 |
| `duplicateKeysOne_run` | `T/Queries/Tests/SelectDuplicateKeySupport.lean` | 0 / 1 |
| `noDuplicateKeys_claims` | `T/Queries/Tests/SelectDuplicateKeySupport.lean` | 0 / 3 |
| `keyGroupsShort_iff_pairwise` | `T/Queries/Tests/SelectDuplicateKeySupport.lean` | 0 / 3 |
| `SelectGroupCases.keyCounts_of_mem` | `T/Queries/Tests/SelectGroupCases.lean` | 0 / 2 |
| `SelectGroupCases.countQuery_fails` | `T/Queries/Tests/SelectGroupCases.lean` | 0 / 2 |
| `SelectGroupCases.uniqueRecords_grouped` | `T/Queries/Tests/SelectGroupSupport.lean` | 0 / 2 |
| `SelectGroupCases.countCondition_truthy` | `T/Queries/Tests/SelectGroupSupport.lean` | 0 / 2 |
| `SelectHavingCases.keptCounts_of_mem` | `T/Queries/Tests/SelectHavingCases.lean` | 0 / 1 |

Test declarations that use these laws (9); their proofs change:

`AssertionExamples.one_live_iff`, `SelectGroupCases.customer_counts`,
`SelectGroupCases.large_counts`, `SelectHavingCases.repeat_customers`,
`email_claims`, `group_nocase`, `no_two_users_share_an_email`,
`two_users_share_an_email`, `uniqueEmail_ok`.

### Claim on the columns of a table

Form: `SELECT 1 FROM pragma_table_info('t') WHERE name = 'c'`.

For a claim with the full catalog as premise, the rows of
`pragma_table_info` are a computed value, and the tactic needs a case for
this source.

Definition of the form. Deleted with the laws.

| Declaration | File | Users |
| --- | --- | --- |
| `tableInfoScope` | `M/Queries/Preparation/TableInfoResolution.lean` | 8 / 5 |

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `tableInfoScope_resolveName_name` | `M/Queries/Preparation/TableInfoLaws.lean` | 1 / 0 |
| `resolveOperand_tableInfo_name` | `M/Queries/Preparation/TableInfoLaws.lean` | 0 / 0 |
| `tableInfoScope_collation_name` | `M/Queries/Preparation/TableInfoLaws.lean` | 0 / 0 |
| `resolveSources_tableInfo` | `M/Queries/Preparation/TableInfoResolution.lean` | 1 / 1 |
| `tableInfoScope_resolveName_type` | `M/Queries/Select/TableInfoColumnLaws.lean` | 1 / 1 |
| `resolveOperand_tableInfo_type` | `M/Queries/Select/TableInfoColumnLaws.lean` | 0 / 1 |
| `tableInfoScope_collation_type` | `M/Queries/Select/TableInfoColumnLaws.lean` | 0 / 1 |
| `resolveStatement_select_one_tableInfo` | `M/Schema/Dispatch/TableInfoResolution.lean` | 0 / 1 |

No-fault law. Replaced by the no-fault check.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Statement.Calm.selectOne_pragma` | `M/Queries/Evaluation/SelectSourceRules.lean` | 0 / 1 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `tableInfo_results` | `T/Schema/Tests/ClaimsTableInfo.lean` | 0 / 2 |
| `table_has_a_stored_column_named` | `T/Schema/Tests/ClaimsTableInfo.lean` | 0 / 3 |

Test declarations that use these laws (9); their proofs change:

`BalanceExample.guard_bodies`, `BalanceExample.guard_scopes`,
`BalanceExample.name_resolves`, `BalanceExample.pragmaScope`,
`BalanceExample.typed_resolves`, `invoices_has_a_status_column`,
`status_column_empty_and_safe`, `the_name_test_is_case_sensitive`,
`upper_case_table_name_reads_the_same_table`.

### `IN` and `EXISTS` on a second table

Form: `SELECT p FROM t WHERE x [NOT] IN (SELECT c FROM u)`, and the same with `EXISTS`.

These laws prove that a query with `IN` and a query with `EXISTS` return the
same rows. The claim is an equivalence of two queries, not a claim that
holds on one database (decision 3).

Definitions of the form. Deleted or kept with the laws that name them.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.CorrelatedEquality` | `M/Queries/Evaluation/InSubqueryFilterLaw.lean` | 4 / 0 |
| `correlatedScope` | `M/Queries/Select/FromSubqueryStatementResolution.lean` | 3 / 0 |

Resolution laws. Decision 1.

| Declaration | File | Users |
| --- | --- | --- |
| `resolveStatement_selectFrom_inQuery` | `M/Schema/Dispatch/InSubqueryStatementResolution.lean` | 0 / 0 |
| `resolveStatement_selectFrom_existsTest` | `M/Schema/Dispatch/CorrelatedExistsResolution.lean` | 0 / 0 |
| `FilterResolves.exists_only` | `M/Schema/Dispatch/CorrelatedExistsResolution.lean` | 0 / 0 |
| `FilterResolves.notExists_only` | `M/Schema/Dispatch/CorrelatedExistsResolution.lean` | 0 / 0 |
| `resolveStatement_selectFrom_subquery` | `M/Schema/Dispatch/FromSubqueryStatementResolution.lean` | 2 / 0 |
| `resolveSelect_from_one_subquery` | `M/Queries/Select/FromSubquerySelectResolution.lean` | 1 / 0 |

Value of `IN` and of `EXISTS` on one table. These are near the operator
level: they give the value for a subquery on one table that reads the outer
row. They and the laws of `EXISTS` on the branch become one set of laws: one
for `IN`, one for `EXISTS`, each for a subquery with or without a use of the
outer row.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Expr.evaluate_inQuery_oneTable` | `M/Schema/Dispatch/InSubqueryEvaluate.lean` | 3 / 0 |
| `Resolved.Expr.evaluate_exists_oneTable` | `M/Schema/Dispatch/InSubqueryEvaluate.lean` | 2 / 0 |
| `Resolved.Expr.evaluate_notExists_oneTable` | `M/Schema/Dispatch/InSubqueryEvaluate.lean` | 2 / 0 |
| `Resolved.any_kept_equals_iff` | `M/Queries/Evaluation/InSubqueryFilterLaw.lean` | 2 / 0 |
| `Resolved.correlatedEquality_of_compare` | `M/Queries/Evaluation/InSubqueryEqualityLink.lean` | 2 / 0 |

No-fault laws. Replaced by the no-fault check.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Query.equalsColumn_calm` | `M/Queries/Evaluation/InSubqueryQueryLaw.lean` | 2 / 0 |
| `Resolved.Query.inColumn_calm` | `M/Queries/Evaluation/InSubqueryQueryLaw.lean` | 2 / 0 |
| `Resolved.Expr.fault_inQuery_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | 2 / 0 |
| `Resolved.Expr.fault_exists_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | 2 / 0 |

Equivalence laws. Decision 3.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Expr.evaluate_notIn_eq_notExists` | `M/Schema/Dispatch/InSubqueryFilterLaw.lean` | 1 / 0 |
| `Resolved.Expr.evaluate_in_truthy_eq_exists` | `M/Schema/Dispatch/InSubqueryFilterLaw.lean` | 1 / 0 |
| `Resolved.Expr.evaluate_notIn_eq_notExists_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | 1 / 0 |
| `Resolved.Expr.evaluate_in_truthy_eq_exists_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | 1 / 0 |
| `resolvedStepOutput_in_eq_exists` | `M/Programs/StatementRunLaws/InSubqueryQueryInLaw.lean` | 1 / 0 |
| `resolvedStepOutput_notIn_eq_notExists` | `M/Programs/StatementRunLaws/InSubqueryQueryLaw.lean` | 1 / 0 |
| `resolvedStepOutput_in_eq_exists_of_rowidAlias` | `M/Programs/StatementRunLaws/InSubqueryQueryRowidAlias.lean` | 1 / 0 |
| `resolvedStepOutput_notIn_eq_notExists_of_rowidAlias` | `M/Programs/StatementRunLaws/InSubqueryQueryRowidAlias.lean` | 1 / 0 |
| `Sql.EquivAt.in_exists_of_rowidAlias` | `S/Programs/StatementRunLaws/NotInQuery.lean` | 0 / 1 |
| `Sql.EquivAt.notIn_notExists_of_rowidAlias` | `S/Programs/StatementRunLaws/NotInQuery.lean` | 0 / 1 |

Support laws of the form in the test fixtures, which go with the package
laws:

| Declaration | File | Users |
| --- | --- | --- |
| `ReplacedSubqueryEquivalence.Sql_EquivAt_in_exists_of_rowidAlias` | `T/Queries/Tests/ReplacedSubqueryEquivalence.lean` | 0 / 0 |

Test declarations that use these laws (1); their proofs change:

`S6NotBlocked.notBlocked_equivalent`.

### Laws that the readers put in the class and that stay

The unit of the tactic, `SELECT 1 WHERE c`. The tactic names the definition
`Resolved.Query.selectOneWhere`, and the new output law
`resolvedStepOutput_selectOneWhere_hasRows` uses the second law.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Query.selectOneWhere_expressions` | `M/Queries/Evaluation/PlainQueryRules.lean` | 5 / 1 |
| `Resolved.Query.selectOneWhere_faultless` | `M/Queries/Evaluation/PlainQueryRules.lean` | 1 / 2 |

`PRAGMA foreign_key_check`. One pragma, not a form of claim. The check of a
schema-only script (`runScriptStep_succeedsBySchema`) uses these laws.

| Declaration | File | Users |
| --- | --- | --- |
| `resolvedStepOutput_keyCheck_rows` | `M/Programs/StatementRunLaws/ForeignKeyCheckContinues.lean` | 1 / 0 |
| `resolvedStepOutput_keyCheck_hasNoRows` | `M/Programs/StatementRunLaws/ForeignKeyPragmaQuery.lean` | 1 / 0 |
| `resolvedStepOutput_keyCheck_clock` | `M/Programs/StatementRunLaws/ForeignKeyPragmaQuery.lean` | 1 / 0 |
| `resolvedStepOutput_keyCheck_empty` | `M/Tooling/Counterexamples/ForeignKeyPragmaQuery.lean` | 0 / 1 |
| `keyCheckQuery_calm` | `M/Schema/Rows/ForeignKeyPragmaQuery.lean` | 4 / 0 |
| `keyCheckQuery_source` | `M/Schema/Rows/ForeignKeyPragmaQuery.lean` | 2 / 0 |
| `resolvePragma_keyCheck_iff` | `M/Schema/Rows/ForeignKeyPrepareLaws.lean` | 0 / 1 |
| `resolvePragma_tableKeyCheck_iff` | `M/Schema/Rows/ForeignKeyPrepareLaws.lean` | 0 / 0 |

Laws of one operator that are in the file of a form. Each is already a law
of one operator: the filter with no condition, and the groups of a column
against a unique key. They stay. The first moves when the file of the
duplicate-key form goes.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.keptRows_none` | `M/Queries/Evaluation/DuplicateKeyQuery.lean` | 0 / 5 |
| `LiteralData.uniqueRows_of_column_groups` | `M/Schema/Rows/GroupKeyConflictLaws.lean` | 0 / 2 |

Laws of `SUM` with a premise in the form of one condition. They are laws of
the value functions. The premise is the condition `NOT BETWEEN` as a value.
They stay.

| Declaration | File | Users |
| --- | --- | --- |
| `Value.numeric_of_not_between` | `M/Queries/Evaluation/SumRangeLaws.lean` | 1 / 0 |
| `sumOf_no_overflow_of_between` | `M/Queries/Evaluation/SumRangeLaws.lean` | 0 / 2 |

Four more test laws are laws of one form with no package law of the same
form: a function call with no `FROM`, a term of a compound query, and a
derived table. They show forms that the tactic does not reach today:

| Declaration | File | Users |
| --- | --- | --- |
| `SelectFunctionFaultCases.absQuery_quiet` | `T/Programs/Claims/SelectFunctionFaultCases.lean` | 0 / 3 |
| `SelectFunctionFaultCases.abs_context` | `T/Programs/Claims/SelectFunctionFaultCases.lean` | 0 / 3 |
| `SelectCompoundCases.columnTerm_run` | `T/Queries/Tests/SelectCompoundSupport.lean` | 0 / 1 |
| `SelectDerivedCases.derived_returns` | `T/Queries/Tests/SelectDerivedSupport.lean` | 0 / 3 |

## Group 3: laws of writes

### Point 4: the rows that a write leaves, with the bound values

Point 4 adds one fact for each kind of write. It changes no statement of
today. The 35 kind rules of ADR 0033 keep their statements. 20 of them are
rules of a write of rows, for example `runScriptStep_plainDelete_eq`: they
give the reached rows in the context of the statement, and the new fact
rewrites that to the bound values.

Two laws of today are cases of the new fact for `INSERT`, for exactly two
and exactly three parameters. They go when the general fact exists:

| Declaration | File | Users |
| --- | --- | --- |
| `rowsAt_two_parameters` | `M/Schema/Writes/PlainInsertRows.lean` | 0 / 2 |
| `rowsAt_three_parameters` | `M/Schema/Writes/PlainInsertRows.lean` | 0 / 1 |

On the branch, `LiteralData.mem_deleted` states the rows that a delete keeps
in the context of the statement. The fact of point 4 for `DELETE` is the
same law with the bound values; the pilot wrote it in form A as
`LiteralData.mem_deleted_rows`.

The readers found 67 package laws of one kind of write that name the context
of the statement, and 20 that are stated with values already. All stay.

### Point 5: the analysis of a write as a step of `sql_run`

Point 5 changes the tactic. It deletes no package law. The tactic applies
the laws that a client applies by hand today: the kind rule of the statement
and the 46 premise laws, for example `runScriptStep_continues`,
`RunStep.continues_of_rule`, `insertReady_of_fits`, `InsertFits.of_valid`,
`Sql.sendReached_single` and `ExecutionContext.initial_holds_valid`. Their
statements stay.

In the test fixtures, the structures that carry the resolution of one write
for a schema, and their helper laws, go for each claim that has the full
catalog as premise (decision 1):

| Declaration | File | Users |
| --- | --- | --- |
| `AssertionExamples.PurgeFrameSite` | `T/Schema/Tests/PurgeFrameSite.lean` | 0 / 8 |
| `AssertionExamples.CustomerInsertSite` | `T/Schema/Tests/CustomerInsertSite.lean` | 0 / 7 |
| `AssertionExamples.AddCustomerSite` | `T/Programs/Tests/AddCustomerQueries.lean` | 0 / 6 |
| `AssertionExamples.AccountSignupSite` | `T/Schema/Tests/SignupInvariantClaims.lean` | 0 / 5 |
| `AssertionExamples.GlobalSignupSite` | `T/Schema/Tests/GlobalSignupInvariant.lean` | 0 / 3 |

The fixture of the table `items` has no structure. It has 15 helper laws for
the one schema. Most are facts that the step of the tactic computes: the
catalog, the table, the clock, the readiness. `ItemInsertSite.items_values`
and `ItemInsertSite.items_inserted` are cases of the fact of point 4:

`ItemInsertSite.items_catalog`, `ItemInsertSite.items_cellsReady`,
`ItemInsertSite.items_clock`, `ItemInsertSite.items_counts_ok`,
`ItemInsertSite.items_fits`, `ItemInsertSite.items_id_integer`,
`ItemInsertSite.items_inserted`, `ItemInsertSite.items_keys`,
`ItemInsertSite.items_name_text`, `ItemInsertSite.items_plain`,
`ItemInsertSite.items_reads`, `ItemInsertSite.items_ready`,
`ItemInsertSite.items_table`, `ItemInsertSite.items_taken_outcome`,
`ItemInsertSite.items_values`.

The structures `LowercaseFixture.TextFieldSite`,
`LowercaseFixture.LowercaseSite` and `ConcatFixture.ConcatSite` are premises
of the migration pattern for a derived column, which is a checker of today.
Point 5 does not affect them. `S6NotBlocked.NotBlockedSite` carries the
resolution of two queries of the `IN` family (decisions 1 and 3).

## Laws that stay

- The 36 laws of one simple `SELECT` on one table, for example
  `resolvedStepOutput_oneTable_rows`, `Resolved.Query.oneTable_subqueryRun`
  and `resolveStatement_select_table`. A simple query is the unit of the
  operator laws.
- The 17 checkers of today and their soundness laws, for example
  `Script.succeeds_of_schema`, `KeptRead.preserves_of_check` and
  `DerivedColumnMigration.preserves_of_check`. Point 6 is about new checkers
  for patterns of claim.
- The 36 laws of a script pattern, such as the migration for a derived
  column.
- The 177 laws of one kind of write, with the two exceptions of point 4, and
  the 46 premise laws of the write rules.
- The 2,348 package theorems that are in none of these classes: the laws of
  values, expressions, rows, the catalog, DDL, triggers, foreign keys and
  the tools.
