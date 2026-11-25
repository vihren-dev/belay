# Claim proof pilot: laws that the recommendation affects

Date: 2026-11-25. Audience: the team. This record answers the question of
the owner: if the project adopts the recommendation of [the pilot
findings](claim-proof-pilot-findings.md), which laws of today change. It
lists each law by name.

Paths: `M/` is `packages/belay-sqlite-model/Belay/Sqlite/Model/`, `S/` is
`packages/belay/Belay/Sqlite/`, and `T/` is `tests/surface/`. "Today" is
revision `1e8dfd8d`, the top of the pull requests of ADR 0033. "The branch"
is the tactic branch of the pilot, revision `5bc3c323`. The numbers of this
record come from local scripts and from readers; they are not results of the
Nix checks.

## Result

The packages have 2,756 theorems today. The recommendation affects package
declarations in three groups:

1. **Changed on the branch.** The branch deletes 15 declarations (11
   theorems and 4 abbreviations), changes the statement of 1 abbreviation
   and the body of 1 definition, and moves 2 theorems to a different file
   with the same statement. This group is exact.
2. **Declarations of one query form.** 86 declarations: 74 theorems and 12
   definitions. None of them changes on the branch. Each has a status in the
   table below. 4 of them are cases of a general law that stays: they can go
   with no decision, after a retention test and the change of their users.
   Each of the others needs a decision of the owner, a statement that the
   pilot did not write, or both.
3. **Laws of writes.** 2 laws of the rows of an `INSERT` can go after a
   general law that does not exist today. Points 4 and 5 of the
   recommendation delete no other package law.

| Status | Meaning | Effect of the recommendation | Declarations |
| --- | --- | --- | --- |
| R | Resolution law of the form. | Decision 1. | 38 |
| F | `Calm` law of the form: the statement is calm when the expressions of its condition are calm. | Decision 1. The calm check of the branch proves `Calm` by computation only for a statement with no variable. | 5 |
| G | Case of a general law that stays. The proof of today derives the case from that law, with the premises of the case. | Can go with no decision. The work is a retention test and the change of each user to the general law. Each law that the derivation uses keeps its own status. | 4 |
| Q | `Quiet` law of the form, or a law that it needs. A quiet statement reads no clock and no counter; it can have a call that fails. | Stays. The branch has no check for `Quiet`. That the evaluation has no fault is a separate obligation of the user of the law. | 3 |
| V | Law about a definition of the form. | Goes, or gets a statement without the definition, after a retention test proves the statement of today. The text of the family gives the steps that the new statement must keep. | 5 |
| K | Fact about unique keys that is stated with the count of the form. | Decision 4. | 3 |
| E | Equivalence law of `IN` and `EXISTS`, or a declaration that only these laws use. | Decision 3. | 17 |
| D | Definition of the form. | Goes when no law names it. | 11 |

Of the 2,756 package theorems, 89 are in the three groups and 2,667 are not.
Of the 99 theorems that the readers put in the class "law of one query
form", 74 are in group 2, 7 are in group 1, and 18 are in no group; the
section of group 2 gives the reason for each of these.

Effect on the test fixtures (`tests/surface`): the branch deletes 5
declarations, changes the statement of 5, changes the body of 1 and moves 3;
one moved definition is among those with a new statement. 63 more test
declarations name a declaration of group 2, and 3 name a law of group 3.
Each changes when the declaration that it names changes. 2 anonymous
examples, 1 `#print axioms` check and 3 Python tests also use a declaration
of group 2; the families list them.

Three findings matter for the decision:

- No package declaration outside group 2 names a declaration of group 2.
  Outside the group, its users are the test fixtures, the set `sql_simp` and
  Python tests. One Python test, `tests/query_claims_theorems_test.py`,
  compiles a consumer of a law of group 2 outside `tests/surface`. A change
  of group 2 changes no other law of the model.
- 43 of the 86 declarations of group 2 are resolution laws and `Calm` laws
  (status R and F). They serve claims that are general in two ways: the
  database has a named table among other tables, and the condition of the
  query is a variable. The tactic of the branch needs the full catalog as
  premise and a statement with no variable, and it uses none of these laws.
  Decision 1 thus decides the largest part of the list, and it touches a
  capability group that the simplification goal names essential.
- 4 laws of group 2 are in the set `sql_simp`. 3 package declarations, 30
  test theorems and 4 anonymous examples use the set.

## Method and limits

Three sources give the list:

- A comparison of the declarations of today with the branch, for each
  declaration: deleted, added, moved, statement changed. This gives group 1.
- A classification of each theorem of today. Twelve readers read all 2,756
  theorems of the packages and all 1,208 theorems of `tests/surface`, and
  gave each a class: law of one query form (99 in the packages, 49 in the
  tests), law of one simple `SELECT` (36, 1), law of one kind of write (177,
  36), premise of a write rule (46, 10), checker with its soundness law (17,
  2), law of a script pattern (36, 11), or none of these. The author of this
  record read the statement and the users of each law of one query form
  again.
- A search by name for the users of each declaration, in two parts. The
  first part reads the text of each declaration of today. The second part
  reads all Lean and Python files of today under `packages`, `tests` and
  `tools`; in a Lean file it skips comments and docstrings. The second part
  finds anonymous examples, `#print axioms` checks, Lean code in Python
  tests, and uses through dot notation. The column "Users" of each table
  gives three numbers: package declarations, test declarations, and other
  users.

Limits:

- The class of a law is a judgment of a reader. A law of one query form is a
  law whose statement fixes a composition of two or more operators. A law
  that a reader put in a different class by mistake is not in the list.
- The search does not find a use that starts with a dot and takes the
  namespace from the expected type. For two declarations with a common last
  part of the name (`count`, `expression`), the author looked for uses
  through dot notation by hand and found none. A user count can thus be low.
- A test declaration is in a list when its text names a package declaration
  of the list. A test declaration that depends on a listed declaration only
  through a different test declaration is not in the list.
- A Python test is a user when its text names the law, also in a
  description. A Python test that builds a fixture and does not name the law
  is not in the lists.
- The search cannot show which proof needs a law of the set `sql_simp`. Only
  a build can show that.
- Only group 1 is built. For groups 2 and 3, the record gives the condition
  under which a law can go. No build shows that the condition can be met.

## Rule for each deletion

The [simplification goal](../development/lean-simplification-goal.md) counts
30 capability groups. A group keeps its point only when its complete
capability remains: a stronger proof assumption or a weaker conclusion gives
zero for the group. A deleted law does not reduce a group when its statement
stays derivable from the laws that remain. Retention that is not checked
counts as unknown. A loss needs a decision of the owner.

ADR 0033 (D8) gives the form of the evidence for its slices: a retention
test states the deleted law as it was, with the same premises, and proves it
from the new laws. When that proof is not possible, the work stops and the
owner decides. The branch follows this form for the four deleted theorems
that a fixture used. The other 7 deleted theorems have no user outside the
deleted set and no retention test. No retention test exists for a law of
group 2 or group 3. A retention test for each law is thus part of the work
of each deletion in these groups, and its result is evidence for the
capability group of the law. The other users of a law are part of the same
work: an anonymous example, a `#print axioms` check or a Python test that
uses the law must pass with the retention theorem or with the new law.

## Decisions that the list depends on

1. **Claims over a part of the catalog, with a variable condition.** The
   fixtures of today state many claims that are general in two ways. First,
   the claim is for each database that has a named table; the database can
   have other tables. Examples are `countOne_run` and `tableInfo_results`:
   their premise is the result of the lookup of the table (`findTable`), and
   the position of the table is a variable. Second, the condition of the
   query is a variable. An example is `tableOne_run`: its condition is a
   variable, with the premise that each expression of the condition is calm.
   The resolution laws of a statement (status R) take the resolution of the
   written filter as a premise, and the laws with status F take the calm
   expressions of the condition as a premise. The tactic `sql_holds` works
   in a different way: its hint is a proof that the database has one full
   catalog (`Database.HasCatalog`), and the kernel computes the resolution
   and the calm check on that catalog, for a statement with no variable.
   Such a proof uses no law with status R or F.

   If each claim takes the full catalog as premise, the lookups of the
   tables become computations. The claim is then about fewer databases: its
   assumption is stronger. By the rule above, that gives zero for each
   capability group that it touches. Group S04, "claims over every
   database", is one of the essential groups. Its inventory row names the
   claim laws of the count form and of the `pragma_table_info` form by their
   old names (`Holds.iff_selectOne_count`, `Holds.iff_selectOne_tableInfo`).

   The full catalog does not make the condition a constant. The kernel
   cannot compute the resolution or the calm check of a statement whose
   condition is a variable. The laws with status R and F thus go only when
   one more condition holds: a general law gives their statements for a
   variable condition with the premises of today, or the owner decides that
   claim laws with a variable condition go too. The second is also a weaker
   capability.

   If claims over a part of the catalog stay, the laws with status R and F
   stay, or a general law replaces them. For the forms with one `SELECT` and
   no subquery, the general laws exist: `resolveStatement_select_simple` and
   `Resolved.Statement.simpleTable_calm`; the laws with status G are their
   cases. For the forms with a subquery, the pilot did not examine whether a
   general law exists. The general law cannot be "the resolution depends
   only on the tables that the statement names". The resolved query holds
   the catalog position that `findTable` returns, and that position changes
   when a different table comes before the named table. The general law must
   assume, for the two catalogs, the same result of each lookup that the
   resolution makes: the position and the entry of each name that it finds,
   and each name that it does not find. As an alternative, it states the
   result up to a mapping of positions. The pilot did not examine such a
   law.

2. **`Empty` and `Fails`.** The claim laws of the fixtures give three facts
   for a claim: when it holds, when it is empty, and that it does not fail.
   `whereOne_claims` is the general one. The tactic `sql_holds` proves only
   that a claim holds. A fixture that replaces its claim law by the tactic
   keeps only this fact: a weaker conclusion, which is also a loss of
   capability. The tactic must give all three facts before it replaces a
   claim law.
3. **Equivalence of two queries.** The laws with status E compare a query
   with `IN` and a query with `EXISTS`. Capability group S10 ("query laws")
   has the laws of `NOT IN` and of the correlated `NOT EXISTS` in its
   inventory row. The laws of the model give equal values of the two
   conditions and equal rows of the two outputs. The two laws of the client
   library conclude more: `Sql.EquivAt` states that the two programs have
   the same run and the same complete outcomes of each branch, with the
   return values, the errors, the reasons to stop, the traces and each field
   of the connection. The laws can stay as they are. As an alternative, the
   library keeps the operator laws, and the equivalences become client
   theorems in the fixtures. That is a deletion from the packages, with the
   rule above: the client theorems must prove the complete equivalence of
   `Sql.EquivAt` with the premises of today, not only the equal rows.
4. **Facts about unique keys.** The three laws with status K state "at most
   one row matches" as a bound on `Resolved.countMatching`. If the
   definition goes, the statement becomes a bound on the rows that the
   condition keeps (`Resolved.keptRows`). Two laws of today state a fact
   about unique keys on the kept rows: `Table.KeysUnique.keptRows_pairwise`
   and `Database.Valid.keptRows_pairwise`. Their premises are different: the
   key column is declared NOT NULL, and the table satisfies `RowsWide` and
   `NotNull` in place of `RowsStored`. The pilot did not examine whether
   they give the three laws. The three laws have users that a new statement
   must keep: the Python test `tests/query_claims_theorems_test.py` compiles
   a consumer of `Table.KeysUnique.countMatching_le_one` with its full
   statement and checks its axioms, and
   `AssertionExamples.AccountSignupSite.keeps_of_valid` applies
   `Database.Valid.countMatching_partial_le_one` to prove the invariant of
   the signup.

## The set `sql_simp`

`S/Queries/Evaluation/SqlSimpLaws.lean` puts 4 declarations of group 2 into
the set `sql_simp`:

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `resolveOperand_tableInfo_name` | `M/Queries/Preparation/TableInfoLaws.lean` | R | 0 / 0 / 0 |
| `tableInfoScope_resolveName_name` | `M/Queries/Preparation/TableInfoLaws.lean` | R | 1 / 0 / 0 |
| `tableInfoScope_collation_name` | `M/Queries/Preparation/TableInfoLaws.lean` | R | 0 / 0 / 0 |
| `Resolved.countMatching_none` | `M/Queries/Evaluation/CountMatchingLaws.lean` | V | 0 / 1 / 0 |

A proof that uses the set can need one of them and not name it. These proofs
use the set. In the packages: `Run.finishingSteps` (the steps that finish a
goal that `sql_run` leaves), `Check.tryProof`, and `Run.runRoute`, which
names the set in a message only. In the tests, 30 named theorems:

`AssertionExamples.AccountSignupSite.keeps_of_valid`,
`AssertionExamples.GlobalSignupSite.keeps_of_valid`,
`AssertionExamples.a_customer_has_the_id_and_name_iff`,
`AssertionExamples.a_customer_named_iff`,
`AssertionExamples.at_most_one_live_account_iff`,
`AssertionExamples.customer_count_is_iff`,
`AssertionExamples.no_customer_has_the_id_iff`,
`AssertionExamples.one_customer_has_the_id_iff`,
`BalanceExample.balance_of_bounds`, `BalanceExample.main_filter`,
`BalanceExample.name_eval`, `BalanceExample.name_resolves`,
`BalanceExample.range_body`, `BalanceExample.typed_eval`,
`BalanceExample.typed_resolves`, `SelectExistenceCases.zeroAmount_results`,
`SelectProjectionCases.customer_present_of_columns`,
`SelectSumCases.integer_sum_failure`, `SelectSumCases.integer_sum_value`,
`an_email_matches_at_most_one_user`, `an_id_matches_at_most_one_user`,
`invoice_count_empty_and_safe`, `invoice_membership_empty_and_safe`,
`invoices_has_n_rows`, `invoices_with_negative_amount_are_n`,
`no_invoice_is_negative`, `tableInfo_results`,
`table_has_a_stored_column_named`, `unique_lookup_holds`,
`x_is_an_invoice_id`.

And 4 anonymous examples, which the count of named theorems does not
include: `T/Queries/Evaluation/ClaimsExpressionLaws.lean:15`,
`T/Queries/Evaluation/ClaimsExpressionLaws.lean:34`,
`T/Queries/Evaluation/ClaimsExpressionLaws.lean:43`,
`T/Queries/Evaluation/SelectSumInstances.lean:90`. The three examples of
`ClaimsExpressionLaws.lean` are the fixture of the Python test
`test_expression_laws_turn_a_condition_into_logic` of
`tests/surface_claims_test.py`.

Before one of the four laws goes, a build of these proofs must show which of
them need it. How the rewrites stay available:

- The three laws of `pragma_table_info` rewrite the resolution of the column
  `name` in the scope of the function. They stay in the set as long as the
  resolution laws of that family stay (decision 1). If decision 1 removes
  them, a proof with the full catalog as premise computes the resolution and
  needs no rewrite. A proof for each database that has the table has no
  replacement.
- `Resolved.countMatching_none` rewrites the count with no condition to the
  number of the stored rows of the table (`table.rows.length`).
  `AssertionExamples.customer_count_is_iff` names it for that step. It stays
  in the set as long as `Resolved.countMatching` stays. If the count becomes
  the length of the kept rows, `Resolved.keptRows_none`, which exists and is
  not in the set today, gives only a part of the step: the length of the
  scanned rows (`Resolved.sourceRows`). The rewrite to the number of the
  stored rows also needs `sourceRows_perm` and `List.length_map`. The change
  must put one law with the full step into the set.

## Group 1: changed on the branch

These changes are on the branch. They are exact.

### Deleted

The frame form `SELECT 1 WHERE NOT EXISTS (q1 EXCEPT q2)`:

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.notExistsExcept` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 2 / 1 / 0 |
| `Resolved.notExistsExceptSubqueries` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 4 / 0 / 0 |
| `Resolved.currentTerm` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 5 / 0 / 0 |
| `Resolved.initialTerm` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 6 / 0 / 0 |
| `Resolved.currentTerm_mem_results` | `M/Queries/Evaluation/TwoStateKeptRows.lean` | 1 / 0 / 0 |
| `Resolved.initialTerm_mem_results` | `M/Queries/Evaluation/TwoStateKeptRows.lean` | 2 / 0 / 0 |
| `Resolved.notExistsExcept_calm` | `M/Queries/Evaluation/TwoStateNotExistsExceptOutput.lean` | 1 / 0 / 0 |
| `Resolved.notExistsExcept_context_zero` | `M/Schema/Dispatch/TwoStateNotExistsExcept.lean` | 1 / 0 / 0 |
| `Resolved.notExistsExcept_identical` | `M/Schema/Columns/TwoStateKeptRows.lean` | 0 / 1 / 0 |
| `Resolved.notExistsExcept_subset` | `M/Schema/Columns/TwoStateKeptRows.lean` | 0 / 1 / 0 |
| `resolvedStepOutput_notExistsExcept_hasRows` | `M/Tooling/Counterexamples/TwoStateNotExistsExceptOutput.lean` | 0 / 1 / 0 |
| `resolvedStepOutput_query_hasRows_of_clean_from` | `M/Tooling/Counterexamples/TwoStateQuerySteps.lean` | 1 / 0 / 0 |

The branch proves the frame claim with these additions in place of the
deleted declarations: the law of the subquery of a simple query
(`Resolved.Query.simple_subqueryRun`,
`Resolved.Query.simple_subqueryRun_rowwise`), the laws of `EXISTS`
(`Resolved.Expr.truthy_exists`, `Resolved.Expr.truthy_notExists`), the
identity of rows that compare equal
(`Resolved.equalRowsIdentical_rowidFirst`), the calm check
(`Resolved.Statement.calm_of_calmCheck`), the output laws
`resolvedStepOutput_calm_hasRows` and
`resolvedStepOutput_selectOneWhere_hasRows`, and the membership in the rows
that a delete keeps (`LiteralData.mem_deleted`).

The condition `(a AND b) IS NOT 1`:

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Expr.truthy_isNot_one_and` | `M/Queries/Evaluation/RowwiseExpr.lean` | 0 / 1 / 0 |
| `Resolved.Value.and_cases` | `M/Queries/Evaluation/RowwiseExpr.lean` | 1 / 0 / 0 |
| `Resolved.truthy_isNot_one_of_cases` | `M/Queries/Evaluation/RowwiseExpr.lean` | 1 / 0 / 0 |

The branch adds in their place the property that a value is NULL, 0 or 1
(`Value.IsLogical`) and one law of `IS NOT 1` for such a value
(`Value.truthy_isNot_one`, `Resolved.Expr.truthy_isNot_one`).

The branch deletes six modules. Each held only declarations of this group:
`M/Queries/Evaluation/TwoStateKeptRows.lean`,
`M/Queries/Evaluation/TwoStateNotExistsExcept.lean`,
`M/Queries/Evaluation/TwoStateNotExistsExceptOutput.lean`,
`M/Schema/Columns/TwoStateKeptRows.lean`,
`M/Schema/Dispatch/TwoStateNotExistsExcept.lean`,
`M/Tooling/Counterexamples/TwoStateNotExistsExceptOutput.lean`.

### Moved, with the same statement

These two theorems move from
`M/Queries/Evaluation/TwoStateNotExistsExcept.lean` to
`M/Queries/Evaluation/RowwiseExpr.lean`. Their premises and conclusions are
the same at the two revisions:

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Query.simple_expressions_rowwise` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 2 / 0 / 0 |
| `Resolved.Query.simple_results_congr` | `M/Queries/Evaluation/TwoStateNotExistsExcept.lean` | 1 / 0 / 0 |

### Statement changed

- `Connection.queryContextFrom` (abbrev),
  `M/Schema/Dispatch/TwoStateQuerySteps.lean`. The start database is now
  optional, so that one definition serves a claim on one database and a
  claim that reads the start.

### Body changed, with the same type

- `Select.evaluationProof?` (def),
  `S/Programs/Automation/SqlSelectEval.lean`. The check of the equation is
  now synchronous. Before, the check ran in a background task, which
  reported the failure of a false equation only after the tactic had used
  the proposed proof. This is a fault fix that does not depend on the
  decision.

The branch adds 58 package declarations. The [findings
record](claim-proof-pilot-findings.md) gives the line counts.

### Test fixtures

Deleted, in `T/Schema/Tests/PurgeFrameInstances.lean`:

`AssertionExamples.fiftySite`, `AssertionExamples.modeledAtFifty`,
`AssertionExamples.null_customer_has_a_site`,
`AssertionExamples.null_time_has_a_site`,
`AssertionExamples.text_time_has_a_site`.

Statement changed (5). The structure `AssertionExamples.PurgeFrameSite`
loses the parameters `c` and `now` and the field `purgeModeled`; the new
theorem `AssertionExamples.PurgeFrameSite.purge_continues` proves what the
field assumed. The structure keeps the fields `claimAfter` and
`claimResolves`: the resolution of the claim is a premise that the site
still carries. The statements of three theorems that name the structure
change also:

`AssertionExamples.PurgeFrameSite`, `AssertionExamples.purge_frame`,
`AssertionExamples.purge_frame_typed`, `AssertionExamples.purge_keeps_rows`.

The definition `AssertionExamples.sessionsSite` moves and changes its
statement. Today it is the site for the one database `sessions` and two
values, and it takes as premise that the model runs the purge with them. On
the branch it is the site for each database that has the catalog of
`sessions`, with no premise about the run.

Body changed: `AssertionExamples.purgeKeepsResolved`. Moved to
`T/Schema/Tests/PurgeFrameSchema.lean`:

`AssertionExamples.sessions`, `AssertionExamples.sessionsEntry`,
`AssertionExamples.sessionsSite`.

The branch adds 35 test declarations. Nine of them are in the namespace
`PurgeLawRetention`: four abbreviations that state the deleted definitions
again, one helper theorem, and four retention theorems. The retention
theorems prove, from the laws that remain, the statements of the four
deleted theorems that a fixture used: `Resolved.Expr.truthy_isNot_one_and`,
`Resolved.notExistsExcept_identical`, `Resolved.notExistsExcept_subset`,
`resolvedStepOutput_notExistsExcept_hasRows`. At the start revision, the one
user of each outside the packages is `AssertionExamples.purge_keeps_rows`.

## Group 2: declarations of one query form

Each family is one form. The column "Status" has the codes of the table in
the section "Result". The column "Users" has the number of package
declarations, of test declarations and of other users. The calm check is
`Resolved.Statement.calm_of_calmCheck` of the branch. After each table, the
record lists the test declarations that name a declaration of the family,
and the other users: anonymous examples, `#print axioms` checks and Python
tests.

### Resolution blocks that more than one form uses

`resolveSelect_noFrom_one_subquery` resolves a `SELECT` with no `FROM` and
one subquery. `resolveColumns_one` resolves the result column `1`. The
resolution laws of the families below use them.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `resolveSelect_noFrom_one_subquery` | `M/Queries/Select/SubquerySelectResolution.lean` | R | 4 / 0 / 0 |
| `resolveColumns_one` | `M/Queries/Select/SimpleSourceResolution.lean` | R | 8 / 2 / 0 |

Test declarations that name these declarations (2):

`BalanceExample.main_body`, `BalanceExample.one_body`.

### `EXISTS` claim on one table

Form: `SELECT 1 WHERE [NOT] EXISTS (SELECT 1 FROM t WHERE p)`.

The effect claim of the pilot has this form. On the branch, the tactic
`sql_holds` proves it for a database with the full catalog as premise, with
the laws that the branch adds (`Resolved.Query.simple_subqueryRun`,
`Resolved.Expr.truthy_exists`, `Resolved.Expr.truthy_notExists`,
`resolvedStepOutput_selectOneWhere_hasRows`). The tactic proves that the
claim holds (decision 2). The laws of today serve the fixtures that state
the claim for each database that has the table, for example `tableOne_run`.

`Resolved.Statement.Quiet.selectOne_subquery` stays: `abs_exists_unmodeled`
uses it for a condition with a call of `abs`, which can fail.
`Resolved.Query.simple_first_expressions` stays with it; its users are the
`Calm` law and the `Quiet` law of this family.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `resolveStatement_selectOne_subquery` | `M/Schema/Dispatch/ExistsStatementResolution.lean` | R | 2 / 0 / 0 |
| `resolveStatement_selectOne_exists` | `M/Schema/Dispatch/ExistsStatementResolution.lean` | R | 0 / 2 / 0 |
| `resolveStatement_selectOne_notExists` | `M/Schema/Dispatch/ExistsStatementResolution.lean` | R | 0 / 3 / 0 |
| `Resolved.Statement.Calm.selectOne_subquery` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | F | 0 / 7 / 0 |
| `Resolved.Statement.Quiet.selectOne_subquery` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | Q | 0 / 1 / 0 |
| `Resolved.Query.simple_first_expressions` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | Q | 2 / 0 / 0 |

Test declarations that name these declarations (8):

`AssertionExamples.no_customer_has_the_id_iff`, `abs_exists_unmodeled`,
`columnOne_run`, `exists_invoice_observations`, `no_invoice_is_negative`,
`not_exists_invoice_observations`, `tableOne_run`, `whereColumn_claims`.

### `SELECT 1 FROM t WHERE p` as the claim

Form: `SELECT 1 FROM t WHERE p`.

The claim is a query with a `FROM` clause. The tactic `sql_holds` has no
case for it: its unit is a claim `SELECT 1 WHERE c`.

The proof of `resolveStatement_select_one_from` applies the general law of a
simple `SELECT`, `resolveStatement_select_simple`, which stays. The premises
that it gives to the general law come from `resolveSources_table`,
`resolvePendingSources_table` and `resolveColumns_one`. The lookup of the
table and the resolution of the filter stay premises, as today.

The statement of `Resolved.Statement.Calm.selectOne` is the case of
`Resolved.Statement.simpleTable_calm`, which stays, for the result column
`1`. Its proof of today does not use that law, and no build has checked the
derivation; the status is thus F.

`Resolved.Statement.Quiet.selectOne` stays: `abs_where_unmodeled` uses it
for a condition with a call of `abs`. The call is quiet and not calm,
because it can fail.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `resolveStatement_select_one_from` | `M/Schema/Dispatch/SelectOneResolution.lean` | G | 0 / 4 / 0 |
| `Resolved.Statement.Calm.selectOne` | `M/Queries/Evaluation/SelectOneResolution.lean` | F | 0 / 3 / 0 |
| `Resolved.Statement.Quiet.selectOne` | `M/Queries/Evaluation/SelectOneResolution.lean` | Q | 0 / 1 / 0 |

Test declarations that name these declarations (4):

`AssertionExamples.a_customer_has_the_id_and_name_iff`,
`AssertionExamples.a_customer_named_iff`,
`SelectExistenceCases.zeroAmount_results`, `abs_where_unmodeled`.

### `count(*)` of the rows that a condition selects

Form: `SELECT 1 WHERE c`, where `c` reads `(SELECT count(*) FROM t WHERE p)`.

The packages have the definition of the number of rows that a condition
selects (`Resolved.countMatching`) and laws about it. The law of the run of
the subquery (`countOne_run`) and the law of the claim (`whereCount_claims`)
are in the test fixtures, for each database that has the table.

`Resolved.countMatching` is, by definition, the length of the rows that the
condition keeps (`Resolved.keptRows`) among the scanned rows of the table
(`Resolved.sourceRows`). A statement about the number is thus a statement
about the kept rows, and it needs no new law. `Resolved.countMatching_eq`
and `Resolved.countMatching_none` give the number on the stored rows of the
table, not on the scanned rows. A statement on the kept rows must keep that
step: `sourceRows_perm` and `List.length_map` give it.
`countMatching_appended` is the number after one appended row.
`Resolved.truthy_count_le_one` evaluates the comparison of a given count
with 1. `Resolved.Query.countOf_expressions` gives the expressions of the
count query; the proofs that the query is calm use it.
`Resolved.countMatching_none` is in the set `sql_simp`.

The operator laws of `COUNT(*)` exist and stay: `Resolved.countRows_eval`
(the count of a group is its length) and `Resolved.records_ungrouped` (an
aggregate query with no `GROUP BY` and no `HAVING` has one record). A
package law for the run of a `count(*)` subquery does not exist. Only a
proof that evaluates the subquery needs it: `countOne_run` and
`whereCount_claims` in the fixtures. The pilot did not write that law.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `Resolved.countMatching` | `M/Queries/Evaluation/CountOf.lean` | D | 6 / 5 / 1 |
| `Resolved.Query.countOf` | `M/Queries/Evaluation/CountOf.lean` | D | 4 / 6 / 0 |
| `Resolved.SubqueryRun.count` | `M/Queries/Evaluation/CountOf.lean` | D | 1 / 9 / 0 |
| `countShape` | `M/Queries/Select/CountStatementResolution.lean` | D | 2 / 10 / 0 |
| `resolveColumns_countStar` | `M/Queries/Preparation/CountSelectResolution.lean` | R | 1 / 0 / 0 |
| `resolveQueryBody_count` | `M/Queries/Preparation/CountSelectResolution.lean` | R | 1 / 1 / 0 |
| `subqueryShape_count` | `M/Queries/Select/CountStatementResolution.lean` | R | 1 / 0 / 0 |
| `resolveStatement_selectOne_count` | `M/Schema/Dispatch/CountStatementResolution.lean` | R | 0 / 1 / 0 |
| `Resolved.Statement.Calm.selectOne_count` | `M/Queries/Evaluation/SelectOneSubqueryContext.lean` | F | 0 / 1 / 0 |
| `Resolved.Query.countOf_expressions` | `M/Queries/Evaluation/CountOf.lean` | V | 1 / 2 / 0 |
| `Resolved.countMatching_eq` | `M/Queries/Evaluation/CountMatchingLaws.lean` | V | 3 / 1 / 0 |
| `Resolved.countMatching_none` | `M/Queries/Evaluation/CountMatchingLaws.lean` | V | 0 / 1 / 0 |
| `Resolved.truthy_count_le_one` | `M/Queries/Evaluation/UniqueLookupCount.lean` | V | 0 / 2 / 0 |
| `countMatching_appended` | `M/Queries/Evaluation/PlainInsertRows.lean` | V | 0 / 1 / 0 |
| `Table.KeysUnique.countMatching_le_one` | `M/Schema/Rows/UniqueLookupCount.lean` | K | 0 / 1 / 1 |
| `Table.KeysUnique.countMatching_partial_le_one` | `M/Schema/Rows/PartialUniqueCount.lean` | K | 1 / 0 / 0 |
| `Database.Valid.countMatching_partial_le_one` | `M/Schema/Rows/ValidUniqueKeys.lean` | K | 0 / 1 / 1 |

Test declarations that name these declarations (18):

`AssertionExamples.AccountSignupSite.keeps_of_valid`,
`AssertionExamples.at_most_one_live_account_iff`,
`AssertionExamples.customer_count_is_iff`,
`AssertionExamples.inserted_customer_is_unique`,
`AssertionExamples.one_customer_has_the_id_iff`, `BalanceExample.count_run`,
`BalanceExample.guardQueries`, `BalanceExample.guard_bodies`,
`BalanceExample.guard_calm`, `BalanceExample.guard_from_runs`,
`an_email_matches_at_most_one_user`, `an_id_matches_at_most_one_user`,
`countOne_run`, `invoice_count_empty_and_safe`, `invoices_has_n_rows`,
`invoices_with_negative_amount_are_n`, `unique_lookup_holds`,
`whereCount_claims`.

- Other user of `Resolved.countMatching`,
  `Table.KeysUnique.countMatching_le_one`: the Python test
  `tests/query_claims_theorems_test.py`: it compiles a new consumer that
  applies the law with its full statement, and requires that the axiom
  report of the law has no `sorryAx`, `ofReduceBool` or native axiom.
- Other user of `Database.Valid.countMatching_partial_le_one`: the Python
  test `tests/surface_s6_automation_test.py`: its test
  `test_sql_run_proves_the_partial_index_invariant_of_a_signup` builds the
  fixtures that apply the law and names it in its description.

### One-column subquery in the condition

Form: `SELECT 1 WHERE c`, where `c` reads `(SELECT e FROM t WHERE p)` as a value or after `IN`.

The packages have the resolution of this form and the shape of its subquery.
The laws of the value are operator laws that exist and stay:
`Resolved.Expr.eval_subquery` (the first cell of the first row, or NULL),
`Resolved.Expr.eval_inQuery` (the membership among the first cells of all
rows), `Resolved.Expr.fault_inQuery` and `Resolved.truthy_inValue_eq_true`.
The law of the run of the subquery (`columnOne_run`) and the law of the
claim (`whereColumn_claims`) are in the test fixtures.

Two clients, `x_is_an_invoice_id` and `invoice_membership_empty_and_safe`,
use `IN`: a value in a row after the first can match. Their obligations are
the membership of the probe among the values of all kept rows, and no fault,
which needs certain rows of the run. A change of this family must keep both
obligations.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `scalarShape` | `M/Queries/Select/ScalarSubqueryResolution.lean` | D | 2 / 3 / 0 |
| `subqueryShape_scalar` | `M/Queries/Select/ScalarSubqueryResolution.lean` | R | 1 / 0 / 0 |
| `resolveStatement_selectOne_scalar` | `M/Schema/Dispatch/ScalarSubqueryResolution.lean` | R | 0 / 1 / 0 |

Test declarations that name these declarations (3):

`invoice_membership_empty_and_safe`, `whereColumn_claims`,
`x_is_an_invoice_id`.

### One column of one table

Form: `SELECT c FROM t WHERE f`.

`resolveStatement_select_column` and `Resolved.Statement.simpleColumn_calm`
state, for a result list of one column, what `resolveStatement_select_table`
and `Resolved.Statement.simpleTable_calm` state for each result list. Each
uses the general law in its proof, with the premises of the case, and adds
no assumption about the catalog. The two general laws stay. The derivation
of `resolveStatement_select_column` uses `resolveColumns_identifier_at` for
the result list.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `resolveColumns_identifier_at` | `M/Queries/Preparation/SelectColumnResolution.lean` | R | 1 / 1 / 0 |
| `resolveStatement_select_column` | `M/Schema/Dispatch/SelectColumnResolution.lean` | G | 0 / 9 / 0 |
| `Resolved.Statement.simpleColumn_calm` | `M/Queries/Evaluation/SimpleTableCalm.lean` | G | 0 / 5 / 0 |

Test declarations that name these declarations (10):

`AssertionExamples.one_live_iff`, `ConcatFixture.resolve_pipes_lookup`,
`LowercaseFixture.resolve_original_lookup`,
`LowercaseFixture.resolve_stored_lookup`,
`S6RulesQuerySites.resolve_column_lookup`,
`SelectCardinalityCases.customers_perm`,
`SelectCardinalityCases.paying_length_le`,
`SelectComparisonCases.amounts_above`, `SelectFilterCases.present_notes`,
`SelectProjectionCases.customer_present_of_columns`.

### One aggregate of one table

Form: `SELECT agg(x) FROM t WHERE p`.

The operator laws of the aggregates exist and stay, for example
`Resolved.Aggregate.eval_sum`, `Resolved.countRows_eval` and
`Resolved.records_ungrouped`. The general law of an aggregate query with no
`GROUP BY` is in the test fixtures (`SelectGroupCases.result_ungrouped`). It
does not fix the sources or the number of aggregate columns, and it stays.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `Resolved.Query.aggregateOf` | `M/Queries/Select/AggregateSelectResolution.lean` | D | 3 / 4 / 0 |
| `resolveColumns_aggregate` | `M/Queries/Select/AggregateSelectResolution.lean` | R | 1 / 0 / 0 |
| `decidingCall_aggregateColumn` | `M/Queries/Select/AggregateSelectResolution.lean` | R | 1 / 0 / 0 |
| `resolveQueryBody_aggregate` | `M/Queries/Select/AggregateSelectResolution.lean` | R | 1 / 0 / 0 |
| `resolveStatement_select_aggregate` | `M/Schema/Dispatch/AggregateSelectResolution.lean` | R | 0 / 2 / 0 |
| `Resolved.Statement.Calm.aggregateOf_first` | `M/Queries/Select/AggregateSelectResolution.lean` | F | 0 / 2 / 0 |

Test declarations that name these declarations (6):

`BalanceExample.balance_of_bounds`, `SelectSumCases.sumCents_overflow`,
`SelectSumCases.sumCents_resolved`, `SelectSumCases.sumCents_results`,
`SelectSumCases.sumQuery`, `SelectSumCases.sumQuery_calm`.

### Duplicate keys

Form: `SELECT 1 WHERE NOT EXISTS (SELECT e FROM t WHERE w GROUP BY k HAVING count(*) > 1)`.

The packages have the definition and the resolution of this form. The laws
of its evaluation are in the test fixtures: `duplicateKeysOne_run`,
`noDuplicateKeys_claims`, and the laws of `GROUP BY` and `HAVING`
`SelectGroupCases.uniqueRecords_grouped` and
`SelectGroupCases.countCondition_truthy`.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `Resolved.Query.duplicateKeys` | `M/Queries/Evaluation/DuplicateKeyQuery.lean` | D | 2 / 2 / 0 |
| `GroupTermResolvesIn` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | D | 7 / 3 / 0 |
| `GroupTermResolves` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | D | 2 / 2 / 0 |
| `GroupTermResolvesIn.expression` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | R | 0 / 0 / 0 |
| `GroupTermResolves.toIn` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | R | 0 / 2 / 0 |
| `GroupTermResolvesIn.identifier_table` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | R | 1 / 1 / 0 |
| `GroupTermResolves.identifier_table` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | R | 0 / 1 / 0 |
| `resolveOperand_moreThanOne` | `M/Queries/Select/DuplicateKeyGroupTerm.lean` | R | 1 / 0 / 0 |
| `decidingCall_duplicateKeys` | `M/Queries/Select/DuplicateKeyResolution.lean` | R | 1 / 0 / 0 |
| `resolveQueryBody_duplicateKeys` | `M/Queries/Select/DuplicateKeyResolution.lean` | R | 1 / 0 / 0 |
| `resultColumn_one_facts` | `M/Queries/Select/DuplicateKeyResolution.lean` | R | 0 / 2 / 0 |
| `resolveStatement_selectOne_notExists_duplicateKeys` | `M/Schema/Dispatch/DuplicateKeyResolution.lean` | R | 0 / 1 / 0 |

Test declarations that name these declarations (7):

`AssertionExamples.one_live_iff`, `duplicateKeysOne_run`,
`duplicateKeys_calm`, `email_claims`, `group_nocase`,
`noDuplicateKeys_claims`, `uniqueEmail_ok`.

### Claim on the columns of a table

Form: `SELECT 1 FROM pragma_table_info('t') WHERE name = 'c'`.

The law of the claim, `tableInfo_results`, is in the test fixtures, for each
database that has the table. The tactic `sql_holds` has no case for the
source `pragma_table_info`. `tableInfoScope_resolveName_name`,
`resolveOperand_tableInfo_name` and `tableInfoScope_collation_name` are in
the set `sql_simp`. `resolveSources_tableInfo` is the law of this one
source, as `resolveSources_table` is the law of a table source. Its
statement holds for each callback of the sibling queries and each prefix of
a nested query; the anonymous examples below apply it in that generality.

The proof of `resolveStatement_select_one_tableInfo` applies the general law
`resolveStatement_select_simple`, which stays, with the premises from
`resolveSources_tableInfo`, `resolvePendingSources_pragma` and
`resolveColumns_one`.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `tableInfoScope` | `M/Queries/Preparation/TableInfoResolution.lean` | D | 8 / 5 / 2 |
| `tableInfoScope_resolveName_name` | `M/Queries/Preparation/TableInfoLaws.lean` | R | 1 / 0 / 0 |
| `resolveOperand_tableInfo_name` | `M/Queries/Preparation/TableInfoLaws.lean` | R | 0 / 0 / 0 |
| `tableInfoScope_collation_name` | `M/Queries/Preparation/TableInfoLaws.lean` | R | 0 / 0 / 0 |
| `resolveSources_tableInfo` | `M/Queries/Preparation/TableInfoResolution.lean` | R | 1 / 1 / 3 |
| `tableInfoScope_resolveName_type` | `M/Queries/Select/TableInfoColumnLaws.lean` | R | 1 / 1 / 0 |
| `resolveOperand_tableInfo_type` | `M/Queries/Select/TableInfoColumnLaws.lean` | R | 0 / 1 / 0 |
| `tableInfoScope_collation_type` | `M/Queries/Select/TableInfoColumnLaws.lean` | R | 0 / 1 / 0 |
| `resolveStatement_select_one_tableInfo` | `M/Schema/Dispatch/TableInfoResolution.lean` | G | 0 / 1 / 0 |
| `Resolved.Statement.Calm.selectOne_pragma` | `M/Queries/Evaluation/SelectSourceRules.lean` | F | 0 / 1 / 0 |

Test declarations that name these declarations (6):

`BalanceExample.guard_bodies`, `BalanceExample.guard_scopes`,
`BalanceExample.name_resolves`, `BalanceExample.pragmaScope`,
`BalanceExample.typed_resolves`, `tableInfo_results`.

- Other user of `resolveSources_tableInfo`: the `#print axioms` check at
  `T/Queries/Evaluation/SuccessSumBound.lean:80`.
- Other user of `tableInfoScope`, `resolveSources_tableInfo`: the anonymous
  example at `T/Queries/Evaluation/ClaimsDerived.lean:52`.
- Other user of `tableInfoScope`, `resolveSources_tableInfo`: the anonymous
  example at `T/Queries/Evaluation/SuccessSumBound.lean:92`.

### `IN` and `EXISTS` on a second table

Form: `SELECT p FROM t WHERE x [NOT] IN (SELECT c FROM u)`, and the same with `EXISTS`.

These laws compare a query with `IN` and a query with `EXISTS` (decision 3).
The laws of the model give equal values of the two conditions and equal rows
of the two outputs. The two laws of the client library,
`Sql.EquivAt.in_exists_of_rowidAlias` and
`Sql.EquivAt.notIn_notExists_of_rowidAlias`, conclude `Sql.EquivAt`: the two
programs have the same run and the same complete outcomes of each branch,
with the errors, the traces and the state of the connection. The
declarations with status E have no user in the packages outside this family.

`Resolved.Expr.fault_inQuery_of_columns` and
`Resolved.Expr.fault_exists_of_columns` give the fault of the evaluation
from facts about the table and about the run of the subquery. The calm check
of the branch decides a property of the syntax and does not replace them.
They stay until operator laws give their conclusions from their premises.

The inventory of ADR 0033 (`plans/20261124-step-rule-inventory.status.md`,
row "Partial retention") keeps the test witness
`ReplacedSubqueryEquivalence.Sql_EquivAt_in_exists_of_rowidAlias`, which
proves the former statement of `Sql.EquivAt.in_exists_of_rowidAlias` at its
original premises, until a different client checks the positive `IN` with
inner values that can be NULL. The witness stays, or the change proves it
again, until that client exists.

| Declaration | File | Status | Users |
| --- | --- | --- | --- |
| `correlatedScope` | `M/Queries/Select/FromSubqueryStatementResolution.lean` | D | 3 / 0 / 0 |
| `resolveStatement_selectFrom_inQuery` | `M/Schema/Dispatch/InSubqueryStatementResolution.lean` | R | 0 / 0 / 0 |
| `resolveStatement_selectFrom_existsTest` | `M/Schema/Dispatch/CorrelatedExistsResolution.lean` | R | 0 / 0 / 0 |
| `FilterResolves.exists_only` | `M/Schema/Dispatch/CorrelatedExistsResolution.lean` | R | 0 / 0 / 0 |
| `FilterResolves.notExists_only` | `M/Schema/Dispatch/CorrelatedExistsResolution.lean` | R | 0 / 0 / 0 |
| `resolveStatement_selectFrom_subquery` | `M/Schema/Dispatch/FromSubqueryStatementResolution.lean` | R | 2 / 0 / 0 |
| `resolveSelect_from_one_subquery` | `M/Queries/Select/FromSubquerySelectResolution.lean` | R | 1 / 0 / 0 |
| `Resolved.CorrelatedEquality` | `M/Queries/Evaluation/InSubqueryFilterLaw.lean` | E | 4 / 0 / 0 |
| `Resolved.any_kept_equals_iff` | `M/Queries/Evaluation/InSubqueryFilterLaw.lean` | E | 2 / 0 / 0 |
| `Resolved.correlatedEquality_of_compare` | `M/Queries/Evaluation/InSubqueryEqualityLink.lean` | E | 2 / 0 / 0 |
| `Resolved.Query.equalsColumn_calm` | `M/Queries/Evaluation/InSubqueryQueryLaw.lean` | E | 2 / 0 / 0 |
| `Resolved.Query.inColumn_calm` | `M/Queries/Evaluation/InSubqueryQueryLaw.lean` | E | 2 / 0 / 0 |
| `Resolved.Expr.fault_inQuery_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | E | 2 / 0 / 0 |
| `Resolved.Expr.fault_exists_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | E | 2 / 0 / 0 |
| `Resolved.Expr.evaluate_notIn_eq_notExists` | `M/Schema/Dispatch/InSubqueryFilterLaw.lean` | E | 1 / 0 / 0 |
| `Resolved.Expr.evaluate_in_truthy_eq_exists` | `M/Schema/Dispatch/InSubqueryFilterLaw.lean` | E | 1 / 0 / 0 |
| `Resolved.Expr.evaluate_notIn_eq_notExists_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | E | 1 / 0 / 0 |
| `Resolved.Expr.evaluate_in_truthy_eq_exists_of_columns` | `M/Schema/Dispatch/InSubqueryColumnLaw.lean` | E | 1 / 0 / 0 |
| `resolvedStepOutput_in_eq_exists` | `M/Programs/StatementRunLaws/InSubqueryQueryInLaw.lean` | E | 1 / 0 / 0 |
| `resolvedStepOutput_notIn_eq_notExists` | `M/Programs/StatementRunLaws/InSubqueryQueryLaw.lean` | E | 1 / 0 / 0 |
| `resolvedStepOutput_in_eq_exists_of_rowidAlias` | `M/Programs/StatementRunLaws/InSubqueryQueryRowidAlias.lean` | E | 1 / 0 / 0 |
| `resolvedStepOutput_notIn_eq_notExists_of_rowidAlias` | `M/Programs/StatementRunLaws/InSubqueryQueryRowidAlias.lean` | E | 1 / 0 / 0 |
| `Sql.EquivAt.in_exists_of_rowidAlias` | `S/Programs/StatementRunLaws/NotInQuery.lean` | E | 0 / 1 / 1 |
| `Sql.EquivAt.notIn_notExists_of_rowidAlias` | `S/Programs/StatementRunLaws/NotInQuery.lean` | E | 0 / 1 / 0 |

Test declarations that name these declarations (2):

`ReplacedSubqueryEquivalence.Sql_EquivAt_in_exists_of_rowidAlias`,
`S6NotBlocked.notBlocked_equivalent`.

- Other user of `Sql.EquivAt.in_exists_of_rowidAlias`: the Python test
  `tests/surface_select_automation_test.py`: its test
  `test_positive_in_equivalence_allows_nullable_inner_values` builds the
  witness that proves the former statement of the law.

### Laws that the readers put in the class and that are not in group 2

The unit of the tactic, `SELECT 1 WHERE c`. The tactic names the definition
`Resolved.Query.selectOneWhere`, and the new output law
`resolvedStepOutput_selectOneWhere_hasRows` uses the second law.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Query.selectOneWhere_expressions` | `M/Queries/Evaluation/PlainQueryRules.lean` | 5 / 1 / 0 |
| `Resolved.Query.selectOneWhere_faultless` | `M/Queries/Evaluation/PlainQueryRules.lean` | 1 / 2 / 0 |

`IN`, `EXISTS` and `NOT EXISTS` on a subquery on one table. They state the
evaluation of the operator on a subquery on one table
(`Resolved.Query.oneTable`), for each probe, condition and list of result
expressions. Their users are laws with status E. The branch adds laws of
`EXISTS` for each run of a subquery (`Resolved.Expr.truthy_exists`,
`Resolved.Expr.truthy_notExists`); the pilot did not examine whether one set
of laws can serve both.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.Expr.evaluate_inQuery_oneTable` | `M/Schema/Dispatch/InSubqueryEvaluate.lean` | 3 / 0 / 0 |
| `Resolved.Expr.evaluate_exists_oneTable` | `M/Schema/Dispatch/InSubqueryEvaluate.lean` | 2 / 0 / 0 |
| `Resolved.Expr.evaluate_notExists_oneTable` | `M/Schema/Dispatch/InSubqueryEvaluate.lean` | 2 / 0 / 0 |

`PRAGMA foreign_key_check`. One pragma, not a form of claim. The check of a
schema-only script (`runScriptStep_succeedsBySchema`) uses these laws.

| Declaration | File | Users |
| --- | --- | --- |
| `resolvedStepOutput_keyCheck_rows` | `M/Programs/StatementRunLaws/ForeignKeyCheckContinues.lean` | 1 / 0 / 0 |
| `resolvedStepOutput_keyCheck_hasNoRows` | `M/Programs/StatementRunLaws/ForeignKeyPragmaQuery.lean` | 1 / 0 / 0 |
| `resolvedStepOutput_keyCheck_clock` | `M/Programs/StatementRunLaws/ForeignKeyPragmaQuery.lean` | 1 / 0 / 0 |
| `resolvedStepOutput_keyCheck_empty` | `M/Tooling/Counterexamples/ForeignKeyPragmaQuery.lean` | 0 / 1 / 0 |
| `keyCheckQuery_calm` | `M/Schema/Rows/ForeignKeyPragmaQuery.lean` | 4 / 0 / 0 |
| `keyCheckQuery_source` | `M/Schema/Rows/ForeignKeyPragmaQuery.lean` | 2 / 0 / 0 |
| `resolvePragma_keyCheck_iff` | `M/Schema/Rows/ForeignKeyPrepareLaws.lean` | 0 / 1 / 1 |
| `resolvePragma_tableKeyCheck_iff` | `M/Schema/Rows/ForeignKeyPrepareLaws.lean` | 0 / 0 / 0 |

The condition `c = ?n`. `equalsParameter` is the resolved comparison of a
column with a parameter, and `equalsParameter_true` states when it is true.
They are about one operator with two fixed operands, and no query form is in
their statements: `AssertionExamples.customer_named_after_insert` uses the
law for a query with no aggregate, and
`AssertionExamples.inserted_customer_is_unique` and
`AssertionExamples.inserted_customer_has_the_name` use it for the row of an
insert. The recommendation does not change them.

| Declaration | File | Users |
| --- | --- | --- |
| `equalsParameter` | `M/Queries/Evaluation/PlainInsertRows.lean` | 1 / 5 / 0 |
| `equalsParameter_true` | `M/Queries/Evaluation/PlainInsertRows.lean` | 0 / 3 / 0 |

Laws of one operator that are in the file of a form. Each is a law of one
operator: the filter with no condition, and the groups of a column against a
unique key.

| Declaration | File | Users |
| --- | --- | --- |
| `Resolved.keptRows_none` | `M/Queries/Evaluation/DuplicateKeyQuery.lean` | 0 / 5 / 0 |
| `LiteralData.uniqueRows_of_column_groups` | `M/Schema/Rows/GroupKeyConflictLaws.lean` | 0 / 2 / 0 |

Laws of `SUM` with a premise in the form of one condition. They are laws of
the value functions. The premise is the condition `NOT BETWEEN` as a value.

| Declaration | File | Users |
| --- | --- | --- |
| `Value.numeric_of_not_between` | `M/Queries/Evaluation/SumRangeLaws.lean` | 1 / 0 / 0 |
| `sumOf_no_overflow_of_between` | `M/Queries/Evaluation/SumRangeLaws.lean` | 0 / 2 / 0 |

### Test laws of one query form

The readers put 49 theorems of `tests/surface` in the class. 18 of them name
a declaration of group 2, and are in the lists of the families above:

`BalanceExample.count_run`, `BalanceExample.one_body`,
`ConcatFixture.resolve_pipes_lookup`,
`LowercaseFixture.resolve_original_lookup`,
`LowercaseFixture.resolve_stored_lookup`,
`ReplacedSubqueryEquivalence.Sql_EquivAt_in_exists_of_rowidAlias`,
`S6RulesQuerySites.resolve_column_lookup`, `SelectSumCases.sumQuery_calm`,
`columnOne_run`, `countOne_run`, `duplicateKeysOne_run`,
`duplicateKeys_calm`, `noDuplicateKeys_claims`, `tableInfo_results`,
`tableOne_run`, `unique_lookup_holds`, `whereColumn_claims`,
`whereCount_claims`.

The other 31 name no declaration of group 2. The recommendation does not
change them:

- General laws: the statement does not fix the table, or it takes the
  resolution as a premise. `whereOne_claims` gives `Holds`, `Empty` and
  `Fails` for a claim `SELECT 1 WHERE c` with one subquery.
  `SelectAutomation.collection_count`, `SelectAutomation.where_fact` and
  `SelectAutomation.where_nonnull` are laws over each list of source rows;
  the test `test_select_collection_rules` of
  `tests/surface_select_automation_test.py` requires that the proofs of
  their module have only logical axioms. `SelectGroupCases.result_ungrouped`
  is the law of an aggregate query with no `GROUP BY`, which
  `SelectExtremumCases.joined_customers` uses for a join.

  `whereOne_claims`, `BalanceExample.one_run`,
  `SelectAutomation.collection_count`, `SelectAutomation.where_fact`,
  `SelectAutomation.where_nonnull`, `SelectAutomation.schema_projection`,
  `SelectGroupCases.result_ungrouped`,
  `SelectGroupCases.uniqueRecords_grouped`,
  `SelectGroupCases.countCondition_truthy`.

- Client claims and facts of fixture definitions that name only test laws
  and general package laws.

  `SelectGroupCases.keyCounts_of_mem`, `SelectGroupCases.countQuery_fails`,
  `SelectHavingCases.keptCounts_of_mem`, `keyGroupsShort_iff_pairwise`,
  `table_has_a_stored_column_named`.

- Facts about the filters of the fixtures of the migration for a derived
  column.

  `LowercaseFixture.resolve_original_filter_at`,
  `LowercaseFixture.resolve_stored_filter_at`,
  `LowercaseFixture.originalFilter_calm`,
  `LowercaseFixture.storedFilter_calm`,
  `LowercaseFixture.simpleColumn_calm`,
  `LowercaseFixture.storedFilter_append`,
  `LowercaseFixture.originalFilter_append`,
  `LowercaseFixture.results_translate`, `LowercaseFixture.results_preserve`,
  `ConcatFixture.storedFilter_append_pipes`,
  `ConcatFixture.pipesFilter_append`,
  `ConcatFixture.resolve_pipes_filter_at`, `ConcatFixture.pipesFilter_calm`.

- Laws of a form with no package law of the same form: a function call with
  no `FROM`, a term of a compound query, and a derived table. The tactic
  `sql_holds` has no case for these forms.

  `SelectFunctionFaultCases.absQuery_quiet`,
  `SelectFunctionFaultCases.abs_context`,
  `SelectCompoundCases.columnTerm_run`,
  `SelectDerivedCases.derived_returns`.

## Group 3: laws of writes

### Point 4: the rows that a write leaves, with the bound values

Point 4 adds one fact for each kind of write. No pilot branch has this fact
in a general form, so the point changes no law of today. On the branch,
`LiteralData.mem_deleted` states the membership in the rows that a delete
keeps, for an arbitrary evaluation context. Form A of the pilot has the law
`LiteralData.mem_deleted_rows` with the same arbitrary context. Form A
rewrites the context of the statement to the bound values only in one test
theorem (`purge_reached_rows`), by computation for one filter. The general
rewrite is outstanding. `Resolved.Expr.evaluate_rowAndParameters` exchanges
the evaluation context of an expression under two premises: no part of the
expression reads more than its row and the parameters
(`Resolved.Expr.readsBeyondRowAndParameters`), and the two contexts have
equal parameters. An expression with arithmetic, casts and calls of scalar
functions can meet the first premise. `Resolved.Expr.Rowwise` is one
sufficient way to show the first premise
(`Resolved.Expr.Rowwise.localReads`); `Resolved.Expr.Rowwise.evaluate_congr`
is the exchange for such an expression.

Two laws of today state the rows of an `INSERT` for exactly two and exactly
three parameters: each parameter is stored under the affinity of its column.
They state the conversion of the input cells before the insert, so a fact
about the rows that a write leaves does not replace them. They can go after
a general law of `Resolved.rowsAt`, for a list of parameter cells of each
length, exists and a retention test derives the two equations from it.
`Resolved.rowsAt_values` is the law for cells that are known values. The law
for parameter cells does not exist today or on a pilot branch:

| Declaration | File | Users |
| --- | --- | --- |
| `rowsAt_two_parameters` | `M/Schema/Writes/PlainInsertRows.lean` | 0 / 2 / 0 |
| `rowsAt_three_parameters` | `M/Schema/Writes/PlainInsertRows.lean` | 0 / 1 / 0 |

Test declarations that name them (3):

`AssertionExamples.customer_named_after_insert`,
`AssertionExamples.inserted_rows`, `ItemInsertSite.items_values`.

The readers found 67 package laws of one kind of write that name the context
of the statement (the two laws above are among them), and 20 that are stated
with values. The 35 kind rules of ADR 0033, for example
`runScriptStep_plainDelete_eq`, keep their statements.

### Point 5: the analysis of a write as a step of `sql_run`

Point 5 changes the tactic `sql_run`. No pilot branch has this step; form D
of the pilot has the analysis as a separate definition
(`PlainDelete.analyze`). The point deletes no package law: the step applies
the laws that a client applies by hand today, which are the kind rule of the
statement and the 46 premise laws, for example `runScriptStep_continues`,
`RunStep.continues_of_rule`, `insertReady_of_fits`, `InsertFits.of_valid`,
`Sql.sendReached_single` and `ExecutionContext.initial_holds_valid`.

In the test fixtures, five structures carry the facts of one write for a
schema. For example, `AssertionExamples.PurgeFrameSite` has the lookup of
the table and the resolution of the statement and of the claim. The step can
compute such facts only for a claim that has the full catalog as premise
(decision 1). The pilot removed none of the structures; on the branch,
`AssertionExamples.PurgeFrameSite` loses one field. They are candidates, not
results:

| Declaration | File | Users |
| --- | --- | --- |
| `AssertionExamples.PurgeFrameSite` | `T/Schema/Tests/PurgeFrameSite.lean` | 0 / 8 / 0 |
| `AssertionExamples.CustomerInsertSite` | `T/Schema/Tests/CustomerInsertSite.lean` | 0 / 7 / 0 |
| `AssertionExamples.AddCustomerSite` | `T/Programs/Tests/AddCustomerQueries.lean` | 0 / 6 / 0 |
| `AssertionExamples.AccountSignupSite` | `T/Schema/Tests/SignupInvariantClaims.lean` | 0 / 5 / 0 |
| `AssertionExamples.GlobalSignupSite` | `T/Schema/Tests/GlobalSignupInvariant.lean` | 0 / 3 / 0 |

The fixture of the table `items` has no structure. Its 15 helper laws for
the one schema (`ItemInsertSite.items_*`) have the same position: 12 in
`T/Schema/Tests/ItemInsertSite.lean` and 3 in
`T/Schema/Tests/ItemInsertOutcomes.lean`.

## Laws that the recommendation does not affect

- 32 of the 36 laws of one simple `SELECT` on one table, for example
  `resolvedStepOutput_oneTable_rows`, `Resolved.Query.oneTable_subqueryRun`
  and `resolveStatement_select_table`. A simple query is the unit of the
  operator laws. Of the other four, the branch deletes
  `Resolved.currentTerm_mem_results` and `Resolved.initialTerm_mem_results`,
  and moves the two theorems of group 1.
- The 17 checkers of today and their soundness laws, for example
  `Script.succeeds_of_schema`, `KeptRead.preserves_of_check` and
  `DerivedColumnMigration.preserves_of_check`. Point 6 of the recommendation
  is about new checkers for patterns of claim.
- The 36 laws of a script pattern, such as the migration for a derived
  column.
- The 177 laws of one kind of write, with the two exceptions of group 3, and
  the 46 premise laws of the write rules.
- The 2,345 package theorems that are in none of these classes: the laws of
  values, expressions, rows, the catalog, DDL, triggers, foreign keys and
  the tools.
