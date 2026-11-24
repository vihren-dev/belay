# Pilot: forms of proof for a claim that is stated in SQL

Created 2026-11-24.
Status: OPEN.
Status: [20261124-claim-proof-pilot.status.md](20261124-claim-proof-pilot.status.md).
Owner request of 2026-11-24: "Run a pilot with the different reasonable
approaches used by professionals in such situations. Then compare and
give me a recommendation."

The purge frame claim of the guide says that a purge of the expired
sessions of one customer keeps each other session. The claim is a SQL
query that reads the database at the start of the run through the schema
`before`. Its proof for every database is `purge_frame` with
`purge_keeps_rows` in `tests/surface/Programs/Scripts/PurgeFrameClaims.lean`.
The proof costs more than its content:

- The four purge fixtures have 216 code lines.
- The proof calls four laws from nine modules of the model package with
  429 code lines. These modules state the output of one form of query,
  `SELECT 1 WHERE NOT EXISTS (SELECT … FROM before.t WHERE p EXCEPT
  SELECT … FROM t)`. The purge fixtures are the only callers of these
  laws.
- `purge_keeps_rows` has 27 proof lines. Eight of them unfold the claim
  to its resolved form, and five apply the law of the query form with
  its explicit arguments.
- The claim holds for a database that has a `PurgeFrameSite`. The site
  assumes how the purge and the claim resolve, and it assumes that the
  model runs the purge for each clock and each set of counters
  (`purgeModeled`).

The pilot proves two claims about the purge in a base form and in four
other forms, and it measures each form. The four forms are the usual
answers of verification practice to a claim language that is expensive
to evaluate in a proof: a claim in the logic, composable laws for each
operator, a tactic that applies the laws, and a checker with a proof of
soundness. The findings record compares the forms and gives a
recommendation. The owner selects the form.

## Acceptance

### The two claims

Both claims are about the purge of the fixtures,
`DELETE FROM sessions WHERE customer_id = :c AND expires_at < :now`.
The pilot schema is the catalog of the database `sessions` of
`tests/surface/Schema/Tests/PurgeFrameInstances.lean`: one table with the
columns `id INTEGER PRIMARY KEY`, `customer_id` and `expires_at`.

- The frame claim is `purgeKeeps` of
  `tests/surface/Queries/Evaluation/PurgeFrameQueries.lean`, with the
  start of the run as its initial database: `SELECT 1 WHERE NOT EXISTS
  (SELECT * FROM before.sessions WHERE (customer_id = $c AND expires_at
  < $now) IS NOT 1 EXCEPT SELECT * FROM sessions)`.
- The effect claim is new: `SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM
  sessions WHERE customer_id = $c AND expires_at < $now)`. It says that
  no row for which the filter of the purge is true is left.

In each form, a client statement of each claim meets these conditions:

- It holds for each pair of values, also NULL and text, for each database
  that has the catalog of the pilot schema (`Database.HasCatalog`), and
  for each complete environment.
- It requires the claim after each run of the purge that has no error
  (`ifOk`).
- It has no other premise. It does not assume a resolution, and it does
  not assume that the model runs the purge.

The existing instances stay as tests of the model, with the claims as the
actual observations decide them on a database: the NULL customer, the
NULL time, the text time, the purge with `OR`, the claim with `NOT` and
the trigger that aborts the purge. The theorems that state that a site
holds for given values are replaced: the client statement applies to the
database `sessions`.

### Base form

The base form keeps the present way of proof: one law for one form of
query. All other forms start from the revision of the base form.

- The model package has a law for the case in which a plain DELETE
  continues. The law is general: it holds for each plain DELETE whose
  filter reads only its row and the parameters, on each connection in
  which the target holds a table. It follows from the kind rule
  `runScriptStep_plainDelete_eq`. The status file records the general
  form that the law has and the cases that it leaves out.
- `PurgeFrameSite` has no field `purgeModeled`. A theorem states the
  frame claim for each database with a site, as `purge_frame` does today,
  with the weaker site. This theorem holds for each schema in which a
  site exists.
- A theorem gives a site for each database that has the catalog of the
  pilot schema, and the client statement of the frame claim follows.
- The client statement of the effect claim is proved with the laws that
  exist today for a query of the form `SELECT 1 WHERE NOT EXISTS (SELECT
  1 FROM t WHERE f)`. Laws that are in a test support file and that the
  proof needs can move to a package when their statements are general.

### Form A: claims in the logic

The claims are Lean propositions about rows, and no SQL query states
them.

- The frame claim says: each row of the table `sessions` of the start
  for which the filter of the purge is not true is a row of the table of
  the reached database. The effect claim says: the filter is true for no
  row of the table of the reached database.
- A reader can see the condition on a row in the statement. The
  statement can use the resolved filter of the purge or a Lean
  predicate on the cells. The findings record shows the statements.
- The proofs use the kind rule of the plain DELETE and data facts. The
  model package gets a data fact for the rows that a DELETE keeps: a row
  is in the table of `LiteralData.deleted` exactly when it is in the
  table before and the filter does not select it. The fact mentions no
  step, no resolution and no connection.
- This form changes no existing law and no existing fixture. It adds a
  fixture and the data facts.

### Form B: composable laws

The claims stay SQL queries. Each operator of the two queries has its own
law, and a proof of a claim composes the laws.

- A law connects a two-state assertion to the output of the resolved
  query. For a script of one SELECT, an initial database and a context:
  when `resolveTwoState` gives a resolved statement,
  `Holds.inContextSince` holds exactly when the output of the resolved
  statement, observed with the initial database, has rows.
- The model or the surface package has laws for these parts, and each
  law is about one part. No statement of a law fixes a combination of two
  of them:
  - the output of a statement `SELECT 1 WHERE e` for a condition `e` and
    each list of subqueries;
  - the value of `EXISTS` and `NOT EXISTS` over a subquery of the
    statement, as the rows of the run of that subquery;
  - the run of a subquery of the statement that is a compound of two
    terms with `EXCEPT`, as the rows of its terms;
  - the rows of a read of one table with a filter and a list of columns,
    from the table of the current database and from the table of the
    initial database;
  - the rows that a DELETE keeps (the data fact of form A).
- A law is an equation or an equivalence where the model permits it. A
  law that gives only a sufficient condition names the reason in the
  status file.
- Both client statements are proved with these laws. The proof of the
  effect claim uses the same laws for `SELECT 1 WHERE`, `NOT EXISTS` and
  the read of one table as the proof of the frame claim. It uses no law
  that fixes the form `SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM t WHERE
  f)`.
- The declarations that fix the form `NOT EXISTS (… EXCEPT …)` are
  deleted: `Resolved.notExistsExcept`, `Resolved.initialTerm`,
  `Resolved.currentTerm`, `Resolved.notExistsExceptSubqueries` and the
  theorems about them. A module of the nine that then has no declaration
  is deleted. `Resolved.Expr.Rowwise` and its laws stay, because
  `tests/surface/Queries/Evaluation/ClaimsExpressionCongruence.lean`
  uses them.
- No capability is lost. A fixture proves, from the laws that remain,
  the statements of the four deleted or changed laws that the purge
  fixtures call today: `resolvedStepOutput_notExistsExcept_hasRows`,
  `Resolved.notExistsExcept_subset`, `Resolved.notExistsExcept_identical`
  and `Resolved.Expr.truthy_isNot_one_and`. The statements are copied
  from the revision of the base form. A definition that a statement
  needs and that the form deletes is restated in the fixture. The
  theorem of the base form for each database with a site stays proved.

### Form C: a tactic over the laws

Form C starts from the revision of form B.

- The surface package has a tactic for the goal that `sql_run` leaves for
  a post with `holds q` or `holdsSince start q`: the assertion at the
  reached context.
- With the catalog premise as a hint, the tactic resolves the query,
  applies the laws of form B and leaves goals about rows. A goal that it
  leaves names rows of tables, values of expressions on a row
  (`Resolved.Expr.eval`, `Resolved.truthy`) and data functions of the
  write, such as `LiteralData.deleted`. It names no function that runs a
  query.
- The tactic applies theorems and evaluates closed terms. When it cannot
  go on, its message says which part of the query has no law.
- Both client statements are proved with `sql_run` and the tactic. The
  proofs of form B stay in their fixture, so that the two forms can be
  compared at one revision.

### Form D: a checker with a proof of soundness

Form D starts from the revision of the base form and keeps the laws of
the base form.

- The surface package has a check for each of the two patterns of claim:
  a function to `Bool` from a schema, the script of a DELETE and the
  script of a claim. The frame check accepts a claim that compares the
  table of the DELETE in `before` with the same table after it, with the
  condition "the filter of the DELETE `IS NOT 1`". The effect check
  accepts a claim that says that no row of the table satisfies the
  filter of the DELETE.
- A theorem of soundness for each check: when the check gives `true` for
  a schema, a DELETE and a claim, the client statement holds for the
  DELETE and the claim with each list of values, for each database with
  the catalog of the schema. The theorem follows the pattern of
  `KeptRead.preserves_of_check`.
- Both client statements are proved with the theorems of soundness and
  an evaluation of the check.
- The fixture shows the limits of the checks: the frame check gives
  `false` for the purge with `OR` and the frame claim of the purge with
  `AND`, and it gives `false` for a claim outside its pattern, such as
  the claim with `NOT`. The docstring of each check says which claims it
  accepts.

### Branches

The base form is on the branch `claim-proof-pilot`, on top of the last
pull request of ADR 0033. Forms A, B and D each have a branch on top of
the base form. Form C has a branch on top of form B. A branch holds no
code of a form that it does not need. The findings record is on the
branch of the base form.

### Model behavior

The results that the executable model computes do not change:
`just verdict` gives the same verdict as before the pilot on each
branch.

### Findings record

`docs/records/claim-proof-pilot-findings.md` records, for the team and
for the owner decision:

- The statement of each claim in each form, as the reader sees it.
- For each form and each claim: the code lines of the client fixture,
  split into the statement, the proof and the helper declarations.
- For each form: the code lines added to and deleted from each package
  (`scc`, as `docs/development/lean-simplification-goal.md` counts them),
  split into lines that serve each claim of that kind and lines that
  serve only these two claims.
- For each form: what a reader must trust to accept the claim, and which
  premises a client must prove.
- For each form: the claims that it cannot state or prove, and what it
  costs to add a claim that is outside its present reach. The record
  uses the effect claim as the measured case and gives an estimate for
  the frame claim of a plain UPDATE.
- The elaboration time of each client fixture and of each new or changed
  library module.
- What a user sees when a claim is false or outside the reach of the
  form.
- Which forms can be combined, and which form makes another one
  unnecessary.
- The recommendation, with its reasons.

The pilot ends with the findings record and the recommendation. After the
owner decision, this task file records the decision, and the branch of
the selected form becomes the pull request.

## Tests

- The Lean build with `--wfail` of the model, the SQL text package and
  the surface, on each branch.
- `tests/surface_assertion_examples_test.py` compiles the purge fixtures
  of each branch. Each new fixture module is a root of the suite
  `surface` in `tests/surface_fixture_roots.json` or is imported by one,
  and a test function with a timeout compiles it and checks its axiom
  reports. The timeout of a module is at most 300 seconds, which is the
  present timeout of the purge fixtures.
- Each client statement and each retention statement has a
  `#print axioms` report that the test checks.
- On each branch, at the end of its form: `just test-full` and
  `just verdict`.
- On the branch of the selected form, before its pull request:
  `just test-nix` and `just test-scheduled-checks`, once.

## Points to know

**Coverage is assumed today.** No law says that a plain DELETE
continues. `PurgeFrameSite.purgeModeled` assumes it, and
`PurgeFrameInstances.sessionsSite` takes it as an argument that each
instance proves by evaluation. `big_after_delete` in
`tests/surface/Queries/Tests/SelectContextCases.lean` assumes it too. No
theorem is about `deleteJsonReady` or `Resolved.anyMayFail`. The kind
rule gives the conditions: `statementClock`, `Counters.firstUnknown`,
the table at the target, `Resolved.subqueriesPlain` and
`deleteJsonReady`. `Resolved.Expr.Rowwise.fault_none` and
`Resolved.Expr.Rowwise.calm` are in
`Queries/Evaluation/RowwiseExpr.lean` of the model package.

**Two contexts for one filter.** The DELETE evaluates its filter in the
context of the statement (`Resolved.statementContext`). The claim
evaluates its condition in the context of its own query. The present
proof connects them with `Resolved.Expr.Rowwise.evaluate_congr`.

**Two-state assertions.** `Holds.reachedSince` is
`Holds.inContextSince` at the default observation of the context.
`Script.observeTwoStateIn` and `Model.observeTwoState` resolve the query
with `resolveTwoState` and give `resolvedStepOutput` with the initial
database. No law connects the assertion to `resolvedStepOutput` for a
known resolution; `purge_keeps_rows` unfolds the definitions.
`resolvedStepOutput_query_hasRows_of_clean_from`
(`Tooling/Counterexamples/TwoStateQuerySteps.lean` of the model
package) is general and gives a sufficient condition only.

**Laws that exist for the parts.** `mem_filtered`,
`Resolved.Query.run_of_faultless`,
`Resolved.Query.results_eq_nil_iff_plain`,
`Resolved.Query.results_plain_unordered`,
`Resolved.Query.subqueryRun_of_faultless`, `mem_except_combine`,
`CompoundOperator.except_combine_eq_nil`, `mem_sourceRows_iff`,
`Resolved.Expr.eval_exists` and the other laws of `ExprEvalLaws.lean`,
`Database.table_setRows`. `Resolved.Query.PlainExcept` states a compound
of two terms with `EXCEPT`; its laws `results`, `ending` and
`subqueryRun` are in the nine modules.

**The effect claim today.** `resolveStatement_selectOne_notExists`
(`Schema/Dispatch/ExistsStatementResolution.lean` of the model package)
resolves the form over each catalog. `tableOne_run` and `whereOne_claims`
are in the test support file
`tests/surface/Queries/Evaluation/SelectOneWhereSupport.lean`.
`no_invoice_is_negative` in `tests/surface/Queries/Tests/ClaimsExists.lean`
and `x_is_an_invoice_id` in `tests/surface/Queries/Tests/ClaimsIn.lean`
use them.

**The catalog premise.** `Database.HasCatalog db schema` is
`db.raw.catalog = schema.raw.catalog`. `shop_found` and `shop_state` in
`tests/surface/Queries/Tests/SelectJoinSupport.lean` show the pattern:
rewrite the catalog and decide the fact on the schema.
`Database.resolveState_of_catalog`, `Database.table_of_catalog` and
`Database.tableNamed_of_hasCatalog` are the library laws. The decisions
on a schema can be expensive: `PurgeFrameInstances.lean` sets
`maxRecDepth 200000`. The notations `ensures` and `ensuresFrom` have no
form with a schema; a client statement uses `FreshEnsures` and
`FreshEnsuresFrom` directly.

**The rowid alias.** `Resolved.notExistsExcept_identical` needs the
rowid alias in the first column: `EXCEPT` compares rows with the
collations, and the rowid shows that two equal rows are one row. The
pilot schema meets the premise.

**`sql_run`.** The tactic reduces the send with the kind rules and
leaves the post at the reached context as a goal with the tag `success`.
It has no rule for `holds` or `holdsSince`. `Sql.check_send_of_rule`
(`Programs/Scripts/KindRuleSend.lean` of the surface package) has the
premise `modeled : result.continues = true`.

**The checker pattern.** `KeptRead.preservesCheck`,
`KeptRead.preserves_of_check` and `KeptRead.preserves`
(`Programs/Claims/KeptReadCheck.lean` and `KeptRead.lean` of the surface
package) with `ReadAnalysis.analyze` and `ReadAnalysis.analyze_sound`.
`tests/surface/Programs/Scripts/KeptReadChecks.lean` is a client.

**Imports of the nine modules.** `Model.lean` imports
`Schema/Columns/TwoStateKeptRows` and
`Tooling/Counterexamples/TwoStateNotExistsExceptOutput`. The two modules
`CorrelatedSubquerySource` import the two modules `ExceptSubqueryRun`.

**Package limits.** The core modules of the model package import `Init`
and `Lean.Meta.Tactic.Simp.RegisterCommand`, and no other module of
`Lean` or `Std` (ADR 0006). A tactic belongs to the surface package.
Guide examples stay in `tests/surface`: a law in a package names no
table, column or value of the purge.

## Not in this task

The use of the selected form for other claims and other statement kinds,
a notation for a client statement with a schema, claims about a DELETE
with RETURNING, triggers or foreign-key actions, and a change of the
two-state assertions themselves.
