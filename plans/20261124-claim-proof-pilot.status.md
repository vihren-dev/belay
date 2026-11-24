# Status: pilot of the forms of proof for a claim in SQL

Created 2026-11-24.
Status: OPEN. The pilot is complete. The owner selected the branch
`claim-proof-pilot-tactic` on 2026-11-25; the pull request and its checks
are pending.
Task: [20261124-claim-proof-pilot.task.md](20261124-claim-proof-pilot.task.md).

## References

- Owner request of 2026-11-24 (quoted in the task file).
- ADR 0033, `docs/adr/adr-0033-exact-step-rules.md`: the kind rules that the
  pilot uses.
- `docs/development/lean-simplification-goal.md`: how code lines and
  capabilities are counted.
- Fixtures: `tests/surface/Queries/Evaluation/PurgeFrameQueries.lean`,
  `tests/surface/Schema/Tests/PurgeFrameSite.lean`,
  `tests/surface/Programs/Scripts/PurgeFrameClaims.lean`,
  `tests/surface/Schema/Tests/PurgeFrameInstances.lean`.
- Test: `tests/surface_assertion_examples_test.py`,
  `test_purge_frame_claim_over_every_database`.
- Kind rule: `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/PlainDeleteRule.lean`.
- Findings record: `docs/records/claim-proof-pilot-findings.md`.
- Two-state assertions:
  `packages/belay/Belay/Sqlite/Programs/Claims/TwoStateAssertions.lean`.

## Branches

| Form | Branch | Starts from |
| --- | --- | --- |
| Base | `claim-proof-pilot` | `adr-0033-phase-8-inventory` |
| A, claims in the logic | `claim-proof-pilot-logic` | base |
| B, composable laws | `claim-proof-pilot-laws` | base |
| C, tactic | `claim-proof-pilot-tactic` | B |
| D, checker | `claim-proof-pilot-checker` | base |

## Progress log

- 2026-11-24: task file and status file written. The task file's
  statements about the present code were checked against the revision
  `adr-0033-phase-8-inventory`.
- 2026-11-24, base form: the readiness facts of a row-wise filter
  (`anyMayFail`, `deleteJsonReady`).
- 2026-11-24, base form: review fixes of the readiness facts (the
  docstring of `anyMayFail_eq_false_iff`, the reach of the UPDATE checks).
- 2026-11-24, base form: the weaker site, `purge_continues` and the frame
  client statement over the catalog of `sessions`.
- 2026-11-24, base form: review fixes of the frame commit (docstrings in
  short sentences, the fields of `sessionsSite`).
- 2026-11-24, base form: the effect claim `purgeClears` and its client
  statement `purge_clears`.
- 2026-11-24, base form: review fixes of the effect commit (declaration
  names in module docstrings as plain code, the proof sketch of
  `purgeClears_iff`, the docstrings of the instances and of the test).
- 2026-11-24, base form: `PurgeEffectClaims.lean` and
  `PurgeFrameSchema.lean` name their declarations with checked references,
  in a second module docstring at the end of the file. Lean refuses a Verso
  module docstring after a Markdown one, so `set_option doc.verso true` now
  comes before the first module docstring.
- 2026-11-24, base form: `PurgeFrameSite.lean` gets the same layout, with a
  checked reference to `PurgeFrameSite.purge_continues` at the end.
- 2026-11-24, base form: the first module docstring of `PurgeFrameSite.lean`
  no longer names the structure; the last one names it with a checked
  reference.
- 2026-11-24, base form: `JsonReadyLaws` is listed in the core library of
  the model package (folded into the readiness commit). Final checks run;
  the base form is DONE.
- 2026-11-24, form B: the bridge laws from the one-state and two-state
  assertions to the output of the resolved statement
  (`ResolvedOutputBridge.lean`).
- 2026-11-24, form B: review fixes of the bridge laws (the plain words of
  `Output.hasRows`, `usesSchema` and `Script.isQuery`, checked names in the
  module docstring).
- 2026-11-24, form B: second review fixes of the bridge laws (the module
  docstring names the resolution of each law; the two-state law says which
  argument of `resolvedStepOutput` is the initial database).
- 2026-11-24, form B: the laws of the parts of a query claim (SELECT 1
  WHERE, EXISTS and NOT EXISTS, a subquery of the statement, the read of
  one table, the rows that a DELETE keeps, the logical values) and the new
  proof of the effect claim with them.
- 2026-11-24, form B: review fixes of the laws of the parts (the wrapper
  `resolvedStepOutput_query_hasRows_of_clean_from` is deleted, each form of
  `Resolved.Expr.isLogical` is listed, docstrings and status text).
- 2026-11-24, form B: the module text of `RowidOutputIdentity` names its
  three table premises (distinct rowids, each row stores its rowid in the
  alias, the alias is the column 0) and says that the law fixes the values
  of the kept rows of EXCEPT for fixed term rows, not their order.
- 2026-11-24, form B: the proof of the frame claim composes the laws of the
  parts.
- 2026-11-24, form B: the laws of the form `NOT EXISTS (… EXCEPT …)` and the
  truth law of `(a AND b) IS NOT 1` are deleted; retention fixtures prove
  their base statements from the laws of the parts.
- 2026-11-24, form B: review fixes of the deletion commit (the plain words
  of `Resolved.Query.simple_results_congr` and of the retention statements,
  the record of the replaced truth laws, the note on `nix-build`), and a
  shorter frame proof with `purgeKeepsSubqueries`.
- 2026-11-25: forms A, B, C and D are DONE on their branches. The
  findings record compares them and gives the recommendation. The owner
  decision is open.

## Base form

DONE on the branch `claim-proof-pilot`.

### Readiness facts (model package)

The kind rule `runScriptStep_plainDelete_eq` continues when the clock and
counter checks pass, the table is present, `Resolved.subqueriesPlain` of the
subqueries is true and `deleteJsonReady` is true. The new facts are data
facts. They mention no step.

- `Resolved.anyMayFail_eq_false_iff` (`Queries/Evaluation/QueryPlainLaws.lean`):
  for each context, list of rows and list of expressions, `anyMayFail` is
  false exactly when each listed expression, evaluated in the context over
  each listed row, has the fault `none`. This is the general form: an
  equivalence with no premise.
- `Resolved.anyMayFail_of_rowwise` (`Queries/Evaluation/RowwiseExpr.lean`):
  for each list of row-wise expressions, each context and each list of rows,
  `anyMayFail` is false. The WHERE test of `deleteJsonReady` and the WHERE
  and SET tests of `updateJsonReady` have this form, so the fact serves a
  later UPDATE fact too. The RETURNING test of `updateJsonReady` is a
  separate test that this fact does not cover. The fact leaves out an
  expression that is not row-wise, for example one with a subquery or a
  function call; for such an expression the equivalence above still applies.
- `deleteJsonReady_of_rowwise` (`Schema/Writes/JsonReadyLaws.lean`, new
  module, imported by `Model.lean`): for each optional filter whose
  expression is row-wise, each context, each table and each list of
  RETURNING columns, `deleteJsonReady` equals the RETURNING check alone. With
  no RETURNING it is true. It leaves out a filter that is not row-wise.
- The clock and counter conditions come from `Resolved.Statement.Calm`
  (`Calm.readsClock`, `Calm.firstUnknown`) and `Resolved.Expr.Rowwise.calm`;
  `Resolved.subqueriesPlain []` is true by computation. No new fact is needed
  for them.
- No package theorem states that the step of a DELETE continues (ADR 0033,
  D7).

Elaboration time of the changed model modules (`lake env lean`, lower of two
runs, local): `QueryPlainLaws` 1.98 s, `RowwiseExpr` 0.46 s,
`JsonReadyLaws` 0.26 s.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local).

### The weaker site and the frame client statement (fixtures)

- `PurgeFrameSite` (`tests/surface/Schema/Tests/PurgeFrameSite.lean`) has
  only the database as its parameter. The field `purgeModeled` is removed;
  the values of the parameters are no longer part of the site.
- `PurgeFrameSite.purge_continues` (same file, a client lemma, not a package
  theorem): for each site, environment and pair of values, the step of the
  purge continues. Its proof applies `runScriptStep_plainDelete_eq` with
  `Resolved.Statement.Calm` of the delete and `deleteJsonReady_of_rowwise`.
- `purge_keeps_rows` and `purge_frame`
  (`tests/surface/Programs/Scripts/PurgeFrameClaims.lean`) take the weaker
  site. The pre of `purge_frame` is `Nonempty (PurgeFrameSite db)`.
- New fixture `tests/surface/Schema/Tests/PurgeFrameSchema.lean`: the
  database `sessions` and `sessionsEntry` (moved from the instances), the
  lookup `sessions_found`, the site `sessionsSite` for each database with
  `db.HasCatalog sessions`, and the frame client statement
  `purge_frame_on_sessions` with the catalog as its only premise.
- `tests/surface/Schema/Tests/PurgeFrameInstances.lean`: the site-for-values
  theorems (`null_customer_has_a_site`, `null_time_has_a_site`,
  `text_time_has_a_site`, with `modeledAtFifty` and `fiftySite`) are replaced
  by uses of `purge_frame_on_sessions` (`null_customer_keeps_the_frame`,
  `null_time_keeps_the_frame`, `text_time_keeps_the_frame`).
  `purge_frame_typed` has the catalog as its pre. The decide checks stay.
- `big_after_delete` in `SelectContextCases.lean` still has a premise
  `modeled` that its DELETE step continues. It does not use the site and is
  outside this task.
- The fields of `sessionsSite`: the position, the entry, the names and the
  two states after the resolution are values of `sessions`. `keyAlias` is
  decided by the kernel. `found` and `claimResolves` rewrite the catalog of
  the database to that of `sessions` with the premise, then the kernel
  decides them. `purgeResolves` rewrites the resolution state of the idle
  connection with `Database.resolveState_of_catalog`, then the kernel
  decides it.
- Tests: `test_purge_frame_claim_over_every_database` compiles the chain
  with `PurgeFrameSchema`; the new module is in the `surface` roots.

Elaboration time of the fixtures (lower of two runs, local):
`PurgeFrameQueries` 1.0 s, `PurgeFrameSite` 1.0 s, `PurgeFrameClaims`
1.3 s, `PurgeFrameSchema` 1.3 s, `PurgeFrameInstances` 3.1 s.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local); `python3 -m pytest tests/surface_assertion_examples_test.py -k purge`
passed (local); `python3 -m pytest tests/test_source_identity_derivations.py`
passed (local).

### The effect claim (fixtures)

- New fixture `tests/surface/Programs/Scripts/PurgeEffectClaims.lean`:
  - `purgeClears`: `SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE
    customer_id = $c AND expires_at < $now)`.
  - `purgeClears_iff`: on a database with the catalog of `sessions`, the
    claim holds exactly when the filter is true for no row of the table.
    The proof uses `resolveStatement_selectOne_notExists`, `tableOne_run`
    and `whereOne_claims`, as the task file says.
  - `purge_clears`: the effect client statement, with the catalog as its
    only premise. The proof runs the purge with `sql_run`, with
    `PurgeFrameSite.purge_continues` as the hint for the step. It reads the
    rows that `LiteralData.deleted` keeps and uses
    `Resolved.Expr.Rowwise.evaluate_congr` to move the filter from the
    context of the statement to the two values.
- New fixture `tests/surface/Schema/Tests/PurgeEffectInstances.lean`: a use
  of `purge_clears` on `sessions`, and decide checks that the claim is false
  before the purge and true after it (integer time and text time), true
  before and after for a NULL customer, and false after an aborted purge.
- Tests: `test_purge_frame_claim_over_every_database` compiles the chain
  with `SelectOneWhereSupport`, `PurgeEffectClaims` and
  `PurgeEffectInstances`, timeout 300 s. Both new modules are in the
  `surface` roots.
- Effort, for the findings record: `purge_clears` and `purgeClears_iff` are
  about 45 proof lines. No package code was needed beyond the readiness
  facts.

Elaboration time of the fixtures (lower of two runs, local):
`SelectOneWhereSupport` 1.0 s, `PurgeEffectClaims` 1.2 s,
`PurgeEffectInstances` 1.7 s.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local); `python3 -m pytest tests/surface_assertion_examples_test.py -k purge`
passed (local); `python3 -m pytest tests/test_source_identity_derivations.py`
passed (local).

### Final checks of the base form

Checks run on the last commit, local outcome only, not evidence:

- `just dev-build`: passed (local).
- `just test-full`: the first run failed in `tests/test_model_package.py`,
  because the new module `JsonReadyLaws` was not in the core library of
  `lakefile.toml`. The readiness commit now lists it. The second run failed
  with a timeout of 120 s in `test_stateful_modes[True]` of
  `tests/conformance_generation_test.py` at a load average of about 15. The
  third run, at a lower load, passed (local).
- `just verdict`: passed (local), with no change in the counts of the
  corpora.

## Forms A to D

Each form is DONE on its branch. The status file of that branch has the
section of the form: its declarations, the general form of each new law,
its measurements, its limits and its checks. A form branch does not have
the commits of this branch that come after `ff882f8d`.

| Form | Branch | Last code revision | Last revision |
| --- | --- | --- | --- |
| A | `claim-proof-pilot-logic` | `a1705c06` | `40986de1` |
| B | `claim-proof-pilot-laws` | `0f070f76` | `364d10fb` |
| C | `claim-proof-pilot-tactic` | `5bc3c323` | `2a2db889` |
| D | `claim-proof-pilot-checker` | `8e136beb` | `1795538c` |

Checks of each form at its last code revision, local outcome only, not
evidence: `just dev-build`, `just test-full` and `just verdict` passed
(local). For form C, `just test-full` ran at `3c505c1d`, and
`just dev-build` and `just verdict` ran at `5bc3c323`, which changes one
docstring line.

## Form B

In progress on the branch `claim-proof-pilot-laws`.

### The bridge laws (surface package)

New module `packages/belay/Belay/Sqlite/Programs/Claims/ResolvedOutputBridge.lean`.

- `Script.observeTwoStateIn_resolved`: for a script of one SELECT
  statement with values, an initial database and a context, when
  `resolveTwoState` gives a resolved statement, the two-state observation
  equals `resolvedStepOutput` of that statement at the clock, index and
  connection of the context, with the initial database exactly when
  `usesSchema` is true. An equation, with no other premise.
- `Holds.inContextSince_iff_hasRows`: the same premises; the two-state
  assertion holds exactly when that output has rows. This is the law that
  the task file asks for.
- `Holds.inContext_iff_hasRows`: the one-state analog. When the one
  statement resolves in the resolution state of the context's connection,
  `Holds.inContext` holds exactly when the output of the resolved statement
  (without an initial database) has rows.
- What they leave out: a script of more than one statement. The frame
  proof uses `Script.observeTwoStateIn_resolved`, and the effect proof
  uses `Holds.inContext_iff_hasRows`.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local).

### The laws of the parts (model package)

- `resolvedStepOutput_calm_hasRows`
  (`Tooling/Counterexamples/TwoStateQuerySteps.lean`): for a calm query
  statement observed with an optional initial database, with its source
  rows and its bound window, the output has rows exactly when the source
  has no fault `may`, the run has no mismatch, no overflow and no fault,
  and the one result of the bound query has a row. An iff. It replaces
  `resolvedStepOutput_query_hasRows_of_clean_from`, which gave only the
  sufficient direction for an initial database that is present. The
  wrapper is deleted, and its caller uses the iff.
  `Connection.queryContextFrom` now takes an optional initial database.
- `resolvedStepOutput_selectOneWhere_hasRows` (same module): for
  `SELECT 1 WHERE c` with any list of subqueries and an optional initial
  database, calm and with no fault of `c` over the empty row, the output
  has rows exactly when `c` is true over the empty row in the context of the
  statement. An iff. It leaves out a condition with a fault.
- `Resolved.Expr.truthy_exists` and `Resolved.Expr.truthy_notExists`
  (`Queries/Evaluation/ExprEvalLaws.lean`): EXISTS of a subquery is true
  exactly when the run of the subquery has a row; NOT EXISTS exactly when it
  has none. Equations, for each context, row and index.
- `Resolved.subqueryContext_subqueries` and
  `Resolved.statementContext_subqueries`
  (`Schema/Dispatch/Subqueries.lean`): the subquery at an index of the
  context of the statement (or of a depth) is the run of that query in the
  context one depth lower. Equations.
- `Resolved.Query.simple_subqueryRun`
  (`Schema/Dispatch/SelectSubqueryRules.lean`): the read of a simple query
  with a filter and scalar columns, as a subquery. With source rows that
  have no fault and expressions with no fault and no fallible call, the run
  has as rows the columns of the source rows that the filter keeps, no fault,
  and the ending `done`. With `Query.source_first_from` it reads the table of
  the current database, and with `Query.source_initialTable` the table of the
  initial database. Equations under the premises; it leaves out a query with
  a fallible call, an ordering, a window or a grouping, and a source with a
  fault.
- `Resolved.equalRowsIdentical_rowidFirst` (new module
  `Schema/Columns/RowidOutputIdentity.lean`): for a table with distinct
  rowids whose first column is the rowid alias, and each of whose rows
  stores its rowid in that column (`Table.RowsAliased`), the outputs of
  column 0 followed by any columns, over any list of source rows of the
  table, are identical where they compare equal. This is the premise `identical` of
  `Resolved.Query.PlainExcept.subqueryRun`, the law of the EXCEPT compound
  (an equation of its rows with `CompoundOperator.combine` of the rows of its
  terms). In the frame proof it replaces
  `Resolved.notExistsExcept_identical`, which fixes the term of the
  two-state form.
- `LiteralData.mem_deleted` (`Schema/Columns/RowDelete.lean`): a row is in
  the table that a DELETE leaves exactly when it is in the table and the
  filter does not select it. An iff with no premise.
- `Value.IsLogical`, `Comparison.apply_isLogical`, `Value.truthy_isNot_one`,
  `Resolved.Expr.isLogical`, `Resolved.inValue_isLogical`,
  `Resolved.Expr.eval_isLogical` and `Resolved.Expr.truthy_isNot_one`
  (new module `Queries/Evaluation/LogicalValueLaws.lean`): a comparison,
  AND, OR, NOT, IS NULL, EXISTS and IN give NULL, 0 or 1; for such an
  expression `e IS NOT 1` is true exactly when `e` is not true. An equation.
  It generalizes `Resolved.Expr.truthy_isNot_one_and` (AND only, one
  direction), which is deleted with `Value.and_cases` and
  `truthy_isNot_one_of_cases`. It leaves out a column, a literal and the other forms, whose
  value can be 2: then `e` and `e IS NOT 1` are both true.

### The effect claim (fixtures)

- `purgeClears_iff` and `purge_clears` keep their statements. The proof of
  `purgeClears_iff` uses `Holds.inContext_iff_hasRows`,
  `resolvedStepOutput_selectOneWhere_hasRows`,
  `Resolved.Expr.truthy_notExists`, `Resolved.statementContext_subqueries`
  and `Resolved.Query.simple_subqueryRun` with `Query.source_first_from`. The
  kernel decides the resolution of the claim on the catalog of `sessions`
  and the calm check of the statement. `purge_clears` uses
  `LiteralData.mem_deleted`. The proof uses no
  `resolveStatement_selectOne_notExists`, `tableOne_run` or
  `whereOne_claims`, and `PurgeEffectClaims` no longer imports
  `SelectOneWhereSupport`.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local); `python3 -m pytest tests/surface_assertion_examples_test.py -k purge`
passed (local).

### The frame claim (fixtures)

- `purge_keeps_rows` and `purge_frame` keep their statements. The proof of
  `purge_keeps_rows` composes the laws of the parts:
  `Script.observeTwoStateIn_resolved` with `PurgeFrameSite.claimResolves`,
  `resolvedStepOutput_selectOneWhere_hasRows`,
  `Resolved.Expr.truthy_notExists`, `Resolved.statementContext_subqueries`
  and `Resolved.subqueryContext_subqueries` for the three subqueries,
  `Resolved.Query.PlainExcept.subqueryRun` for the compound, and
  `Resolved.Query.simple_subqueryRun` with `Query.source_initialTable` and
  `Query.source_first_from` for the two terms. The compound is empty by
  `CompoundOperator.except_combine_eq_nil`, with `mem_sourceRows_iff`,
  `LiteralData.mem_deleted`, `Resolved.Expr.truthy_isNot_one` and
  `Resolved.Expr.Rowwise.evaluate_congr`. The identity premise of the
  compound is `Resolved.equalRowsIdentical_rowidFirst`.
- The proof uses no `resolvedStepOutput_notExistsExcept_hasRows`,
  `Resolved.notExistsExcept_subset`, `Resolved.notExistsExcept_identical`
  or `Resolved.Expr.truthy_isNot_one_and`. It uses the same laws for
  SELECT 1 WHERE, NOT EXISTS, the subqueries of the statement and the read
  of one table as the effect proof.
- `PurgeFrameQueries` gives the two terms (`purgeKeepsInitialTerm`,
  `purgeKeepsCurrentTerm`), the list of the three subqueries
  (`purgeKeepsSubqueries`) and the resolved statement
  (`purgeKeepsResolved`) of the claim, and `purgeKeepsResolved_calm`. The
  proof states the run of the compound once for the context of the
  statement, with `purgeKeepsSubqueries`.
  `Resolved.Query.simple_expressions_rowwise` moves to
  `Queries/Evaluation/RowwiseExpr.lean`.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local); `python3 -m pytest tests/surface_assertion_examples_test.py -k purge`
passed (local).

### Deletions and retention

- Deleted modules of the model package, with their entries in `Model.lean`
  and `lakefile.toml`: `Queries/Evaluation/TwoStateNotExistsExcept`,
  `Queries/Evaluation/TwoStateKeptRows`,
  `Queries/Evaluation/TwoStateNotExistsExceptOutput`,
  `Schema/Dispatch/TwoStateNotExistsExcept`,
  `Schema/Columns/TwoStateKeptRows` and
  `Tooling/Counterexamples/TwoStateNotExistsExceptOutput`. With them go
  `Resolved.notExistsExcept`, `Resolved.initialTerm`,
  `Resolved.currentTerm`, `Resolved.notExistsExceptSubqueries`,
  `Resolved.notExistsExcept_calm`, `Resolved.notExistsExcept_context_zero`,
  `Resolved.initialTerm_mem_results`, `Resolved.currentTerm_mem_results`,
  `Resolved.notExistsExcept_subset`, `Resolved.notExistsExcept_identical`
  and `resolvedStepOutput_notExistsExcept_hasRows`.
- `Resolved.Query.simple_results_congr` is a general law, not a law of the
  form: it moves to `Queries/Evaluation/RowwiseExpr.lean`, which now
  imports `SelectSubqueryRules`. `Model.lean` now imports
  `Tooling/Counterexamples/TwoStateQuerySteps` directly; the deleted
  module imported it before.
- `Resolved.Expr.Rowwise` and its laws stay.
- The records `docs/records/spec-proof-agreement-targets.md` and
  `docs/records/select-automation-retirement.md` get a dated note on the
  deleted declarations.
- Retention fixtures `tests/surface/Queries/Evaluation/PurgeLawRetention.lean`
  and `PurgeLawRetentionOutput.lean` restate `initialTerm`, `currentTerm`,
  `notExistsExceptSubqueries` and `notExistsExcept` in the namespace
  `PurgeLawRetention`, and prove the statements of the base revision of
  `Resolved.Expr.truthy_isNot_one_and`, `Resolved.notExistsExcept_subset`,
  `Resolved.notExistsExcept_identical` and
  `resolvedStepOutput_notExistsExcept_hasRows` from the laws that remain.
  The statement text is the text of the base revision; the namespace of the
  fixture is the only change. Each has a `#print axioms` report, and the
  purge test checks the counts (3 and 1). Both modules are roots of the
  suite `surface`.
- `purge_frame` (each database with a site) stays proved.

Checks run, local outcome only, not evidence: `just dev-build` passed
(local); `python3 -m pytest tests/surface_assertion_examples_test.py -k purge`
passed (local); `python3 -m pytest tests/test_lean_categories.py` passed
(local). The brief of this form does not allow a direct `nix-build` between
the gates. `tests/test_model_package.py` starts `nix-build` itself; the run
stopped at its timeout of 120 seconds and is not run again. `just test-full`
at the end of the form runs the package checks.

## Findings record

`docs/records/claim-proof-pilot-findings.md` is written. The code-line
counts in it come from `scc` 3.7.0 over the Lean files of each revision,
without the three frozen experiments, as
`docs/development/lean-simplification-goal.md` counts them.

At the time of the record, the owner decision was open; the section
"Owner decision" gives it. After it, the task file records the decision,
and the branch of the selected form becomes the pull request, with
`just test-nix` and `just test-scheduled-checks` once before it.

## Affected laws

Owner question of 2026-11-25: which laws of today change if the project
adopts the recommendation. `docs/records/claim-proof-pilot-affected-laws.md`
lists them by name, in three groups: changed on the pilot branch,
declarations of one query form, and laws of writes. Each declaration of one
query form has a status that names the decision or the missing law that it
depends on. The record also lists the test declarations that name a listed
declaration, and the listed laws that are in the set `sql_simp`. Sources:
the comparison of the declarations of `1e8dfd8d` with `5bc3c323`, a
classification of each theorem of the packages and of `tests/surface` by
twelve readers, and a search by name for the users of each law. The record
names four decisions that the list depends on. Test of the commit:
`python3 -m pytest tests/docs_test.py`.

The first review of the record (`reviews/20261125T073157Z-0428f77d`) had 13
"must" findings. Their common cause: the record gave "replaced by" as a
result where the pilot had no proof. The corrected record gives, for each
law outside the pilot branch, the condition under which it can go, and says
where the pilot did not examine a point.

The second review (`reviews/20261125T080617Z-19912b7f`) had 12 "must"
findings. Their common causes: the search for users read only the text of
named declarations, so it did not find anonymous examples, `#print axioms`
checks, Lean code in Python tests and one use through dot notation; and
some statements were more general than the code. The corrected record
searches all Lean and Python files of `1e8dfd8d` under `packages`, `tests`
and `tools`, has the status G for the
four cases of a general law that stays, moves the comparison of a column
with a parameter out of the list, and states decision 1 for the two ways in
which the claims of today are general: a part of the catalog, and a
variable condition.

The third review (`reviews/20261125T083446Z-ae782c44`) had 8 "must"
findings: six about a summary that said more than the laws state, and two
about omissions (the references in docstrings, and the claim law
`BalanceExample.count_run`). The
corrected record gives the premises of the `Calm` laws and of the laws of
`IN` and `EXISTS` as the code has them, limits the conditions of decision 1
to the laws that they apply to, and lists the docstrings that have a
checked reference to a listed declaration.

The fourth review (`reviews/20261125T084306Z-ba07cb92`) had 4 "must"
findings and 3 "should" findings. Four reviews in a row had "must"
findings, so the work stopped, and the owner decided on 2026-11-25 to
correct the record and review it again. The corrected record names the
two NULL premises of the law of `NOT IN`, states that the calm check proves `Calm`
only when it reduces to `true`, names the resolution law that takes the
resolution of the filter as a premise and one that does not, and states
that `sql_holds` needs the catalog of each database that the claim
reads. It counts 6 docstrings outside the lists, not 8: two of the
owners were in the lists.

The fifth review (`reviews/20261125T123839Z-1c050a90`) had 6 "must"
findings: three about the record and three about the decision text in
this file and in the task file. The record now refers to the docstring
of the law of `NOT IN` for its premises and does not restate them, and
it states the two forms of a hint of `sql_holds`.

## Owner decision

On 2026-11-25 the owner accepted the recommendation of the findings
record. The task file records the decision. Next: the pull request from
`claim-proof-pilot-tactic` on top of `adr-0033-phase-8-inventory`. Before
the final checks, the proofs of form B that the branch keeps only for the
comparison are removed, so that each claim has one proof; the retention
fixtures stay. Then `just test-nix` and `just test-scheduled-checks` run
once.
