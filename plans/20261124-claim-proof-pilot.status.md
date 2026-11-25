# Status: pilot of the forms of proof for a claim in SQL

Created 2026-11-24.
Status: OPEN. The pilot is complete. The owner selected the branch
`claim-proof-pilot-tactic` on 2026-11-25. The branch
`claim-proof-sql-holds` has it for the pull request; the checks of the
pull request are pending.
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
- 2026-11-24, form B: review fixes (the note on the consumer test of the
  model package, the clock and the index in the retention output law).
- 2026-11-24, form B: measurements (replaced laws, lines per claim, code
  lines, tactic steps, elaboration times).
- 2026-11-24, form C: the tactic `sql_holds`, the bridge laws over a
  catalog, the decidable row-wise check, the read law with the bound values,
  the client proofs of the effect and frame claims, a third claim and the
  negative cases.
- 2026-11-24, form C: review fixes (the row-wise check in the model's
  globs, the tactic keeps the other goals, the table law moves to the model
  as `Model.Database.table_of_sameCatalog`, the messages name the column
  names and the expression that is not calm, the fixture `PurgeTacticCases`
  with an `EXISTS` claim, status text and `scc` counts).
- 2026-11-24, form C: second review fixes (a two-state claim without a
  schema name needs no catalog of the start, the message when the kernel
  does not decide the calm check, a checked docstring example, plain words
  of `Model.Database.table_of_sameCatalog`).
- 2026-11-25, form C: the module text of `sql_holds` names the one-state
  step; `just test-full` and `just verdict` passed (see "## Form C").
- 2026-11-25: forms A, B, C and D are DONE on their branches. The
  findings record compares them and gives the recommendation. The owner
  decision is open.
- 2026-11-25, pull request: the branch `claim-proof-sql-holds` has, on top
  of `adr-0033-phase-8-inventory` (`6a6de020`), copies of the commits of
  `claim-proof-pilot` up to `2dd24dc4` and of the commits of
  `claim-proof-pilot-tactic` after `ff882f8d` up to `2a2db889`. The later
  commits of `claim-proof-pilot` (`6d060eb3` to `c314ed38`: the last
  corrections of the affected-laws record and their review records) are
  not copied one by one; the commit "docs: the last review fixes of the
  affected-laws record on the pull request branch" has their content. The proof of the effect claim that composes
  the laws by hand is removed, with its helpers: `purge_clears` (form B),
  `purgeClears_iff`, `purgeClearsStatement` and `purgeClearsSubquery`. The
  proof with `sql_holds` moves from the deleted module `PurgeEffectTactic`
  to `PurgeEffectClaims` and gets the name `purge_clears`. The frame proof
  of form B (`purge_frame`, `purge_keeps_rows`) stays, because it proves the
  claim for each database with a site, which is more general than the
  catalog premise of the proof with the tactic. The retention fixtures stay.
  Tests: `python3 -m pytest tests/surface_assertion_examples_test.py -k
  purge`, and `python3 -m pytest tests/docs_test.py`.
- 2026-11-25, pull request: the statement of the frame claim with the
  catalog premise keeps one proof, the proof with `sql_holds`. The
  corollary `purge_frame_on_sessions` of `purge_frame` in
  `PurgeFrameSchema` is removed, and the proof `purge_frame_by_tactic` in
  `PurgeFrameTactic` gets its name. The instances in `PurgeFrameInstances`
  use this proof. The more general theorem `purge_frame`, for each
  database with a site, stays. Tests: `python3 -m pytest
  tests/surface_assertion_examples_test.py -k purge`, and `python3 -m
  pytest tests/docs_test.py`.
- 2026-11-25, pull request: one test compiles each fixture of the two
  purge tests once.
  `test_purge_frame_claim_over_every_database` has the modules of the
  former test `test_purge_claims_by_the_claim_tactic`, which is removed.
  Tests: `python3 -m pytest tests/surface_assertion_examples_test.py -k
  purge`.

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

Done on the branch `claim-proof-pilot-laws`.

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
stopped at its timeout of 120 seconds and is not run again. Its consumer
test has the marker `requires_nix`, so `just test-nix` runs it once, before
the pull request of the selected branch, as the task file says.

### Measurements (local)

Laws that form B replaces, and what replaces them:

| Deleted | Replaced by |
| --- | --- |
| `resolvedStepOutput_query_hasRows_of_clean_from` | `resolvedStepOutput_calm_hasRows` (an iff, optional initial database) |
| `resolvedStepOutput_notExistsExcept_hasRows` | `Script.observeTwoStateIn_resolved`, `resolvedStepOutput_selectOneWhere_hasRows`, `Resolved.Expr.truthy_notExists`, `Resolved.statementContext_subqueries`, `Resolved.subqueryContext_subqueries`, `Resolved.Query.PlainExcept.subqueryRun`, `Resolved.Query.simple_subqueryRun` |
| `Resolved.notExistsExcept_subset` | `LiteralData.mem_deleted`, `mem_sourceRows_iff`, `Resolved.Expr.truthy_isNot_one` (the subset step of the client proof) |
| `Resolved.notExistsExcept_identical` | `Resolved.equalRowsIdentical_rowidFirst` |
| `Resolved.Expr.truthy_isNot_one_and`, `Value.and_cases`, `truthy_isNot_one_of_cases` | `Resolved.Expr.eval_isLogical`, `Value.truthy_isNot_one`, `Resolved.Expr.truthy_isNot_one` |

The effect proof no longer uses the fixture `SelectOneWhereSupport`
(`resolveStatement_selectOne_notExists`, `tableOne_run`, `whereOne_claims`);
other fixtures still use it, so it stays.

Lines of the client proofs (code lines, without docstrings; the statement
is the lines up to `:= by`):

| Claim | Base: statement / proof | Form B: statement / proof | Form B helpers |
| --- | --- | --- | --- |
| `purge_keeps_rows` | 6 / 27 | 6 / 71 | `PurgeFrameQueries`: `purgeKeepsInitialTerm` 3, `purgeKeepsCurrentTerm` 2, `purgeKeepsSubqueries` 2, `purgeKeepsResolved_calm` 2 |
| `purge_frame` | 3 / 7 | 3 / 7 | none |
| `purgeClears_iff` | 4 / 16 | 4 / 30 | `purgeClearsStatement` 1, `purgeClearsSubquery` 3 |
| `purge_clears` | 2 / 21 | 2 / 20 | none |

In the base form, `purge_keeps_rows` used the laws of the fixed form
(`resolvedStepOutput_notExistsExcept_hasRows` and its two premise laws,
about 290 package lines), and `purgeClears_iff` used the 72 code lines of
`SelectOneWhereSupport`. In form B, the client proofs carry the
composition.

Code lines with scc 3.7.0 (`Code` field), over the Lean files that the
branch changes, base revision `xvwqrnqr` against `wmklzsxl`:

- Packages: 790 to 729 (net -61). The new laws add 231 lines (by a
  count without docstrings and comments); the deletions remove 292. Each
  new law serves each claim of its kind; none names a purge table, column
  or value.
- Tests: 147 to 364 (+217). The client fixtures add 70 lines; the
  retention fixtures (`PurgeLawRetention`, `PurgeLawRetentionOutput`) add
  147 lines.

Steps that form C (a tactic) could do, as the two client proofs show them:

- The chain from the observation to the subquery runs: rewrite with
  `Script.observeTwoStateIn_resolved` or `Holds.inContext_iff_hasRows`,
  apply `resolvedStepOutput_selectOneWhere_hasRows`, rewrite with
  `Resolved.Expr.fault_not`, `Resolved.Expr.fault_exists`,
  `Resolved.Expr.truthy_notExists` and
  `Resolved.statementContext_subqueries`, then
  `Resolved.subqueryContext_subqueries` for each term of a compound. Each
  step is syntax-directed by the resolved statement.
- The side goals: the calm check of the statement (decided by `rfl`), the
  row-wise proofs of the filter and the columns, and the faults of each read
  (`Resolved.Expr.Rowwise.fault_none`).
- The read of each table: `Resolved.Query.simple_subqueryRun` with
  `Query.source_first_from` or `Query.source_initialTable`, and the `erw`
  steps that unfold the named terms of the claim.
- The membership goals over `filter` and `map` of the source rows
  (`List.mem_map`, `List.mem_filter`, `mem_sourceRows_iff`).

The steps that remain for the user are the core of each claim: the subset
step (`LiteralData.mem_deleted` with the truth of the condition) and the
identity premise of `EXCEPT` (`Resolved.equalRowsIdentical_rowidFirst`
with the admitted table).

`CompoundOperator.except_combine_eq_nil` gives only the sufficient
direction: `EXCEPT` is empty when each row of the first term is a row of the
second. The converse needs equality under the collations, not membership,
so the frame proof proves the claim and not an iff.

Elaboration time (lower of two runs, local):

- Fixtures (the compile of the purge test): `PurgeFrameQueries` 1.2 s
  (base 1.0 s), `PurgeFrameSite` 1.0 s, `PurgeFrameClaims` 1.4 s (base
  1.3 s), `PurgeFrameSchema` 1.4 s, `PurgeEffectClaims` 1.3 s (base 1.2 s,
  plus 1.0 s for `SelectOneWhereSupport`), `PurgeFrameInstances` 3.3 s,
  `PurgeEffectInstances` 1.7 s, `PurgeLawRetention` 0.9 s,
  `PurgeLawRetentionOutput` 1.1 s.
- New and changed model modules (`lake env lean`):
  `LogicalValueLaws` 1.25 s, `RowwiseExpr` 0.50 s, `ExprEvalLaws` 0.46 s,
  `RowidOutputIdentity` 0.35 s, `RowDelete` 0.27 s, `SelectSubqueryRules`
  0.44 s, `Subqueries` 0.41 s, `TwoStateQuerySteps` 1.57 s.
- `ResolvedOutputBridge` (surface package): 1.0 s, the lowest time that
  `just dev-build` printed; `lake env lean` does not find its imports
  because the two packages share the prefix `Belay.Sqlite`.

## Form C

Done on the branch `claim-proof-pilot-tactic`, on top of form B. The
comparison with the other forms is for the owner.

### The tactic (surface package)

Name and syntax: `sql_holds [h₁, …]`. Each hint is a proof of
`db.HasCatalog schema`, or of an equation of a catalog with the catalog of a
database without variables, for each database that the claim reads. Use it
on the goal of a post `holds q` or `holdsSince start q`, for example the
goal that `sql_run` leaves. The tactic introduces the premises that stay in
the goal, so it can run as soon as the claim is the conclusion of the goal.
It works on the main goal and keeps the other goals.

Mechanism. The tactic introduces the premises and unfolds `holds` and
`holdsSince`. Then it applies these laws in order. Each law is a theorem. The tactic
closes each premise of a law with a hint or with a computation that the
kernel checks, except one: the identity premise of the `EXCEPT` law, which it
returns as the goal `identical`:

- For `holdsSince start q`, when the kernel decides that `q` is a `SELECT`
  that names no schema: `Holds.reachedSince_iff_reached`, which makes it a
  one-state claim. It then needs no catalog of the start.
- The bridge `Holds.reached_iff_of_catalog` or
  `Holds.reachedSince_iff_of_catalog` (new module
  `Programs/Claims/CatalogClaimBridge.lean`). The kernel resolves the claim
  on the catalog of the hint.
- `resolvedStepOutput_selectOneWhere_hasRows` for `SELECT 1 WHERE c`. The
  calm premise comes from `Resolved.Statement.calm_of_calmCheck`, which the
  kernel decides.
- `Resolved.Expr.truthy_notExists` or `Resolved.Expr.truthy_exists`. The
  premise that `c` has no fault comes from `Resolved.Expr.fault_not`,
  `Resolved.Expr.fault_exists` and the fault of the run of the subquery.
- For each subquery: `Resolved.statementContext_subqueries` or
  `Resolved.subqueryContext_subqueries`, then the law of its form:
  - one table of the current or the initial database, with row-wise
    expressions and no other clause: the new law
    `Resolved.Query.simple_subqueryRun_rowwise`, with
    `Query.source_first_from` or `Query.source_initialTable`. The row-wise
    premises come from `Resolved.Expr.rowwise_of_all` and
    `Resolved.QuerySource.rowwise_of_all`, which the kernel decides;
  - `EXCEPT` of two terms: `Resolved.Query.PlainExcept.subqueryRun`. The
    shape premise is closed by `constructor` and `rfl`. The premise
    `equalRowsIdentical` stays open as the goal `identical`.
- Each open goal is simplified with `List.isEmpty_iff`,
  `List.map_eq_nil_iff`, `List.filter_eq_nil_iff`, `Option.all_some`,
  `Option.all_none`, `Bool.not_eq_true`, `Bool.not_eq_true'` and
  `List.isEmpty_eq_false_iff_exists_mem`, and the connection and context
  functions are unfolded.

No step names the purge, `sessions` or a claim shape as a whole. The query
of the claim selects the laws by its resolved form.

Code lines (without docstrings, comments and blank lines):

| File | Code lines | All lines |
| --- | --- | --- |
| `Programs/Automation/SqlHoldsFacts.lean` (applying one law, messages) | 79 | 114 |
| `Programs/Automation/SqlHoldsRuns.lean` (the runs of subqueries) | 94 | 127 |
| `Programs/Automation/SqlHolds.lean` (bridge, SELECT 1 WHERE, EXISTS, syntax) | 100 | 151 |
| Tactic total | 273 | 392 |
| `Programs/Claims/CatalogClaimBridge.lean` (bridge laws over a catalog) | 50 | 86 |
| Model: `Queries/Evaluation/RowwiseCheck.lean` (decidable row-wise check) | 32 | 54 |
| Model: `Resolved.Query.simple_subqueryRun_rowwise` in `RowwiseExpr.lean` | 28 | 43 |
| Model: `Resolved.Statement.calm_of_calmCheck` in `ExprFormChecks.lean` | 3 | 5 |
| Model: `Database.table_of_sameCatalog` in `Schema/Ddl/DatabaseLookup.lean` | 8 | 12 |

The counts of whole files are the `Code` and `Lines` fields of `scc`.

Other changes:

- `Belay.Sqlite.Select.evaluationProof?` (`SqlSelectEval.lean`, the
  helper of `sql_select`) now checks its auxiliary theorem synchronously
  and restores the state when the kernel refuses it. Before, with
  `Elab.async`, the kernel check ran in a background task: a false
  equation gave a proof, and the error came only at the end of the
  declaration. The docstring said that the result is `none` when the
  kernel accepts no proof; that is now true. The tests of `sql_select`
  check this change.
- `Model.Database.table_of_sameCatalog` (model, `DatabaseLookup.lean`): the
  table at a position of a database with the catalog of a fixed schema. The
  tactic and the identity steps of the client proofs use it.
- `Holds.reachedSince_iff_of_catalog` takes the choice of the initial
  database as a premise `(if usesSchema … then some initial.raw else none)
  = chosen`, so that the kernel computes the choice.

### The client proofs (fixtures)

New fixtures, roots of the suite `surface`, in the test
`test_purge_claims_by_the_claim_tactic`:

- `tests/surface/Programs/Scripts/PurgeEffectTactic.lean`:
  `purge_clears_by_tactic`, the statement of `purge_clears`.
- `tests/surface/Programs/Scripts/PurgeFrameTactic.lean`:
  `purge_frame_by_tactic`, the statement of `purge_frame_on_sessions`; the
  third claim `purgeAddsNone` and `purge_adds_none`.
- `tests/surface/Programs/Scripts/PurgeTacticCases.lean`: `sessions_exists`,
  an `EXISTS` claim with a witness row as the first goal of `∧`, where the
  tactic keeps the second goal; `sessions_exists_since`, the same claim as
  a two-state claim with no catalog of the initial database; then eleven
  negative cases with `#guard_msgs`.

The proofs of form B stay in `PurgeEffectClaims.lean`,
`PurgeFrameClaims.lean` and `PurgeFrameSchema.lean`. The new proofs use the
base helpers `sessions_found`, `sessionsSite` (for `purgeResolves`) and
`PurgeFrameSite.purge_continues`, as form B does, before `sql_run`.

Each proof has 10 lines up to `sql_run` (as in form B), then `sql_holds
[schema]`, then the steps about rows:

- Effect: `mem_sourceRows_iff`, `Model.Database.rows_getD_setRows`,
  `LiteralData.mem_deleted` and the congruence of the row-wise filter
  (`Resolved.Expr.Rowwise.evaluate_congr`).
- Frame: `CompoundOperator.except_combine_eq_nil` with the subset step
  (`mem_sourceRows_iff`, `rows_getD_setRows`, `LiteralData.mem_deleted`,
  `Resolved.Expr.truthy_isNot_one`, `Rowwise.evaluate_congr`), and the goal
  `identical` from `Resolved.equalRowsIdentical_rowidFirst` with the
  admitted table of `Model.Database.table_of_sameCatalog`.
- Third claim: the same, with the terms of `EXCEPT` in the other order.
  The subset step is `LiteralData.mem_deleted` (a kept row is a row of the
  start). The identity premise uses the validity of the reached database
  (`valid.1.admitted.table`).

Client lines per claim (lines; the statement is the lines up to `:= by`):

| Claim | Form B: statement / proof / helpers | Form C: statement / proof (after `sql_holds`) / helpers |
| --- | --- | --- |
| Effect | `purgeClears_iff` 4 / 30 and `purge_clears` 2 / 20; helpers `purgeClearsStatement` 1, `purgeClearsSubquery` 3 | `purge_clears_by_tactic` 2 / 18 (7); none |
| Frame | `purge_keeps_rows` 6 / 71, `purge_frame` 3 / 7, `purge_frame_on_sessions` 3 / 1; helpers in `PurgeFrameQueries` 9 | `purge_frame_by_tactic` 3 / 29 (18); none |
| Adds no session | not proved | `purge_adds_none` 3 / 24 (13), `purgeAddsNone` 2; none |

What the third claim took: the claim (2 lines) and its proof (27 lines with
the statement). The tactic needed no change: the run of `EXCEPT` with the
current table first and the initial table second goes through the same
laws.

The goals that the tactic leaves, verbatim (targets only; `_` is the proof
of the catalog entry):

```text
case success
⊢ ∀ (a : List Value),
    a ∈
        Resolved.sourceRows
          { shape := (sessions.raw.catalog.tableAt 0).get _,
            rows :=
              (Database.setRows db.raw sessionsEntry.fst
                      (LiteralData.deleted
                          (Resolved.statementContext 0
                            (env.counters.view
                              (Resolved.Statement.delete sessionsEntry.fst (some purgeFilter) []).counterReads)
                            [c, now] db.raw [])
                          { shape := sessionsEntry.snd, rows := db.raw.rows.getD sessionsEntry.fst [] }
                          (some purgeFilter)).rows).rows.getD
                0 [] } →
      Resolved.truthy
          (Resolved.Expr.eval (Resolved.EvalContext.bound [c, now]) a
            ((Resolved.Expr.compare Comparison.eq (some Affinity.integer) (Resolved.Expr.column 1)
                  (Resolved.Expr.parameter 1)).and
              (Resolved.Expr.compare Comparison.lt (some Affinity.integer) (Resolved.Expr.column 2)
                (Resolved.Expr.parameter 2)))) =
        false
--- end of claim ---
case success
⊢ CompoundOperator.combine [Collation.binary, Collation.binary, Collation.binary] CompoundOperator.except
      (List.map
        (fun row =>
          List.map (fun x => Resolved.Expr.eval (Resolved.EvalContext.bound [c, now]) row x)
            [Resolved.Expr.column 0, Resolved.Expr.column 1, Resolved.Expr.column 2])
        (List.filter
          (fun row =>
            Resolved.truthy
              (Resolved.Expr.eval (Resolved.EvalContext.bound [c, now]) row
                (Resolved.Expr.compare Comparison.isNot none
                  ((Resolved.Expr.compare Comparison.eq (some Affinity.integer) (Resolved.Expr.column 1)
                        (Resolved.Expr.parameter 1)).and
                    (Resolved.Expr.compare Comparison.lt (some Affinity.integer) (Resolved.Expr.column 2)
                      (Resolved.Expr.parameter 2)))
                  (Resolved.Expr.literal (Value.integer (Int.ofNat 1))))))
          (Resolved.sourceRows
            { shape := (sessions.raw.catalog.tableAt 0).get _,
              rows := db.raw.rows.getD 0 [] })))
      (List.map
        (fun row =>
          List.map (fun x => Resolved.Expr.eval (Resolved.EvalContext.bound [c, now]) row x)
            [Resolved.Expr.column 0, Resolved.Expr.column 1, Resolved.Expr.column 2])
        (List.filter (fun row => true)
          (Resolved.sourceRows
            { shape := (sessions.raw.catalog.tableAt 0).get _,
              rows :=
                (Database.setRows db.raw sessionsEntry.fst
                        (LiteralData.deleted
                            (Resolved.statementContext 0
                              (env.counters.view
                                (Resolved.Statement.delete sessionsEntry.fst (some purgeFilter) []).counterReads)
                              [c, now] db.raw [])
                            { shape := sessionsEntry.snd, rows := db.raw.rows.getD sessionsEntry.fst [] }
                            (some purgeFilter)).rows).rows.getD
                  0 [] }))) =
    []
case identical
⊢ Resolved.equalRowsIdentical [Collation.binary, Collation.binary, Collation.binary]
      (List.map
        (fun row =>
          List.map (fun x => Resolved.Expr.eval (Resolved.EvalContext.bound [c, now]) row x)
            [Resolved.Expr.column 0, Resolved.Expr.column 1, Resolved.Expr.column 2])
        (List.filter
          (fun row =>
            Resolved.truthy
              (Resolved.Expr.eval (Resolved.EvalContext.bound [c, now]) row
                (Resolved.Expr.compare Comparison.isNot none
                  ((Resolved.Expr.compare Comparison.eq (some Affinity.integer) (Resolved.Expr.column 1)
                        (Resolved.Expr.parameter 1)).and
                    (Resolved.Expr.compare Comparison.lt (some Affinity.integer) (Resolved.Expr.column 2)
                      (Resolved.Expr.parameter 2)))
                  (Resolved.Expr.literal (Value.integer (Int.ofNat 1))))))
          (Resolved.sourceRows
            { shape := (sessions.raw.catalog.tableAt 0).get _,
              rows := db.raw.rows.getD 0 [] }))) =
    true
--- end of claim ---
case success
⊢ CompoundOperator.combine [Collation.binary, Collation.binary, Collation.binary] CompoundOperator.except
      (List.map
        (fun row =>
          List.map (fun x => Resolved.Expr.eval (Resolved.EvalContext.bound []) row x)
            [Resolved.Expr.column 0, Resolved.Expr.column 1, Resolved.Expr.column 2])
        (List.filter (fun row => true)
          (Resolved.sourceRows
            { shape := (sessions.raw.catalog.tableAt 0).get _,
              rows :=
                (Database.setRows db.raw sessionsEntry.fst
                        (LiteralData.deleted
                            (Resolved.statementContext 0
                              (env.counters.view
                                (Resolved.Statement.delete sessionsEntry.fst (some purgeFilter) []).counterReads)
                              [c, now] db.raw [])
                            { shape := sessionsEntry.snd, rows := db.raw.rows.getD sessionsEntry.fst [] }
                            (some purgeFilter)).rows).rows.getD
                  0 [] })))
      (List.map
        (fun row =>
          List.map (fun x => Resolved.Expr.eval (Resolved.EvalContext.bound []) row x)
            [Resolved.Expr.column 0, Resolved.Expr.column 1, Resolved.Expr.column 2])
        (List.filter (fun row => true)
          (Resolved.sourceRows
            { shape := (sessions.raw.catalog.tableAt 0).get _,
              rows := db.raw.rows.getD 0 [] }))) =
    []
case identical
⊢ Resolved.equalRowsIdentical [Collation.binary, Collation.binary, Collation.binary]
      (List.map
        (fun row =>
          List.map (fun x => Resolved.Expr.eval (Resolved.EvalContext.bound []) row x)
            [Resolved.Expr.column 0, Resolved.Expr.column 1, Resolved.Expr.column 2])
        (List.filter (fun row => true)
          (Resolved.sourceRows
            { shape := (sessions.raw.catalog.tableAt 0).get _,
              rows :=
                (Database.setRows db.raw sessionsEntry.fst
                        (LiteralData.deleted
                            (Resolved.statementContext 0
                              (env.counters.view
                                (Resolved.Statement.delete sessionsEntry.fst (some purgeFilter) []).counterReads)
                              [c, now] db.raw [])
                            { shape := sessionsEntry.snd, rows := db.raw.rows.getD sessionsEntry.fst [] }
                            (some purgeFilter)).rows).rows.getD
                  0 [] }))) =
    true
--- end of claim ---
```

The messages of the negative cases, verbatim (each preceded by its claim):

```text
-- SELECT 1 AS verdict WHERE NOT EXISTS (SELECT id FROM sessions)
sql_holds has no law for the names of the result columns in the query
  { sources := [], filter := some (Resolved.Expr.exists 0).not, aggregate := false, groupBy := [],
    columns := [Resolved.Output.scalar (Resolved.Expr.literal (Value.integer (Int.ofNat 1)))], names := ["verdict"],
    orderBy := [], offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE NOT EXISTS (SELECT count(*) FROM sessions)
sql_holds has no law for the result column
  Resolved.Output.aggregate Resolved.Aggregate.countRows
which is not a scalar expression. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE NOT EXISTS (SELECT id FROM sessions ORDER BY expires_at)
sql_holds has no law for ORDER BY in the query
  { sources := [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none }],
    filter := none, aggregate := false, groupBy := [], columns := [Resolved.Output.scalar (Resolved.Expr.column 0)],
    names := ["id"], orderBy := [{ key := Resolved.SortKey.expression (Resolved.Expr.column 2) }], offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE NOT EXISTS (SELECT id FROM sessions LIMIT 1)
sql_holds has no law for LIMIT in the query
  { sources := [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none }],
    filter := none, aggregate := false, groupBy := [], columns := [Resolved.Output.scalar (Resolved.Expr.column 0)],
    names := ["id"], orderBy := [], offset := 0,
    limit :=
      some
        1 }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE expires_at IN (1, 2))
sql_holds has no law for an expression of
  [(Resolved.Expr.column 2).inList
      (Resolved.Arguments.cons (Resolved.Expr.literal (Value.integer (Int.ofNat 1)))
        (Resolved.Arguments.cons (Resolved.Expr.literal (Value.integer (Int.ofNat 2))) Resolved.Arguments.nil))
      (some Affinity.integer) Collation.binary false]
that is not made of columns, literals and parameters with comparisons, AND, OR, NOT and IS NULL. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions AS a JOIN sessions AS b ON a.id = b.id)
sql_holds has no law for a FROM clause without exactly one source in
  {
    sources :=
      [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none },
        { kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0,
          condition :=
            some
              (Resolved.Expr.compare Comparison.eq (some Affinity.numeric) (Resolved.Expr.column 0)
                (Resolved.Expr.column 3)) }],
    filter := none, aggregate := false, groupBy := [],
    columns := [Resolved.Output.scalar (Resolved.Expr.literal (Value.integer (Int.ofNat 1)))], names := ["1"],
    orderBy := [], offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE (SELECT count(*) FROM sessions) = 0
sql_holds has no law for the condition
  Resolved.Expr.compare Comparison.eq none (Resolved.Expr.subquery 0)
    (Resolved.Expr.literal (Value.integer (Int.ofNat 0)))
which is not EXISTS or NOT EXISTS of a subquery. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions WHERE abs(expires_at) < 3)
sql_holds has no law for the expression
  Resolved.Expr.compare Comparison.lt none
    (Resolved.Expr.scalar Resolved.ScalarFunction.abs
      (Resolved.Arguments.cons (Resolved.Expr.column 2) Resolved.Arguments.nil))
    (Resolved.Expr.literal (Value.integer (Int.ofNat 3)))
which reads the clock or a counter, or calls a function that can fail. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT count(*) FROM sessions
sql_holds has no law for a claim without WHERE
  { sources := [{ kind := Resolved.JoinKind.inner, source := Resolved.Source.table 0, condition := none }],
    filter := none, aggregate := true, groupBy := [],
    columns := [Resolved.Output.aggregate Resolved.Aggregate.countRows], names := ["count(*)"], orderBy := [],
    offset := 0,
    limit :=
      none }. Prove this goal with the laws of the parts, for example Resolved.Query.simple_subqueryRun and Resolved.Expr.truthy_notExists.

-- SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM sessions)
sql_holds needs the catalog of the database
  context.connection.state.database
Give a hint db.HasCatalog schema or an equation of its catalog, with a schema that has no variable.

-- goal: a proposition that is not a claim
sql_holds proves the goal that sql_run leaves for a claim holds q or holdsSince start q. Use it after sql_run, on the goal of the claim.
```

Elaboration time (lower of two runs, local; the compile of the purge
test): `PurgeEffectTactic` 1.6 s (form B: `PurgeEffectClaims` 1.2 s),
`PurgeFrameTactic` 3.6 s for two claims (form B: `PurgeFrameClaims` 1.3 s
and `PurgeFrameSchema` 1.3 s), `PurgeTacticCases` 4.4 s (two claims and
eleven negative cases). With the
profiler, `sql_holds` takes 0.32 s in the effect proof and 0.64 s and
0.82 s in the two frame proofs; the negative cases take 0.23 s to 0.30 s
each. The surface modules build in 1.5 s (`SqlHoldsFacts`), 1.5 s
(`SqlHoldsRuns`) and 1.6 s (`SqlHolds`) in `just dev-build`.

Limits:

- The claim is `SELECT 1 WHERE c` with `c` an `EXISTS` or `NOT EXISTS` of
  one subquery. A claim with another top-level form, or another condition,
  stops with a message.
- A subquery is one table of the current or the initial database, without
  a join condition, with scalar columns and row-wise expressions (columns,
  literals and parameters with comparisons, AND, OR, NOT and IS NULL), and
  no aggregate, GROUP BY, ORDER BY, LIMIT, OFFSET, DISTINCT or HAVING; or an
  `EXCEPT` of two such subqueries. `IN`, `LIKE`, a function call and a
  correlated subquery stop with a message.
- The identity premise of `EXCEPT` stays as a goal, because it depends on
  the table (distinct rowids in column 0).
- `List.filter (fun row => true)` stays in the goals of a term without a
  filter: core Lean has no simp lemma for it.
- The claim of the client must be the conclusion of the main goal. The
  tactic introduces the premises of that goal.
- The result columns of the claim must have the names of `SELECT 1`. An
  alias that changes the name of the column from `1`, as in
  `SELECT 1 AS verdict`, stops with a message.
- A `holdsSince start q` claim whose query names a schema needs a catalog
  hint for the start database. A claim whose query names no schema needs
  none (`Holds.reachedSince_iff_reached`).

The tests of this form: `just dev-build`; `python3 -m pytest
tests/surface_assertion_examples_test.py -k "claim_tactic or
purge_frame_claim_over"`; `tests/surface_select_sources_test.py`,
`surface_select_rules_test.py` and `surface_select_procedure_test.py` (for
`evaluationProof?`); `tests/test_lean_categories.py`.

Nix checks: `just test-full` passed at `3c505c1d` (the later commit
`5bc3c323` changes one docstring line); `just verdict` passed at
`5bc3c323` (each corpus case AGREE or MODEL_UNSUPPORTED, no DISAGREE).

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
this file and in the task file. The record now states the two NULL
premises of the law of `NOT IN` and refers to the docstring of the law
for the others.

The sixth review (`reviews/20261125T124229Z-2dd24dc4`) had 1 "must"
finding, about the form of a hint of `sql_holds`. The owner decided on
2026-11-25 to correct it and review again. The record now refers to the
docstring of the tactic for the form of a hint.

The seventh review (`reviews/20261125T130010Z-6255b60f`) had 1 "must"
finding on the same sentence: the docstring of the tactic does not say
that the schema of a hint has no variable. The record now states this
and refers to `ClaimTactic.catalogFact` for the accepted forms. The
eighth review (`reviews/20261125T130158Z-fa16823d`) had no findings. A
review on the pull request branch (`reviews/20261125T130959Z-6ef7b1e6`)
found that the sentence did not say which catalogs the tactic needs. The
record now names the two bridge laws of the branch, whose premises give
the catalogs that the tactic needs.

## Owner decision

On 2026-11-25 the owner accepted the recommendation of the findings
record. The task file records the decision. The first plan was a pull
request from `claim-proof-pilot-tactic`. The pull request comes from the
branch `claim-proof-sql-holds`, which has the commits of that branch and
the removal of the proofs that served only the comparison; the progress
log gives the details. Pending: `just test-nix` and
`just test-scheduled-checks`, once, and then the pull request on top of
`adr-0033-phase-8-inventory`.
