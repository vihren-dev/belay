# Compositional SELECT proofs: task status

Date: 2026-11-07. Status: IN PROGRESS (stage 3 of the working sequence).
Audience: the implementation team.
Task: [Compositional SELECT proofs](20261107-select-phase-rules.task.md).
Specification: [ADR 0027](../docs/adr-0027-compositional-select-proofs.md),
[acceptance contract](../docs/select-automation-acceptance.md),
[retirement inventory](../docs/select-automation-retirement.md).
Source baseline: the accepted specification on bookmark
`spec/adr-0027-compositional-select-proofs` (PR 299, `7e799755`, on main `c54d8395`).

Relevant files: `tests/surface/SelectAutomation*.lean` (experiments),
`packages/belay-sqlite-model/Belay/Sqlite/Model/QueryResults.lean`,
`Model/QueryOutputFacts.lean`, `packages/belay/Belay/Sqlite/Queries.lean`,
`Belay/Sqlite/ReadStepRule.lean`, `Belay/Sqlite/SqlRun.lean`, `Belay/Sqlite/AutoSearch.lean`.

## Progress

- 2026-11-07: task specified (review `20261106T221739Z-b9ad0060`).
- 2026-11-07: review fixes (`refactor:`): the task file states outcomes without an
  order; the working sequence and the candidate decisions are in this file;
  `ColumnQuery.lean` retires after A19.
- 2026-11-07: review fix (`refactor:`): a decision for each model example file.
- 2026-11-07: run observations of D2. `Output.returnsResult` and `Output.returnsError`
  (`Model/QueryOutputs.lean`), `Run.returnsResult`, `Run.returnsRows` and
  `Run.returnsError` (`RunResults.lean`), each decidable by a term that the kernel
  reduces. `Run.returnsError` is the "matching error observation" of D2 that `Fails`
  needs. A SELECT step that continues the run gives rows, an error or a choice of at
  least two results (`Model/SelectOutputShape.lean`); a step that ends the run gives no
  value, which no claim accepts. So the bridges to `Sql.check` (`RunResultSteps.lean`,
  `SelectResultBridge.lean`, `SelectErrorBridge.lean`) hold for raw and concrete choices
  without a vacuous empty choice. `Holds`, `Empty` and `Fails` are abbreviations of the
  observations of the default run; `QueryObservations.lean` relates them to
  `Script.outputOn`, and every caller uses `Holds.iff_of_outputOn` and its two
  siblings, with no changed statement. Migration witnesses and probes:
  `tests/surface/SelectRunObservations.lean`. Tests: `just dev-build`; locally the
  fixtures of `tests/surface_select_rules_test.py`,
  `surface_select_automation_test.py`, `surface_assertion_examples_test.py`,
  `surface_claims_test.py`, `surface_proof_cost_compat_test.py`,
  `surface_s6_automation_test.py`, `surface_success_test.py`,
  `guide_view_contract_test.py` and `surface_migration_examples_test.py`.
  Follow-up: `Output.hasRows_ofResults` and `hasNoRows_ofResults` are special cases of
  `Output.returnsResult_ofResults`.
- 2026-11-07: review fixes (`refactor:`, review `20261107T030127Z-a5cf1ccf`):
  `Syntax.Statement.select_of_asQuery` moves to the model package; the plain words of
  `Holds.iff_of_outputOn` and `Empty.iff_of_outputOn` name the error, done and
  unmodeled outputs; the SELECT shape claim names the step that continues the run.
  Tests: `just dev-build`.
- 2026-11-07: execution rule (D5). `resolvedStepOutput_query_at` gives the output of a
  query step at every clock value; `resolvedStepOutput_query` is its special case.
  `Connection.SelectReady` collects the readiness premises (known counters, source rows,
  plain nested subqueries, no possible source fault, a bound window, a run without
  mismatch, overflow or fault). Under them `resolvedStepOutput_select` and
  `runScriptStep_select` give `Output.ofResults` of `possibleResults`
  (`Model/SelectExecutionRule.lean`), and `Run.send_returnsResult_select` and
  `Run.query_returnsResult_select` the iff with "every possible result has `Q`" for every
  environment (`SelectExecution.lean`). The unready rule (`resolvedStepOutput_select_unready`,
  `Run.send_unready`) is case B05. The run rule (`Query.run_single`, `Query.run_clean_iff`,
  `SelectReady.of_phases`, `Model/SelectRunRule.lean`) splits the run into the
  `fails`, `mustFail`, `mayFail` and `distinctCertain` obligations; for a calm statement
  `SelectReady.of_calm` (`Model/SelectCalmRule.lean`) discharges `mustFail` and `mayFail`,
  and keeps no overflow (`fails`) and DISTINCT certainty as premises. The general calm
  laws (`EvalContext.bound`, `Connection.queryContext_of_calm`, `Calm.faultless_nil`) move
  from `SimpleQuerySteps.lean` to that file. The model library lists
  `SelectOutputShape`, which the run observations commit left out of `lakefile.toml`, and
  the surface imports the model root instead of two model modules. Fixture:
  `tests/surface/SelectExecutionRules.lean`. Tests: `just dev-build`; locally
  `tests/surface_select_rules_test.py`, `tests/test_model_package.py`,
  `tests/surface_layers_test.py` and the source checks.
- 2026-11-07: review fix (`refactor:`, review `20261107T031515Z-b7c6a717`): the progress
  entry of the execution rule names the obligations that `SelectReady.of_calm` discharges
  and the two that stay premises.
- 2026-11-07: result, filter and projection rules (D1); A01. Every result that the model
  permits is a permutation of a sublist of the rows of the query's records, for every
  `ORDER BY` and window (`Query.exists_sublist_of_mem_possibleResults`), with its membership,
  count and length corollaries, and a permutation of all of them without `OFFSET` and
  `LIMIT` (`Query.perm_of_mem_possibleResults`, `Model/SelectWindowRules.lean`). `WHERE` keeps
  a sublist (`filtered_sublist`), all rows without a condition; a query without aggregation,
  `DISTINCT` or compound gives `Query.rowOutput` of each kept row
  (`Query.uniqueRecords_outputs_plain`), so each result row comes from a kept source row
  (`Query.mem_possibleResults_plain`), and without a window the result is a permutation of
  all of them (`Model/SelectProjectionRules.lean`). `Run.query_returnsResult_calmTable`
  (`SelectExecution.lean`) is the calm one-table form of the execution rule. A01
  (`tests/surface/SelectProjectionCases.lean`): the motivating query with generic table and
  column premises, with `db.HasCatalog invoices`, and as a `Sql.check` claim; the empty and
  populated witnesses and the nullable contrast. Tests: `just dev-build`; locally
  `tests/surface_select_rules_test.py` and `tests/surface_layers_test.py`;
  `tests/test_model_package.py` except its installed-package test, whose Nix build of the
  changed model package exceeds the local 120 s limit.
- 2026-11-07: review fixes (`refactor:`, review `20261107T033220Z-001ee122`): the result
  rules, the execution rule and their fixtures speak of the results that the model permits,
  not of every result of SQLite, and the result rules name the group row that the model fixes
  (ADR 0027 D4); `normalForm_perm` has a proof sketch. Tests: `just dev-build`.
- 2026-11-07: expression rules (D1) and A02 to A04. The value of each expression constructor
  (`Model/ExprValueRules.lean`), its possible fault (`Model/ExprFaultRules.lean`) and its calm
  condition (`Model/ExprCalmRules.lean`, with `Arguments.Calm`); the affinity of a comparison keeps
  NULL, so `x IS NOT NULL` is true exactly when `x` is not NULL, and a true ordinary comparison has
  two non-NULL operands that satisfy the operator (`Model/ComparisonTruthRules.lean`). A comparison
  whose right operand is no `TRUE` or `FALSE` keyword resolves its two operands, also for `IS` and
  `IS NOT` (`resolveOperand_compare_of_notBoolean`); a one-column read of a table with a calm
  condition is calm (`Statement.simpleColumn_calm`); `Run.returnsResult.mono` weakens the property
  of a result. A02 (`tests/surface/SelectFilterCases.lean`): `IS NOT NULL` gives non-NULL cells for a
  nullable column, with a CHECK that accepts NULL as the contrast. A03
  (`tests/surface/SelectComparisonCases.lean`): `amount > :minimum` gives the modeled comparison for
  every parameter value, with the NULL and NaN, affinity and parameter type contrasts. A04
  (`tests/surface/SelectCardinalityCases.lean`): a plain projection is a permutation of the stored
  rows' cells, so it keeps their number and duplicates, and a filter bounds the number of rows; a
  property of each row gives no number of rows and no distinct rows. A01 uses the calm corollary.
  Tests: `just dev-build`; locally `tests/surface_select_rules_test.py`,
  `tests/surface_layers_test.py` and `tests/test_model_package.py` except its installed-package
  test.
- 2026-11-07: A11. A one-table `SELECT` of any result columns without aggregate calls resolves to
  the simple query of the table with the resolved outputs (`resolveStatement_select_table`); the
  one-column law is its corollary. The values of argument lists (`Arguments.eval_nil`,
  `Arguments.eval_cons`). A11 (`tests/surface/SelectExpressionCases.lean`): a projection of a
  column, a parameter, an arithmetic and a `CASE` expression over every database with generic
  premises gives each row from a stored row through the value rules, with a witness; the contrast
  is an `abs` call that can fail: it is not calm, its fault rule gives a fault, and its query
  returns neither a result nor an error, although its value rule gives a value. Tests:
  `just dev-build`; locally `tests/surface_select_rules_test.py`, `tests/surface_layers_test.py`
  and `tests/test_model_package.py` except its installed-package test.
- 2026-11-07: B01, B02 and B11. The prepare-error rule (`Run.query_prepareError`): a one-statement
  query that resolves to a prepare error returns no result and the error of its resolution, in
  every environment; the prepare-error output law now holds for every clock. B01, B02 and B11
  (`tests/surface/SelectOutcomeCases.lean`): a query of a missing table returns error code 1 and
  no result over every database without that table, satisfies the matching error post of
  `Sql.check` and neither another code nor a success post; a read of the clock satisfies no post
  and returns nothing over every database and environment without a clock; on a concrete choice
  of two results a post holds only when each alternative has it, the raw choice and each
  alternative keep their own traces, and an empty choice returns no result. Tests:
  `just dev-build`; locally `tests/surface_select_rules_test.py`, `tests/surface_layers_test.py`
  and `tests/test_model_package.py` except its installed-package test.
- 2026-11-07: retirement of `SelectOneFrom`. The existence and emptiness rules
  (`Query.forall_possibleResults_ne_nil_plain`, `Query.forall_possibleResults_eq_nil_plain`) and
  the equivalence of the runs of `send` and `query` for one statement
  (`Run.send_returnsResult_iff_query`, `Run.send_returnsError_iff_query`). A04 existence and
  emptiness (`tests/surface/SelectExistenceCases.lean`): `Holds`, `Empty` and not `Fails` of
  `SELECT 1 FROM invoices WHERE amount = 0` over every database, with an instance of each side;
  it takes the place of `tests/surface/ClaimsSelectOne.lean`. The guide fixtures
  `AddCustomerQueries` and `CustomerInsertQueries` prove their `Holds` claims through the phase
  rules. Deleted: `Belay/Sqlite/SelectOneFrom.lean` (131 lines), `Model/SimpleTableOutput.lean`
  (67), `tests/surface/ClaimsSelectOne.lean` (100); `SelectOneMayFail` reads the resolution of
  `resolveStatement_select_one_from` itself. The other `Simple*` laws stay for now: the count,
  duplicate-key, no-FROM, EXISTS and may-fail families of stages 2 and 3, the two-state and
  certified-output laws and the `SelectAutomation*` experiments use them. Tests:
  `just dev-build`; locally `tests/surface_select_rules_test.py`, `tests/surface_layers_test.py`,
  `tests/surface_claims_test.py`, `tests/surface_s6_automation_test.py`,
  `tests/surface_assertion_examples_test.py` and `tests/test_model_package.py` except its
  installed-package test.
- 2026-11-07: stage 1 end checks. `just verdict` passed. `just test-full` failed in the
  documentation inventory: `ComparisonTruthRules` declared the NULL laws of
  `InValueEqualsLaws` again under the same names, and the decision instances of
  `Output.returnsResult` and `Output.returnsError` had no docstring. Two `fix:` commits remove the
  duplicates and document the instances; `just test-full` runs again after them.
- 2026-11-07: decision on the stage of two families. The claims of the count and duplicate-key
  forms are subquery-wrapped (`SELECT 1 WHERE (SELECT count(*) …)`,
  `NOT EXISTS (… GROUP BY … HAVING count(*) > 1)`): their retirement needs the subquery rules
  (A18, A19) as well as the group and aggregate rules, so it moves to stage 3. Stage 2 retires
  the aggregate family (`AggregateQuery`, `AggregateQueryOutput`, `ClaimsSum`,
  `ClaimsAggregateLaws`).
- 2026-11-07: group, aggregate, HAVING, DISTINCT, order and window rules. `Model/GroupPartition.lean`
  (the fold of `groups` gives a partition: permutation, formed and apart groups);
  `Model/SelectGroupRules.lean` (`groups_partition`, `queryGroups_ungrouped`,
  `queryGroups_grouped`, `queryGroups_count`, `mem_queryGroups`, `Query.groupRow_mem`);
  `Model/SelectAggregateRules.lean` (`Query.groupRecord`, `Query.keepsGroup`,
  `records_aggregate`, `mem_records_aggregate`, `records_aggregate_length`, `records_ungrouped`,
  `records_grouped_nil`, the result-column rules); `Model/AggregateValueRules.lean` (the all-NULL
  rule of every aggregate, `count(x)` without NULL, the extremum of `min` and `max`,
  `group_concat` without NULL); `Model/SelectDistinctRules.lean` (`keepFirst_fold`,
  `sameOutput_comm`, `distinctRecords_rules`, `Query.uniqueRecords_distinct`,
  `pairwise_sameOutput_perm`); `Model/SelectOrderRules.lean` (`exists_perm_map_eq`,
  `tieGroups_eq`, `Query.exists_sorted_of_mem_possibleResults` for every window,
  `Query.exists_sorted_perm_of_mem_possibleResults` without one,
  `Query.length_of_mem_possibleResults`). Tests: `just dev-build`; locally
  `tests/test_model_package.py` except its installed-package test.
- 2026-11-07: overflow rule of execution (D5). `resolvedStepOutput_select_overflow`: a described
  one-query statement whose bound query has a failing aggregate (`Resolved.Query.fails`) and no
  certain or possible fault gives the error `integer overflow`. `Run.query_overflow_calmTable`
  (`Belay/Sqlite/SelectOverflow.lean`): a calm one-table script with such an aggregate returns no
  result and exactly the error code of the overflow, in every environment. The failing `sum`
  claims of A09 are to use it (planned; done in the A09 entry below). Tests: `just dev-build`; locally `tests/test_model_package.py` except
  its installed-package test and `tests/surface_select_rules_test.py`.
- 2026-11-07: A07 and A10 (`tests/surface/SelectGroupSupport.lean`, `SelectGroupCases.lean`,
  `SelectHavingCases.lean`). Over every database with the catalog of `orders` (customer `NOCASE`),
  `GROUP BY customer` and `GROUP BY amount > 5` with `count(*)` and `ORDER BY 2 DESC` return a
  partition of the stored rows by the key (`KeyPartition`: each row in exactly one group, the rows
  of a group with the key of its first row, the first rows of two groups with different keys), the
  key of one row of each group and its count, the larger counts first; `HAVING count(*) > 1` keeps
  exactly the groups of more than one row. The generic rules (`keyCounts_of_mem`,
  `keptCounts_of_mem`) hold for every grouping term or column. Contrasts: `'acme'` and `'ACME'`
  are one group but different values; a grouping key `abs(amount)` over the least integer leaves
  the run undescribed; `HAVING NULL` keeps no group; `HAVING customer = 'ACME' COLLATE BINARY`
  reads the model's row of the group, a model claim (issue #309: SQLite does not promise the row;
  native SQLite 3.51.0 gives the model's empty result over a full scan and over an index on
  `customer`). Resolution for the fixed catalog is
  computed by `decide +kernel`. Tests: locally `tests/surface_select_rules_test.py`.
- 2026-11-07: review fix (`refactor:`, review `20261107T051539Z-53f7a356`): the A10 model claim
  and its status entry state the native result of the exact fixture correctly.
- 2026-11-07: A08 and the count rule of A09 (`tests/surface/SelectCountCases.lean`;
  `result_ungrouped` in `SelectGroupSupport.lean`). Over every database with the catalog of
  `orders`, `SELECT count(*) FROM orders` returns one row with the number of stored rows, the row
  of 0 when there is no row; the grouped query of A07 returns no row when there is no stored row;
  `count(customer)` equals `count(*)` because `customer` is NOT NULL. Contrasts: an empty table
  still gives the row `[0]`; with a nullable `customer` and one NULL customer the result is
  `[[0, 1]]`. Native SQLite 3.51.0 gives the same results. Tests: locally
  `tests/surface_select_rules_test.py`.
- 2026-11-07: fix of the automatic check found by the stage-1 `just test-full` (in the second
  workspace; 1 failure of 382 in the surface tests,
  `tests/surface_proof_cost_automatic_test.py::test_automatic_check_gives_the_same_result_with_collection`).
  Since `Empty`, `Holds` and `Fails` are abbreviations of `Run.returnsResult` and
  `Run.returnsError`, which are conjunctions at default transparency, the proof search's
  `trivial` split `Empty one db` and executed the run of the database variable: the check of
  `Empty one db → Empty one db` used most of its budget, and with the proof-cost collector it
  gave no result. `tryProof` (`Belay/Sqlite/CheckProof.lean`) now uses `with_reducible trivial`
  for run observations, as it does for profiles. Tests: `just dev-build`; locally
  `tests/surface_proof_cost_automatic_test.py`, `surface_automatic_test.py`,
  `surface_automatic_cancel_test.py`, `surface_s6_check_editor_test.py`.
- 2026-11-07: `just test-full` on the fix of the automatic check (`npzxurlr`, second workspace):
  2 failures in the surface check tests. (1)
  `tests/surface_check_command_test.py::test_sql_check_reports_checked_outcomes`: the case
  `low-depth` (`Empty (sql "SELECT 1") db` at `sql.checkRecursionLimit 128`) gave "false" with the
  empty database, not "unknown". Before the fix, `trivial` executed the run of the database variable
  and stopped at the recursion limit; now the proof attempt stops at once and the candidate search
  finds the counterexample, which is correct. The case now uses the limit 16, well below the depth
  that the evaluation of the candidate needs, so that the search stops at the limit again. (2)
  `tests/surface_check_consumer_size_test.py::test_consumer_size_claim_is_false_and_replays`
  reached the search time limit while a dev-build ran on the same machine. The next
  `just test-full` checks both.
- 2026-11-07: A09 and the retirement of the aggregate family. `tests/surface/SelectSumCases.lean`:
  over every database whose catalog has a table `ledger` with a column `cents`,
  `SELECT sum(cents) FROM ledger` returns the one row of the sum when the sum does not fail, and
  otherwise no result and exactly the error code of `integer overflow`
  (`Run.query_overflow_calmTable`); `Fails` holds exactly when the sum fails, `Holds` exactly when
  it does not, and `Empty` never. `SelectSumInstances.lean` keeps the kernel instances and the
  `sql_simp` and `grind` laws of `ClaimsSum` and `ClaimsAggregateLaws`.
  `SelectExtremumCases.lean`: over every database with the catalog of `orders`, `min(amount)` is
  NULL exactly when there is no row, else the amount of a row and at most every amount under
  `BINARY`; `group_concat(customer)` joins the customers of the scan with commas; contrast: the
  row of a grouped `min` is its deciding row (`ACME|5`, `zeta|7` on `mixed`).
  `SelectNullAggregateCases.lean`: over no row, `min`, `max`, `sum`, `avg` and `group_concat` are
  NULL and `total` is 0.0; over only NULL customers (catalog of `nullable`) `count(customer)` is 0
  and `count(*)` counts the rows. Native SQLite 3.51.0 gives the same results for each query.
  `SuccessBalanceSuccess.balance_of_bounds` now proves its `Holds` claim through
  `resolveStatement_select_aggregate` and `Run.query_returnsResult_calmTable`.
  `Resolved.Statement.Calm.aggregateOf_first` moves to `Model/AggregateSelectResolution.lean`.
  Deleted: `Belay/Sqlite/AggregateQuery.lean` (86 lines), `Model/AggregateQueryOutput.lean` (62),
  `tests/surface/ClaimsSum.lean` (143), `tests/surface/ClaimsAggregateLaws.lean` (57), and from
  `Model/AggregateQueryLaws.lean` the laws that only the deleted output file used
  (`aggregateOf_results`, `aggregateOf_bindWindow`, `aggregateOf_run_of_faultless`, 41 lines).
  The rest of `AggregateQueryLaws` stays for the sum fixture and for `ClaimsQueryCases`. Tests:
  `just dev-build`; locally `tests/surface_select_rules_test.py`, `tests/surface_claims_test.py`
  and `tests/surface_success_test.py -k balance`.
- 2026-11-07: A12, A13 and A14 (`tests/surface/SelectDistinctCases.lean`,
  `SelectOrderCases.lean`; `cell` moves to `SelectGroupSupport.lean`). A12: over every database with
  the catalog of `orders` whose customers that compare equal under `NOCASE` are the same values,
  `SELECT DISTINCT customer FROM orders` returns a result with no two rows equal under `NOCASE`,
  each row the customer of a stored row, and the customer of each stored row; contrast: with
  `'acme'` and `'ACME'` (on `mixed` and with the rows in the other order) the model describes no
  result, since the kept spelling depends on the read order (native SQLite 3.51.0 keeps `acme` and
  `ACME`). A13: `SELECT id FROM orders ORDER BY amount DESC` returns the ids of a permutation of the
  stored rows whose amounts decrease under `BINARY`; the sort key is no result column. A14:
  `SELECT id FROM orders ORDER BY amount LIMIT 2 OFFSET 1` returns `min 2 (n - 1)` rows for `n`
  stored rows, the ids of a permutation of a sublist of the rows with increasing amounts; instances
  for `LIMIT 0`, `LIMIT 1`, many rows and an offset past the end; contrast: with two equal smallest
  amounts the model permits either id for `LIMIT 1` and claims neither alone (native SQLite gives
  id 1 with a full scan and id 2 with an index on `(amount, id DESC)`). Native SQLite 3.51.0 gives
  the instance results. Tests: locally `tests/surface_select_rules_test.py`.
- 2026-11-07: stage 2 end checks. `just verdict` did not run: `just test-full` stopped in
  `test-source` because `docs/spec-proof-query-observation-targets.md` linked the two deleted
  aggregate files (`tests/docs_test.py::test_local_markdown_links`). A `fix:` commit names them
  without links; the checks run again.
- 2026-11-07: join rules and A05, A06 (stage 3). `Model/SelectJoinRules.lean`: the complete rows
  of each join kind as a collection with order and multiplicity (`joinRows_inner`,
  `joinRows_left`, `joinRows_right`, `joinRows_full` over `matchedRows`, `paddedRows` and
  `unmatchedRows`), the cardinality rule (`joinRows_inner_length`) with its unique-match form, and
  the two-table source rule (`Query.source_two_tables`). `Run.query_returnsResult_calm`
  (`SelectExecution.lean`) is the calm execution rule for any source rows;
  `Run.query_returnsResult_calmTable` is now its one-table case. Fixtures
  `tests/surface/SelectJoinSupport.lean`, `SelectJoinCases.lean`, `SelectOuterJoinCases.lean` over
  the catalog of `shop` (`customers`, and `orders` with a nullable `customer_id`): A05, the inner join
  is a permutation of each order with each matching customer, with as many rows as orders when each
  order has one match; A06, the left join keeps each order (NULL name without a match), the right
  join adds each customer without a matching order (NULL id), and the full join both. Contrasts: an
  order with a missing customer is removed, an order with two matches (`c.id <= o.customer_id`)
  gives two rows, and the left join returns a NULL name although `customers.name` is NOT NULL.
  Native SQLite 3.51.0 gives the same rows. Tests: `just dev-build`; locally
  `tests/surface_select_rules_test.py`, `tests/surface_success_test.py` and
  `tests/test_model_package.py` except its installed-package test.
- 2026-11-07: stage 2 end checks, run again at `824f18e6` (the join commit, on the `fix:`
  commit): `just test-full` passed and `just verdict` passed (5768 cases agree, 2100 are
  unsupported by the model, no disagreement).
- 2026-11-07: window parameters and subquery rules, A15, A18 and A19 (stage 3).
  `Model/SelectSubqueryRules.lean`: the statement context runs each subquery in the subquery
  context of the values at depth `subqueries.length - 1` (`EvalContext.statement_subqueries`), and
  in the context of the values alone when the statement has one subquery (`statement_one`); the run of a subquery without a
  fault (`Query.subqueryRun_clean`, `subqueryRun_of_faultless`), the emptiness rule that `EXISTS`
  reads (`results_eq_nil_iff_plain`), the rows of a plain query without `ORDER BY`
  (`results_plain_unordered`) and the short window rule (`windowCertain_of_short`).
  `Connection.SelectReady.of_faultless` (`SelectCalmRule.lean`) and
  `Run.query_returnsResult_faultless` (`SelectCalmExecution.lean`, moved out of
  `SelectExecution.lean`) take a window that binds to the values; the mismatch rules
  `resolvedStepOutput_select_mismatch` and `Run.query_mismatch` give the error `datatype mismatch`
  when it does not bind. `stableSort_of_total` moves to `SelectWindowRules.lean`. Fixtures: A15,
  `SelectParameterWindowCases.lean`: `LIMIT ? OFFSET ?` with integer values returns `min limit
  (n - offset)` ids in increasing amount order, and a `LIMIT` value that is no integer returns the
  error and no result; instances: the text values `'+2'` and `' 1 '` read as integers, `OFFSET
  'abc'` after `LIMIT 2` fails, `LIMIT 0` with `OFFSET NULL` gives no row. A18,
  `SelectSubquerySupport.lean` and `SelectExistsCases.lean`: correlated `EXISTS` and `NOT EXISTS`
  keep the customers with and without a witness order; contrast with two outer rows. A19,
  `SelectInCases.lean`: `IN` and `NOT IN` over the `customer_id` of every order, with the NULL rule
  of `inValue` (`2 NOT IN (1, 9, NULL)` is NULL); `SelectScalarCases.lean`: the scalar subquery
  gives the amount of the first witness order, or NULL without one, when at most one order is a
  witness. Native SQLite 3.51.0 gives the instance results. Tests: `just dev-build`; locally
  `tests/surface_select_rules_test.py`.
- 2026-11-07: compound and derived-source rules, A16 and A17 (stage 3).
  `Model/SelectCompoundRules.lean`: the end of a compound whose terms end
  (`Compound.ending_done`) and the rows of `UNION ALL` (`Compound.rows_unionAll`).
  `Model/SelectCompoundMembership.lean`: the membership rules of `UNION`, `INTERSECT` and `EXCEPT`
  (`mem_union_combine`, `mem_intersect_combine`, `mem_except_combine`) when equal rows are the same
  values, and their rows without duplicates. `Model/SelectCompoundReady.lean`:
  `Connection.SelectReady.of_compound`; `Run.query_returnsResult_compound`
  (`SelectCalmExecution.lean`). `Model/SelectDerivedRules.lean`: the source of a derived table, a
  CTE or a view that is one subquery (`Query.source_derived`), no source when the subquery is
  uncertain (`source_derived_uncertain`), and the window rule without a window
  (`windowCertain_unwindowed`). Fixtures: A16, `SelectCompoundSupport.lean` and
  `SelectCompoundCases.lean`: the ids of `customers` and the `customer_id` of `orders` under the four
  operators, with the multiplicity of `UNION ALL` and the members of the other three; A17,
  `SelectDerivedSupport.lean` and `SelectDerivedCases.lean`: a derived table, a CTE and a view of the
  orders with an amount above 5 give the same `customer_id` rows; contrast on `partial_`: the NULL
  of an outer join comes through a derived table, and the model describes no result for a derived
  table with `LIMIT` and no `ORDER BY`. Native SQLite 3.51.0 gives the instance results. Tests:
  `just dev-build`; locally `tests/surface_select_rules_test.py`.
- 2026-11-07: source rules of a query without a table, A20 (stage 3).
  `Model/SelectSourceRules.lean`: the rows of a pragma that is the only source
  (`Query.source_pragma`, for every pragma whose rows the model gives), the rows of a `json_each`
  call that is the only source (`Query.source_each`), and the fault `may` of a call that fails
  (`Query.source_each_fault`); `Query.source_none` gives the one row with no cells. Fixture
  `SelectSourceCases.lean`: `SELECT 1 + 2` returns the one row 3 over every database;
  `SELECT name FROM pragma_table_info('customers')` and `SELECT value FROM json_each(?)` return the
  names and the JSON values over every database with the catalog of `shop`;
  `SELECT key FROM json_each('[1')` returns no result and no error (native SQLite gives
  `malformed JSON`). Instances: `SELECT count(*)` gives 1 and `count(*)` over the empty `orders`
  gives 0; `PRAGMA table_info(customers)` gives one row of six cells for each column. Native SQLite 3.51.0 gives the
  instance results. Tests: `just dev-build`; locally `tests/surface_select_rules_test.py`.
- 2026-11-07: the tests of the join, subquery, compound, derived, source and window-parameter
  cases (A05, A06, A15 to A20) move from `tests/surface_select_rules_test.py` to
  `tests/surface_select_sources_test.py`, a module of the Nix surface suite, so that each file
  stays under 200 lines. Later stage-3 cases add their tests there. Tests: locally both modules,
  `tests/test_test_ownership.py`, `tests/test_nix_test_targets.py`.
- 2026-11-07: context rules of a SELECT, A21 and A22 (stage 3). `SelectContextExecution.lean`:
  a SELECT at any context, with the readiness premises at that context (`check_query_select_at`),
  and its calm form over the database of the context (`check_query_select_faultless`); both give
  that the reached context keeps the connection. `SendStepRules.lean`: a write that keeps the
  catalog keeps the resolution state (`Connection.resolveState_afterWrite`). Fixture
  `SelectContextCases.lean`: A21, `SELECT customer_id, amount FROM orders WHERE amount > 5` at every
  context with the resolution state of `shop` returns the rows of the database of that context,
  after any program that reaches such contexts, and after `DELETE FROM orders WHERE customer_id IS
  NULL` (the delete step's coverage stays a premise); A22, `SELECT changes()` at every context whose
  counters know `changes()` returns that value. Instances: on `partial_` the result from the start
  does not hold after the delete; `changes()` has no result with `Env.default`, gives 0 with
  `Env.newConnection` and 1 after the delete. Native SQLite 3.51.0 gives the instance results. Tests:
  `just dev-build`; locally `tests/surface_select_sources_test.py`.
- 2026-11-07: refactor after the review of A21 and A22 (R6, must): `Connection.afterWrite` and
  `Connection.resolveState_afterWrite` move from `SendStepRules.lean` to the model file
  `Model/Connection.lean`, beside `Connection.resolveState`. Tests: `just dev-build`.
- 2026-11-07: retirement of the table-info family (stage 3). `TableInfoQuery.lean` and
  `Model/TableInfoOutput.lean` are deleted. `ClaimsTableInfo.lean` proves its claims through the
  pragma source rule (`Resolved.Query.source_pragma`) and `Run.query_returnsResult_calm`
  (`tableInfo_results`); the claim about a stored column now takes a script of one statement.
  `Resolved.Statement.Calm.selectOne_pragma` moves to `SelectSourceRules.lean`, and
  `SuccessBalanceSubqueries.lean` uses `Resolved.Query.source_pragma` in place of
  `source_pragma_fixed`. Tests: `just dev-build`; locally `tests/surface_claims_test.py` and the
  success-balance tests.
- 2026-11-07: retirement of model examples (stage 3). `Model/SubqueryExamples.lean` is deleted:
  the contrasts of A18 and A19 replace its EXISTS, IN and scalar-subquery examples.
  `Model/PossibleResultsExamples.lean` keeps only its two `Resolved.normalForm` examples; A12 and
  A14 replace the `possible` examples. The query examples of `Model/QueryWindowExamples.lean` go
  with `ClaimsQueryCases.lean`, which still uses them. Tests: `just dev-build`.

## Working sequence

Each stage ends with the checks of a slice end (`just test-full`, `just verdict`).

1. Execution rule, `Run.returnsResult`, `Run.returnsRows` and `Run.returnsError` with
   their bridges, the `Holds`/`Empty`/`Fails` abbreviations; projection, filter and
   expression rules; A01 to A04, A11, B01, B02, B05, B11; retirement of
   `SelectOneFrom`, the `Simple*` laws and the outputs that only these cases cover.
2. Group, aggregate, HAVING, DISTINCT, order and window rules, and the overflow rule of
   execution; A07 to A10, A12 to A14; retirement of the aggregate family.
3. Source, join, compound, subquery and context rules; A05, A06, A15 to A22;
   retirement of the count and duplicate-key families (see the decision of 2026-11-07),
   `ColumnQuery`, `UniqueLookupQuery`, the EXISTS, no-FROM, may-fail, query-case and
   hint families.
4. `sql_select`, `sql_select_rule`, the `sql_run` delegation and the `sql_auto`
   route; automatic closure of the core set; B03, B04, B06 to B10; the end-to-end
   theorems; deletion of the experiments and migration witnesses; the measurement.

## Candidate decisions (at assignment, 2026-11-07)

- `TableInfoQuery.lean` and `Model/TableInfoOutput.lean`: delete. The only consumer of
  `Script.outputOn_tableInfo` is `tests/surface/ClaimsTableInfo.lean`, which moves to
  the pragma source rule of A20. `Resolved.Query.source_pragma_fixed`, a general
  source law used by `tests/surface/SuccessBalanceSubqueries.lean`, moves to the
  source rules first.
- `InSubquery*` (eight model files): retain. `NotInQuery.lean` (ADR 0026 D4) uses
  `resolvedStepOutput_in_eq_exists_of_rowidAlias` and
  `resolvedStepOutput_notIn_eq_notExists_of_rowidAlias` of
  `InSubqueryQueryRowidAlias`, whose import chain contains the other seven files.
  A declaration of the chain that this consumer does not use is deleted when the
  `subquery` rule exists.
- `Model/QueryExamples.lean`: retain. The conformance package
  (`VerifierConformance/QueryOutputs.lean`) and the other example files import it.
- `Model/SubqueryExamples.lean`: delete. Its correlated EXISTS, IN-with-NULL and
  scalar-subquery examples are the contrasts of A18 and A19, which replace them.
- `Model/QueryWindowExamples.lean`: delete the examples of the queries `windowed` and
  `empty` (parameter LIMIT/OFFSET results and the mismatch error); A15 replaces them.
  Retain the `windowInteger` conversion examples (integer, real, text, blob and NULL
  values of a window parameter): no acceptance case covers that conversion table.
- `Model/PossibleResultsExamples.lean`: delete the `possible` examples (window ties,
  DISTINCT and LIMIT over the guide's tables); A12 and A14 replace them. Retain the two
  `Resolved.normalForm` examples (NaN against NULL, and real 1.0 against integer 1):
  no case covers the order of output normalization.
- `Model/InSubqueryExamples.lean`: retain. Its NOT IN against NOT EXISTS examples
  (NULL, empty subquery and collation) protect the equivalence of `NotInQuery.lean`
  (ADR 0026 D4), which no ADR 27 case covers; A19 covers one IN observation, not the
  equivalence.
