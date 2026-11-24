# The exact step of a query

Created 2026-11-24. Status OPEN.

[Task](20261124-query-step-rule.task.md) ·
[ADR 0033](../docs/adr/adr-0033-exact-step-rules.md)

The query rule can use the general output equation, the frame for queries
and preparation errors, and the data functions in QueryOutputOn. Checked
the order of faults and the possible-results normalization in Output.lean.

The syntax-only send rule stays. Its caller can supply a modeled premise
on an arbitrary connection, with no validity hypothesis and no resolution.
The common bridge requires validity. Visible SELECT uses the syntax entry
point, while an abstract statement resolving to a query uses the exact rule.
The new continuation proof covers every execution and each chosen output.
The two key-check witnesses restate runScriptStep_keyCheck_resolved and
runScriptStep_keyCheck_continues. SchemaSuccess reads the foreign-key rows
in its group proof. SelectOutcomeCases uses the query equation for a
missing clock. QuerySendClaims checks the continuation and trace on a
variable connection for every modeled outcome.

Independent review requested a precise statement of the selected-output projection,
the SELECT dispatch order, a smaller tactic module, exhaustive output cases and
fixture documentation. The revision covers all five findings.

Inventory of the earlier query claims found five more single-kind laws.
ReplacedQueryOutputs checks runScriptStep_simpleTable_output,
runScriptStep_select and runScriptStep_select_returnsResult with their
original hypotheses. ReplacedPragmaOutputs covers runScriptStep_keyCheck_empty
and runScriptStep_tableKeyCheck_empty. The readiness, possible-result and
foreign-key criteria now supply the data facts. CertifiedQueryOutputs,
CertifiedQueryCommutation and DerivedColumnReads use the exact query
equation and the checks on a calm scan. The proofs in SelectExecution and
SelectContextExecution and the ForeignKeyAtoms fixture use the general
output projection and the corresponding data facts. These cover query
results, program equivalence and foreign-key observations.

The former goal-shape test in S6AutoKindRuleCases now exercises the new
choice obligation directly: it recovers each selected output together
with its membership evidence. Review clarified the six scan checks and
the proof sketch, named the new witnesses in the test, and kept the
foreign-key fixture below 200 lines.

Owner decision 4 applies D12 to query rules. ReplacedContextRules
checks the original contracts of check_query_select_at and
check_query_select_faultless. Their replacement, Sql.check_query_of_step_rows,
takes a property of the actual output. Test test_context_cases checks
the read at the reached connection (A21) and the witnessed changes()
counter (A22), including native instances. The catalog caller now derives
the output from model data. Its public interface is the next migration.

[ADR 0033, owner decision 4](../docs/adr/adr-0033-exact-step-rules.md#owner-decisions) records the scope. The A21 and A22 fixtures each audit their own proofs.

The three catalog run and check rules now use a statementOutputAt
equation on the runtime connection. The resolver can inspect a fixed
catalog while the runtime rows and counters remain variables.
SelectCatalogExecution shares the calm table scan proof with
SelectCatalogCheck. SqlSelectRules registers the new rules, and
SqlSelectEval computes the closed catalog resolution to infer a
candidate, then checks the entire output equation in the kernel.
ReplacedCatalogRules proves all three original statements.
CatalogOutputCases uses an UPDATE with RETURNING on an empty table:
it resolves to a write, and its output equals that of the empty scan.
SelectCheckCases and SelectResidualCases check the rule audit and the
diagnostic. The four surface_select suites exercise the migrated callers.

The shared model fact resolvedStepOutput_calm_scan now lives in Programs/StatementRunLaws/SelectTableOutput.lean. The fixture also checks catalog inference on a concrete database and environment.

Eleven Run contracts in SelectExecution, SelectCalmExecution and SelectOverflow
now take output equality. Callers can supply it from successful resolution to
any kind through runScriptStep_output_of_resolved. Four Replaced*Runs
fixtures prove the eleven original success, error and unmodeled statements.
The select rules, sources and automation suites cover the new premises.

The head-output projections Script.outputOn_resolved and Script.outputIn_resolved
work for all kinds. Holds, Empty, Fails and context independence now consume
the observed outputs. Both IN/EXISTS equivalence laws use equations on their
two actual steps. The old catalog lookup lemma also moved to the retention
fixture. ReplacedObservations, ReplacedRowPredicates and ReplacedSubqueryEquivalence
check the original statements. The not-blocked, assertion-context and select
automation suites exercise the callers.

The all-kinds output projection lives beside runScriptStep_output in the model. The run rules name the clock of the comparison query in their statements and explanations.

The observation bridges now document their distinct clock and index inputs and the tests name their original contracts.

### Proof and fixture files

The file stems below use the directory in their row and the extension .lean.

| Directory | Files |
| --- | --- |
| `packages/belay/Belay/Sqlite/Programs/Automation` | SqlRun, SqlRunKindRules, SqlRunModeled, SqlSelectEval |
| `packages/belay/Belay/Sqlite/Programs/Claims` | SelectOverflow |
| `packages/belay/Belay/Sqlite/Programs/Reasoning` | CertifiedQueryCommutation |
| `packages/belay/Belay/Sqlite/Programs/Scripts` | ContextObservationBridge, KindRuleSend, QueryBridge |
| `packages/belay/Belay/Sqlite/Programs/StatementRunLaws` | DerivedColumnReads, NotInQuery, SelectCatalogExecution, SelectExecution |
| `packages/belay/Belay/Sqlite/Tooling/Counterexamples` | QueryBridge, SelectCalmExecution, SelectCatalogCheck, SelectCatalogExecution, SelectContextExecution, SelectExecution, SqlSelectRules |
| `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Claims` | SelectExecutionRule |
| `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts` | QueryRule, QueryStepOutput, SchemaSuccess |
| `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws` | CertifiedQueryOutputs, ForeignKeyCheckContinues, SelectTableOutput |
| `packages/belay-sqlite-model/Belay/Sqlite/Model/Tooling/Counterexamples` | ForeignKeyCheckContinues, SelectExecutionRule |
| `packages/belay-sqlite-model/Belay/Sqlite` | Model |
| `tests/surface/Programs/Automation` | S6AutoKindRuleCases |
| `tests/surface/Programs/Claims` | SelectFunctionFaultCases, SelectPrepareErrorCases |
| `tests/surface/Programs/Scripts` | S6AutoPaths |
| `tests/surface/Programs/Tests` | AddCustomerQueries, ClaimsMayFail |
| `tests/surface/Queries/Evaluation` | SelectOneWhereSupport, SelectSumCases |
| `tests/surface/Queries/Tests` | CatalogOutputCases, QuerySendClaims, ReplacedCalmRuns, ReplacedCatalogRules, ReplacedContextRules, ReplacedFailedRuns, ReplacedKeyCheck, ReplacedObservations, ReplacedOverflowRuns, ReplacedPragmaOutputs, ReplacedQueryOutputs, ReplacedRowPredicates, ReplacedSelectRuns, ReplacedSubqueryEquivalence, S6NotBlockedLaw, SelectAutomationSchema, SelectCardinalityCases, SelectComparisonCases, SelectCompoundSupport, SelectContextCases, SelectCountCases, SelectCounterContextCases, SelectDerivedSupport, SelectDistinctCases, SelectExecutionRules, SelectExistenceCases, SelectExpressionCases, SelectExtremumCases, SelectFilterCases, SelectGroupCases, SelectHavingCases, SelectJoinSupport, SelectNullAggregateCases, SelectOrderCases, SelectOutcomeCases, SelectParameterWindowCases, SelectProjectionCases, SelectResidualCases, SelectScalarCases, SelectSourceCases, SelectSubquerySupport, SuccessBalanceObservation, SuccessBalanceSuccess |
| `tests/surface/Schema/ForeignKeys` | ForeignKeyAtoms |
| `tests/surface/Schema/Tests` | ClaimsTableInfo, CustomerInsertQueries |
| `tests/surface/Tooling/Tests` | SelectCheckCases |

The query output and context witnesses cover universal claims (S04), equivalence (S06), SQL execution and search, M06–M08 query behavior, M11 clock and counter outcomes, and M12 key-check pragmas. CatalogOutputCases supplies a lasting caller for the broadened contract. No mutant table changed.

### Measurements on the complete schema stack

The slice starts at 33c2bb37 with 98,598 selected Lean code lines. At
ea83eeff the count is 99,400. Model, surface and tests change from
59,128 / 14,321 / 21,456 to 59,216 / 14,316 / 22,175. SQL text (1,945),
conformance (1,042), public documentation tools (134) and other files (572)
are constant. The faster of two elaborations for each changed sql_run
fixture at ea83eeff, before the final catalog-proof change, was:

| Fixture | Start | End |
| --- | ---: | ---: |
| S6AutoKindRuleCases | 1.49 | 1.55 |
| S6AutoPaths | 32.36 | 51.44 |
| SelectContextCases | 8.76 | 9.15 |
| QuerySendClaims | new | 1.33 |

D11 exposed a slowdown in S6AutoPaths. Instrumenting each proof identified
query_keeps_connection. The original slice 4 proof used 8,082,223 raw Lean
heartbeats. Deciding the generalized output equality took 173,993,878 in
slice 5. Checking reflexivity first for a catalog output equality reduced
the same proof to 7,587,931. The complete fixture took 41.23 seconds at
430175e3 (faster of two). The five other successful proofs instrumented
were purge_empties_items, widen_adds_null_cells, single_keeps_connection,
sent_select_keeps_connection and second_goal_stays. Each took under a
second. The two diagnostic examples separately check an expected failure. SqlSelectEval keeps the decision proof for
an equation that reflexivity cannot establish. The focused owners are
test_sql_run_covers_every_statement_rule, test_context_cases and
test_query_rule_checks_selected_outputs_and_retains_pragma_laws.
