# Query and observation change targets

Date: 2026-10-27. Revised: 2026-10-28. Status: D1 and D4 implementation in progress.
Audience: designers and reviewers.
Contract: [query and observation specification](spec-proof-observations.md),
implementing [ADR 0026 D1 and D4](adr-0026-semantic-proof-boundaries.md).
This inventory records the pre-refactor targets. Source-reviewed baseline:
main `3e2212ed6983`. Historical compiled experiments use
`3fe5caef`; this inventory makes no current-main compile claim. Counts are authored declarations, not net savings.

Model namespace: `Belay.Sqlite.Model`; surface namespace: `Belay.Sqlite`.
A prefix plus each listed suffix names one declaration; these are finite deletion lists.

## Replace 21 model observation endpoints

Replace these with semantic output facts usable under arbitrary predicates.
Their current formulas and assumptions remain migration obligations.

| Owning source | Exact name prefix | Exact suffixes to replace |
| --- | --- | --- |
| [AggregateQueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/AggregateQueryOutput.lean) | `resolvedStepOutput_aggregateTable_` | `hasRows`, `not_hasNoRows`, `isError` |
| [ScalarSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/ScalarSubqueryOutput.lean) | `resolvedStepOutput_scalar_` | `hasRows`, `hasNoRows`, `not_isError` |
| [CountSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/CountSubqueryOutput.lean) | `resolvedStepOutput_count_` | `hasRows`, `hasNoRows`, `not_isError` |
| [ExistsSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/ExistsSubqueryOutput.lean) | `resolvedStepOutput_exists_` | `hasRows`, `hasNoRows`, `not_isError` |
| [NotExistsSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/NotExistsSubqueryOutput.lean) | `resolvedStepOutput_notExists_` | `hasRows`, `hasNoRows`, `not_isError` |
| [DuplicateKeyOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/DuplicateKeyOutput.lean) | `resolvedStepOutput_notExists_duplicateKeys_` | `hasRows`, `hasNoRows`, `not_isError` |
| [TableInfoOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/TableInfoOutput.lean) | `resolvedStepOutput_simplePragma_` | `hasRows`, `hasNoRows`, `not_isError` |

The three `DuplicateKeyOutput` names now quantify over a filter, result column
and column name. They describe groups of `Resolved.keptRows`, not all source rows.

## Replace 24 surface observation endpoints

Preserve each resolver-only transport with its weaker premises; 45 includes three filtered targets added since the historical 42.

| Owning source | Exact declarations to replace | Resolver transport to retain |
| --- | --- | --- |
| [AggregateQuery](../packages/belay/Belay/Sqlite/AggregateQuery.lean) | `Holds.iff_selectAggregate`, `Empty.not_selectAggregate`, `Fails.iff_selectAggregate` | `Script.outputOn_selectAggregate` |
| [ColumnQuery](../packages/belay/Belay/Sqlite/ColumnQuery.lean) | `Holds.iff_selectOne_column`, `Empty.iff_selectOne_column`, `Fails.not_selectOne_column` | `Script.outputOn_selectOne_column` |
| [CountQuery](../packages/belay/Belay/Sqlite/CountQuery.lean) | `Holds.iff_selectOne_count`, `Empty.iff_selectOne_count`, `Fails.not_selectOne_count` | `Script.outputOn_selectOne_count` |
| [ExistsQuery](../packages/belay/Belay/Sqlite/ExistsQuery.lean) | `Holds.iff_selectOne_exists`, `Empty.iff_selectOne_exists`, `Fails.not_selectOne_exists` | `Script.outputOn_selectOne_exists` |
| [NotExistsQuery](../packages/belay/Belay/Sqlite/NotExistsQuery.lean) | `Holds.iff_selectOne_notExists`, `Empty.iff_selectOne_notExists`, `Fails.not_selectOne_notExists` | `Script.outputOn_selectOne_notExists` |
| [DuplicateKeyQuery](../packages/belay/Belay/Sqlite/DuplicateKeyQuery.lean) | `Holds.iff_selectOne_noDuplicateKeys`, `Empty.iff_selectOne_noDuplicateKeys`, `Fails.not_selectOne_noDuplicateKeys` | `Script.outputOn_selectOne_noDuplicateKeys` |
| [FilteredDuplicateKeyQuery](../packages/belay/Belay/Sqlite/FilteredDuplicateKeyQuery.lean) | `Holds.iff_selectOne_noDuplicateKeysWhere` | `Script.outputOn_selectOne_noDuplicateKeysWhere` |
| [FilteredDuplicateKeyEmpty](../packages/belay/Belay/Sqlite/FilteredDuplicateKeyEmpty.lean) | `Empty.iff_selectOne_noDuplicateKeysWhere`, `Fails.not_selectOne_noDuplicateKeysWhere` | Uses the filtered transport above |
| [TableInfoQuery](../packages/belay/Belay/Sqlite/TableInfoQuery.lean) | `Holds.iff_selectOne_tableInfo`, `Empty.iff_selectOne_tableInfo`, `Fails.not_selectOne_tableInfo` | `Script.outputOn_selectOne_tableInfo` |

Retain and migrate `Holds.iff_selectOne_noDuplicateKeys_pairwise` and
`Empty.iff_selectOne_noDuplicateKeys_repeated` in `DuplicateKeyQuery`, and
`Holds.selectOne_count_unique_lookup` in
[UniqueLookupQuery](../packages/belay/Belay/Sqlite/UniqueLookupQuery.lean).
Also retain the mathematical consequence `Holds.iff_selectOne_noDuplicateKeysWhere_pairwise` in
`FilteredDuplicateKeyQuery`. Preserve result-column resolution/groupedness,
aggregate-feed restrictions, `GroupTermResolvesIn`, filter/column/key calmness,
and NULL grouping. False/NULL filters exclude rows; fallible filters are outside
the calm contract. The filtered resolver transport itself needs no calmness.

## Preserve semantic helpers and move shared ownership where needed

Keep used helpers outside the 45-name list; mixed owners are not wholesale deletion targets.

| Current owner | Exact definitions and facts to reuse below their consumers |
| --- | --- |
| [QueryStatementOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/QueryStatementOutput.lean) | `Resolved.Query.described`, `Connection.queryContext`, `resolvedStepOutput_query`, `Connection.runOn_of_found` |
| [SimpleQuerySteps](../packages/belay-sqlite-model/Belay/Sqlite/Model/SimpleQuerySteps.lean) | `Resolved.EvalContext.bound`, `Resolved.EvalContext.bound_parameters`, `Connection.queryContext_of_calm`, `Resolved.Statement.Calm.faultless_nil` |
| [SelectOneSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/SelectOneSubqueryOutput.lean) | `Resolved.SubqueryRun.Quiet`, `Connection.queryContext_eq_bound`, `Connection.queryContext_selectOne` |
| [CountSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/CountSubqueryOutput.lean) | `Resolved.SubqueryRun.count`, `Resolved.SubqueryRun.count_quiet`, `Resolved.countMatching`, `Connection.queryContext_countSubquery_zero`, `Connection.queryContext_countSubquery_runs` |
| [ScalarSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/ScalarSubqueryOutput.lean) | `Resolved.SubqueryRun.certain`, `Resolved.SubqueryRun.certain_quiet`, `Resolved.scalarRows`, `Connection.queryContext_scalarSubquery_zero`, `Connection.queryContext_scalarSubquery_runs` |
| [ExistsSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/ExistsSubqueryOutput.lean) | `Resolved.EvalContext.bound_quiet`, `Connection.queryContext_subquery_zero`, `Connection.queryContext_tableSubquery_zero` |
| [DuplicateKeyOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/DuplicateKeyOutput.lean) | `Connection.queryContext_duplicateKeys_zero` |
| [TableInfoOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/TableInfoOutput.lean) | `Resolved.Query.source_pragma_fixed` |
| [SimpleSubqueryRowsOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/SimpleSubqueryRowsOutput.lean) | `resolvedStepOutput_simple_rows_of_faultless`; reuse this current exact-output fact |
| [CertifiedQueryOutputs](../packages/belay-sqlite-model/Belay/Sqlite/Model/CertifiedQueryOutputs.lean) | `runScriptStep_simpleTable_output`, `runScriptStep_simpleTable_output_agree`, `runScriptStep_simpleTable_output_append`; reuse different-filter agreement and named-table append semantics |
| [SimpleTableCalm](../packages/belay-sqlite-model/Belay/Sqlite/Model/SimpleTableCalm.lean) | `Resolved.Output.operands_of_readsBelow`, `Resolved.Statement.simpleTable_calm`; reuse the current shared calmness proof |

The existing generic projections `resolvedStepOutput_query_isError` in
`QueryStatementOutput` and `resolvedStepOutput_simple_not_isError_of_faultless`
in `SimpleQuerySteps` identify important independent guarantees: the former
needs no bound-window premise; the latter needs no clean-source premise.
They are outside the 45-endpoint deletion set. Preserve these strengths when
reusing clean-source exact-output facts; generic projections are not automatically obsolete.

Preserve support gating, mismatch/overflow/function-error precedence, unmodeled
results and every `Output.ofResults` alternative. Aggregate empty input can
produce one row. Preserve resolver scope, parameter, table and calmness premises.

## Replace four relation representations and nine structural wrappers

The four `Prop` structures become profile equality: actual observation plus the
predicate of possible observations. Preserve each `actual`/`branches` meaning.

| Owning source | Exact relation targets | Observer retained |
| --- | --- | --- |
| [ExecutionEquivalence](../packages/belay/Belay/Sqlite/ExecutionEquivalence.lean) | `Sql.EquivAt` | Complete `SqlRun`, including connection and trace |
| [ExecutionObservations](../packages/belay/Belay/Sqlite/ExecutionObservations.lean) | `Sql.ObservationEquivAt` | `SqlRun.observation` |
| [ExecutionViewEquivalence](../packages/belay/Belay/Sqlite/ExecutionViewEquivalence.lean) | `Sql.View.EquivAt`, `Sql.View.ObservationEquivAt` | `Sql.View.fullObservation`, `Sql.View.observation`, respectively |

Remove these nine fixed-context wrappers; ordinary equality supplies their laws:

| Owning source | Exact prefix | Exact suffixes |
| --- | --- | --- |
| [ExecutionEquivalenceLaws](../packages/belay/Belay/Sqlite/ExecutionEquivalenceLaws.lean) | `Sql.EquivAt.` | `refl`, `symm`, `trans` |
| [ExecutionViewEquivalenceLaws](../packages/belay/Belay/Sqlite/ExecutionViewEquivalenceLaws.lean) | `Sql.View.EquivAt.` | `refl`, `symm`, `trans` |
| [ExecutionViewEquivalenceLaws](../packages/belay/Belay/Sqlite/ExecutionViewEquivalenceLaws.lean) | `Sql.View.ObservationEquivAt.` | `refl`, `symm`, `trans` |

`Sql.EquivOn`, `Sql.Equiv`, `Sql.ReturnsIn` in `ExecutionEquivalence` and
`Sql.View.ObservationEquivOn`, `Sql.View.EquivOn`, `Sql.View.ObservationEquiv`,
`Sql.View.Equiv` in `ExecutionViewEquivalence` remain meaningful domain APIs.
Migrate `Sql.Equiv.refl`, `Sql.Equiv.symm`, `Sql.Equiv.trans` and `sqlSetoid` in
`ExecutionEquivalenceLaws` to the new representation; they are not part of the
nine fixed-context removals. Preserve the existing `≈` notation and its meaning.
Current [ExecutionBranches](../packages/belay/Belay/Sqlite/ExecutionBranches.lean)
selects a `RunStep.executions` member before `OutputChoice`: preserve each
member's next connection. `Sql.hasOneBranch` also requires `others.isEmpty`;
absence of `.oneOf` alone no longer establishes a singleton execution.
In [MigrationPatternAfter](../packages/belay/Belay/Sqlite/MigrationPatternAfter.lean),
`Migration.afterView_observation_actual`, `Migration.afterView_observation_branches`
and `Migration.translatesAt_of_observations` preserve the actual result separately
from the union over all migration end states and their shifted raw indexes.

## Share transport and singleton reasoning; retain semantic boundaries

| Owning source | Exact claims whose proof reasoning is consolidated |
| --- | --- |
| [ExecutionObservations](../packages/belay/Belay/Sqlite/ExecutionObservations.lean) | `Sql.EquivAt.observation` |
| [ExecutionViewEquivalenceLaws](../packages/belay/Belay/Sqlite/ExecutionViewEquivalenceLaws.lean) | `Sql.View.EquivAt.observation` |
| [ExecutionViewFrames](../packages/belay/Belay/Sqlite/ExecutionViewFrames.lean) | `Sql.View.EquivAt.with_outputs`, `Sql.View.ObservationEquivAt.full_of_frames` |
| [ExecutionDeterministic](../packages/belay/Belay/Sqlite/ExecutionDeterministic.lean) | `Sql.EquivAt.of_one_branch`, `Sql.View.EquivAt.of_one_branch`, `Sql.View.ObservationEquivAt.of_one_branch` |

Derive these claims through common branch transport or singleton reasoning;
delete duplicate implementations after caller migration. Keep `Sql.branch_iff_actual` and `Sql.hasOneBranch` as the facts
that supply singleton premises. Keep the full-to-weak projection fact
`Sql.View.observation_eq_of_full` and the frame characterization
`Sql.View.fullObservation_eq_iff` in their listed owners, or suitable lower owners.
Migrate `Sql.View.identity_observation_iff`, `Sql.View.identity_full_eq_iff` and
`Sql.View.identity_equiv_iff` in
[ExecutionViewIdentity](../packages/belay/Belay/Sqlite/ExecutionViewIdentity.lean).

Observers in [ExecutionViewProjection](../packages/belay/Belay/Sqlite/ExecutionViewProjection.lean)
keep full connection/raw index distinct from weak observations and actual runs
distinct from possible images. [ScopedAgreement](../packages/belay/Belay/Sqlite/ScopedAgreement.lean)
owns `RunsAgree` and `Sql.ScopedAt`; retain their relation-based meaning and
`Sql.ScopedAt.of_one_branch` independently of profile equality.

## Retain NOT IN and correlated EXISTS equivalences

[NotInQuery](../packages/belay/Belay/Sqlite/NotInQuery.lean) adds meaningful consumers:
`Sql.EquivAt.notIn_notExists_of_rowidAlias`, `Sql.EquivAt.in_exists_of_rowidAlias`
and the singleton bridge `Sql.EquivAt.of_select_steps`. Retain `IsSelectStatement`
and `IsSelectStatement.step_of_rows`: SELECT rows imply no further execution.
Both equivalences require table presence, key bounds, outer rowid alias and
`RowsAliased`, non-TEXT affinity, matching resolution and output columns; their
collations are independent. Only NOT IN requires non-NULL inner cells. Reuse
`resolvedStepOutput_notIn_eq_notExists_of_rowidAlias` and
`resolvedStepOutput_in_eq_exists_of_rowidAlias` in
[InSubqueryQueryRowidAlias](../packages/belay-sqlite-model/Belay/Sqlite/Model/InSubqueryQueryRowidAlias.lean).

## Migrate actual clients and existing tests

| Source | Required migration or retained coverage |
| --- | --- |
| [ExecutionEquivalenceLaws](../packages/belay/Belay/Sqlite/ExecutionEquivalenceLaws.lean) | `Sql.EquivAt.check_iff`, `Sql.EquivAt.andOk_iff`, `Sql.EquivAt.ifOk_iff`, `Sql.Equiv.transformer`, `Sql.Equiv.fresh_iff`, `Sql.Equiv.succeeds_iff` retain their guarantees |
| [ExecutionEquivalenceBind](../packages/belay/Belay/Sqlite/ExecutionEquivalenceBind.lean) | `Sql.EquivOn.bind`, `Sql.Equiv.bind`, `Sql.Equiv.bind_right`, `Sql.Equiv.bind_left`, `Sql.Equiv.map`, `send_append_equiv` |
| [ExecutionViewBindFrames](../packages/belay/Belay/Sqlite/ExecutionViewBindFrames.lean), [ExecutionViewEquivalenceBind](../packages/belay/Belay/Sqlite/ExecutionViewEquivalenceBind.lean) | `Sql.View.EquivAt.bind_branch`, `Sql.View.EquivOn.bind`, `Sql.View.Equiv.bind` |
| [ExecutionViewObservationBind](../packages/belay/Belay/Sqlite/ExecutionViewObservationBind.lean) | `Sql.View.observation_bind_return_eq`, `Sql.View.observation_bind_branch`, `Sql.View.ObservationEquivOn.bind_same` |
| [CounterexampleActual](../packages/belay/Belay/Sqlite/CounterexampleActual.lean), [CheckProof](../packages/belay/Belay/Sqlite/CheckProof.lean) | Migrate `refuteByActualRun?` from relation-field projection to profile equality; remove the quoted `Sql.EquivAt.refl` tactic alternative and retain ordinary reflexivity and proof certification. |
| [MigrationPatternFrames](../packages/belay/Belay/Sqlite/MigrationPatternFrames.lean) | `TranslatesAt.commutes_of_frames`, `TranslatesOn.commutes_of_frames`; retain connection/step frames |
| [ReadCertificate](../packages/belay/Belay/Sqlite/ReadCertificate.lean), [ReadCertificatePreservation](../packages/belay/Belay/Sqlite/ReadCertificatePreservation.lean) | Retain `ReadCertificate.moved`, `ReadCertificate.Valid.moved`, `ReadCertificate.Obligations`, `ReadCertificate.output_eq`, `ReadCertificate.preservesAt`, `ReadCertificate.preservesAt_send`: named tables can move, and general preservation requires obligations at every branch without a uniform-end-state premise |
| [CertifiedQueryCommutation](../packages/belay/Belay/Sqlite/CertifiedQueryCommutation.lean) | Retain `ReadCertificate.step_keeps`, `sendStatements_single_keeps`, `ReadCertificate.commutesOn`, `ReadCertificate.commutesOn_send`: full commutation keeps uniform connection/count, constant-clock and admitted-context premises; sent shortcuts exclude INSERT from a query |
| [DerivedColumnReads](../packages/belay/Belay/Sqlite/DerivedColumnReads.lean), [DerivedColumnQueries](../packages/belay/Belay/Sqlite/DerivedColumnQueries.lean) | Under `DerivedColumnMigration`, retain `Site.LookupMove`, `Site.ReadPreserved`, `Site.LookupMove.outputs`, `Site.LookupMove.rows`, `Site.ReadPreserved.outputs`, `translatesAt_of_outputs`, `queryTranslates`, `queryPreserves`: general expressions, stored affinity and filter agreement |
| [SchemaStepRules](../packages/belay/Belay/Sqlite/SchemaStepRules.lean), [ControlStepRules](../packages/belay/Belay/Sqlite/ControlStepRules.lean) | Retain `Sql.check_send_createTable`, `Sql.check_send_dropPlain`, `Sql.check_send_rewrite`, `Sql.check_send_setting`, `Sql.check_send_begin`, `Sql.check_send_commit` with their connection/error premises; not query endpoint deletions |
| [surface_claims_test.py](../tests/surface_claims_test.py) | Existing `ClaimsCount`, `ClaimsExists`, `ClaimsIn`, `ClaimsDuplicateKeys`, `ClaimsTableInfo`, `ClaimsSum`, `ClaimsUniqueLookup` fixtures use the new query facts |
| [surface_execution_test.py](../tests/surface_execution_test.py), [surface_migration_patterns_test.py](../tests/surface_migration_patterns_test.py) | Existing `ExecutionEquivalence`, `ExecutionComposition`, `ExecutionViewComparisons`, `ExecutionViewChoices` protect branches, state, raw steps and actual choices |
| [surface_s6_check_programs_test.py](../tests/surface_s6_check_programs_test.py) | Preserve full, weak and view actual-run refutations, migration weak-view claims, native replay and independently certified printed proofs after the relation representation changes. |
| [surface_assertion_examples_test.py](../tests/surface_assertion_examples_test.py) | `FilteredDuplicateKeyExamples`, `GlobalSignupInvariant`: filtered/NULL/collated groups and the generic application |
| [surface_s6_not_blocked_test.py](../tests/surface_s6_not_blocked_test.py) | `S6NotBlocked`, `S6NotBlockedLaw`: equivalence premises and NULL/collation counterexamples |
| [InsertSelectExecutions](../tests/surface/InsertSelectExecutions.lean) | Existing execution driver: alternative next databases and failures despite actual success |
| [surface_schema_script_test.py](../tests/surface_schema_script_test.py), [surface_rebuild_test.py](../tests/surface_rebuild_test.py) | `CertificateAfterDrop` protects named-table moves; `RebuildGuide.requireName_preserves_allSessions` in `RebuildKeeps` uses every migration branch; schema/control examples retain state/error cases |
| [surface_derived_column_test.py](../tests/surface_derived_column_test.py), [surface_migration_examples_test.py](../tests/surface_migration_examples_test.py), [surface_application_test.py](../tests/surface_application_test.py) | `S6RulesQuerySites`, `DerivedColumnExamples`, `NormalizedFieldLaws`, `NormalizedFieldExpansionLaws`, `ApplicationExpansion` now use general derived-column laws; retain affinity counterexamples and scoped simulation through the shared `LOWERCASE_LIBRARY` fixture chain |

Other direct query clients: [ExpansionCountQueries](../tests/surface/ExpansionCountQueries.lean),
[AccountSignupQueries](../tests/surface/AccountSignupQueries.lean), [CustomerInsertQueries](../tests/surface/CustomerInsertQueries.lean),
[SuccessBalanceSuccess](../tests/surface/SuccessBalanceSuccess.lean),
[SuccessUniqueEmail](../tests/surface/SuccessUniqueEmail.lean).
Production `NormalizedField*` owners were removed; their lowercase instances now live in fixtures.
Check implicit uses, exports, simp registrations, docs and builds. Preserve continuation/domain/frame assumptions.

## Prototype names and test retirement

[QuerySemantic](../experiments/proof-boundaries/QuerySemantic.lean), [QueryCount](../experiments/proof-boundaries/QueryCount.lean),
[QueryAggregate](../experiments/proof-boundaries/QueryAggregate.lean) and [ObservationAlgebra](../experiments/proof-boundaries/ObservationAlgebra.lean)
demonstrate historical shared facts. Their `ProofBoundaries` names are not fixed API names.
Five query families, including filtered duplicates, remain migration
work; current branch-state alternatives need current acceptance coverage.

Reuse one temporary 45-formula matrix and four relation witnesses through the
last planned change to their shared contracts. Record final Nix acceptance,
then remove redundant temporary sources and registrations. Preserve unique
premise-strength, semantic and independent-proof axiom coverage through existing
clients or focused missing cases. Do not add equality-law tests, a new manifest
or a permanent retired-endpoint matrix. Follow the parent specification's
test lifetime; historical witnesses replay at their accepted revision.
