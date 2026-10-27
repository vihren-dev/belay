# Query and observation change targets

Date: 2026-10-27. Status: PROPOSED; implementation has not started.
Audience: designers and reviewers.
Contract: [query and observation specification](spec-proof-observations.md),
implementing [ADR 0026 D1 and D4](adr-0026-semantic-proof-boundaries.md).
Inventory baseline: `3fe5caef`; the linked production files are unchanged from
that revision. Reconcile branch drift before implementation. Counts below refer
to authored declarations, not generated declarations or measured net savings.

Model names below have namespace `Belay.Sqlite.Model`; surface names have
namespace `Belay.Sqlite`. A prefix plus each explicitly listed suffix names
one declaration. These finite lists are not wildcard deletion instructions.

## Replace 21 model observation endpoints

Each family gets meaningful semantic output facts from which arbitrary output
predicates follow by rewriting. Remove these endpoints after caller migration;
their original formulas and assumptions remain migration obligations.

| Owning source | Exact name prefix | Exact suffixes to replace |
| --- | --- | --- |
| [AggregateQueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/AggregateQueryOutput.lean) | `resolvedStepOutput_aggregateTable_` | `hasRows`, `not_hasNoRows`, `isError` |
| [ScalarSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/ScalarSubqueryOutput.lean) | `resolvedStepOutput_scalar_` | `hasRows`, `hasNoRows`, `not_isError` |
| [CountSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/CountSubqueryOutput.lean) | `resolvedStepOutput_count_` | `hasRows`, `hasNoRows`, `not_isError` |
| [ExistsSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/ExistsSubqueryOutput.lean) | `resolvedStepOutput_exists_` | `hasRows`, `hasNoRows`, `not_isError` |
| [NotExistsSubqueryOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/NotExistsSubqueryOutput.lean) | `resolvedStepOutput_notExists_` | `hasRows`, `hasNoRows`, `not_isError` |
| [DuplicateKeyOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/DuplicateKeyOutput.lean) | `resolvedStepOutput_notExists_duplicateKeys_` | `hasRows`, `hasNoRows`, `not_isError` |
| [TableInfoOutput](../packages/belay-sqlite-model/Belay/Sqlite/Model/TableInfoOutput.lean) | `resolvedStepOutput_simplePragma_` | `hasRows`, `hasNoRows`, `not_isError` |

## Replace 21 surface observation endpoints

These expose the same family results through written SQL. Replace the three
named observations in each row, preserving the resolver-only transport in the
last column as an independently usable fact with its original weaker premises.

| Owning source | Exact declarations to replace | Resolver transport to retain |
| --- | --- | --- |
| [AggregateQuery](../packages/belay/Belay/Sqlite/AggregateQuery.lean) | `Holds.iff_selectAggregate`, `Empty.not_selectAggregate`, `Fails.iff_selectAggregate` | `Script.outputOn_selectAggregate` |
| [ColumnQuery](../packages/belay/Belay/Sqlite/ColumnQuery.lean) | `Holds.iff_selectOne_column`, `Empty.iff_selectOne_column`, `Fails.not_selectOne_column` | `Script.outputOn_selectOne_column` |
| [CountQuery](../packages/belay/Belay/Sqlite/CountQuery.lean) | `Holds.iff_selectOne_count`, `Empty.iff_selectOne_count`, `Fails.not_selectOne_count` | `Script.outputOn_selectOne_count` |
| [ExistsQuery](../packages/belay/Belay/Sqlite/ExistsQuery.lean) | `Holds.iff_selectOne_exists`, `Empty.iff_selectOne_exists`, `Fails.not_selectOne_exists` | `Script.outputOn_selectOne_exists` |
| [NotExistsQuery](../packages/belay/Belay/Sqlite/NotExistsQuery.lean) | `Holds.iff_selectOne_notExists`, `Empty.iff_selectOne_notExists`, `Fails.not_selectOne_notExists` | `Script.outputOn_selectOne_notExists` |
| [DuplicateKeyQuery](../packages/belay/Belay/Sqlite/DuplicateKeyQuery.lean) | `Holds.iff_selectOne_noDuplicateKeys`, `Empty.iff_selectOne_noDuplicateKeys`, `Fails.not_selectOne_noDuplicateKeys` | `Script.outputOn_selectOne_noDuplicateKeys` |
| [TableInfoQuery](../packages/belay/Belay/Sqlite/TableInfoQuery.lean) | `Holds.iff_selectOne_tableInfo`, `Empty.iff_selectOne_tableInfo`, `Fails.not_selectOne_tableInfo` | `Script.outputOn_selectOne_tableInfo` |

Retain and migrate the meaningful consequences
`Holds.iff_selectOne_noDuplicateKeys_pairwise` and
`Empty.iff_selectOne_noDuplicateKeys_repeated` in `DuplicateKeyQuery`, and
`Holds.selectOne_count_unique_lookup` in
[UniqueLookupQuery](../packages/belay/Belay/Sqlite/UniqueLookupQuery.lean).
They add mathematical content beyond transporting an output observer.

## Preserve semantic helpers and move shared ownership where needed

The mixed owner files above are not wholesale deletion targets. Source/context,
calmness and expression-shape facts outside the 42-name list remain available
where the new semantics or other clients use them. The following are concrete
shared ownership targets; this list does not rename their public API in advance.

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

The existing generic projections `resolvedStepOutput_query_isError` in
`QueryStatementOutput` and `resolvedStepOutput_simple_not_isError_of_faultless`
in `SimpleQuerySteps` identify important independent guarantees: the former
needs no bound-window premise; the latter needs no clean-source premise.
They are outside the 42-endpoint deletion set. Any consolidation of their
proofs must retain those strengths. General row/error projections and semantic
simp laws are not automatically obsolete merely because exact output is exposed.

Preserve support gating, mismatch/overflow/function-error precedence, unmodeled
results and every `Output.ofResults` alternative. Aggregate empty input can
produce one row. Preserve resolver scope, parameter, table and calmness premises.

## Replace four relation representations and nine structural wrappers

The four `Prop` structures become equality of profiles containing the actual
observation and the predicate of possible observations. Their meanings stay
distinct; each old `actual`/`branches` pair has an exact migration witness.

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

## Share transport and singleton reasoning; retain semantic boundaries

| Owning source | Exact claims whose proof reasoning is consolidated |
| --- | --- |
| [ExecutionObservations](../packages/belay/Belay/Sqlite/ExecutionObservations.lean) | `Sql.EquivAt.observation` |
| [ExecutionViewEquivalenceLaws](../packages/belay/Belay/Sqlite/ExecutionViewEquivalenceLaws.lean) | `Sql.View.EquivAt.observation` |
| [ExecutionViewFrames](../packages/belay/Belay/Sqlite/ExecutionViewFrames.lean) | `Sql.View.EquivAt.with_outputs`, `Sql.View.ObservationEquivAt.full_of_frames` |
| [ExecutionDeterministic](../packages/belay/Belay/Sqlite/ExecutionDeterministic.lean) | `Sql.EquivAt.of_one_branch`, `Sql.View.EquivAt.of_one_branch`, `Sql.View.ObservationEquivAt.of_one_branch` |

Derive these claims through common branch transport or singleton reasoning;
delete replaced duplicate implementations and unnecessary wrappers after callers
migrate. Keep `Sql.branch_iff_actual` and `Sql.hasOneBranch` as the execution facts
that supply singleton premises. Keep the full-to-weak projection fact
`Sql.View.observation_eq_of_full` and the frame characterization
`Sql.View.fullObservation_eq_iff` in their listed owners, or suitable lower owners.
Migrate `Sql.View.identity_observation_iff`, `Sql.View.identity_full_eq_iff` and
`Sql.View.identity_equiv_iff` in
[ExecutionViewIdentity](../packages/belay/Belay/Sqlite/ExecutionViewIdentity.lean).

The observers themselves are in
[ExecutionViewProjection](../packages/belay/Belay/Sqlite/ExecutionViewProjection.lean).
Full-view comparison retains connection and raw next index; weak comparison
does not determine these. Actual agreement is separate from possible-image
agreement. [ScopedAgreement](../packages/belay/Belay/Sqlite/ScopedAgreement.lean)
owns `RunsAgree` and `Sql.ScopedAt`; these and
`Sql.ScopedAt.of_one_branch` in `ExecutionDeterministic` remain distinct
relation-based simulation, not equality of observation profiles.

## Migrate actual clients and existing tests

| Source | Required migration or retained coverage |
| --- | --- |
| [ExecutionEquivalenceLaws](../packages/belay/Belay/Sqlite/ExecutionEquivalenceLaws.lean) | `Sql.EquivAt.check_iff`, `Sql.EquivAt.andOk_iff`, `Sql.EquivAt.ifOk_iff`, `Sql.Equiv.transformer`, `Sql.Equiv.fresh_iff`, `Sql.Equiv.succeeds_iff` retain their guarantees |
| [ExecutionEquivalenceBind](../packages/belay/Belay/Sqlite/ExecutionEquivalenceBind.lean) | `Sql.EquivOn.bind`, `Sql.Equiv.bind`, `Sql.Equiv.bind_right`, `Sql.Equiv.bind_left`, `Sql.Equiv.map`, `send_append_equiv` |
| [ExecutionViewBindFrames](../packages/belay/Belay/Sqlite/ExecutionViewBindFrames.lean), [ExecutionViewEquivalenceBind](../packages/belay/Belay/Sqlite/ExecutionViewEquivalenceBind.lean) | `Sql.View.EquivAt.bind_branch`, `Sql.View.EquivOn.bind`, `Sql.View.Equiv.bind` |
| [ExecutionViewObservationBind](../packages/belay/Belay/Sqlite/ExecutionViewObservationBind.lean) | `Sql.View.observation_bind_return_eq`, `Sql.View.observation_bind_branch`, `Sql.View.ObservationEquivOn.bind_same` |
| [MigrationPatternFrames](../packages/belay/Belay/Sqlite/MigrationPatternFrames.lean) | `TranslatesAt.commutes_of_frames`, `TranslatesOn.commutes_of_frames`; retain connection/step frames |
| [surface_claims_test.py](../tests/surface_claims_test.py) | Existing `ClaimsCount`, `ClaimsExists`, `ClaimsIn`, `ClaimsDuplicateKeys`, `ClaimsTableInfo`, `ClaimsSum`, `ClaimsUniqueLookup` fixtures use the new query facts |
| [surface_execution_test.py](../tests/surface_execution_test.py), [surface_migration_patterns_test.py](../tests/surface_migration_patterns_test.py) | Existing `ExecutionEquivalence`, `ExecutionComposition`, `ExecutionViewComparisons`, `ExecutionViewChoices` protect branches, state, raw steps and actual choices |

Other direct query clients to migrate are
[ExpansionCountQueries](../tests/surface/ExpansionCountQueries.lean),
[AccountSignupQueries](../tests/surface/AccountSignupQueries.lean),
[CustomerInsertQueries](../tests/surface/CustomerInsertQueries.lean),
[SuccessBalanceSuccess](../tests/surface/SuccessBalanceSuccess.lean) and
[SuccessUniqueEmail](../tests/surface/SuccessUniqueEmail.lean).
This is a source-verified client list, not a closed deletion oracle: check
implicit uses, exports, simp registrations, docs and complete affected builds.
Bind and migration claims retain their continuation/domain/frame assumptions.

## Prototype names and test retirement

[QuerySemantic](../experiments/proof-boundaries/QuerySemantic.lean),
[QueryCount](../experiments/proof-boundaries/QueryCount.lean),
[QueryAggregate](../experiments/proof-boundaries/QueryAggregate.lean) and
[ObservationAlgebra](../experiments/proof-boundaries/ObservationAlgebra.lean)
demonstrate the shared facts. Their `ProofBoundaries` names are experimental,
not prescribed public API names. Five query families still need migration.

Reuse one temporary 42-formula matrix and four relation witnesses through the
last planned change to their shared contracts. Record final Nix acceptance,
then remove redundant temporary sources and registrations. Preserve unique
premise-strength, semantic and independent-proof axiom coverage through existing
clients or focused missing cases. Do not add equality-law tests, a new manifest
or a permanent retired-endpoint matrix. Follow the parent specification's
test lifetime; historical witnesses replay at their accepted revision.
