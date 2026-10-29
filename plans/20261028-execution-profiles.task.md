# Share execution observation profiles

Date: 2026-10-28. Status: DONE on publication of this reviewed completion record.
Completion: [final acceptance record](20261028-execution-profiles.status.md#completion-record).
Audience: the implementation team.
Specification: [ADR 0026 D4](../docs/adr-0026-semantic-proof-boundaries.md),
[observation requirements](../docs/spec-proof-observations.md) and
[exact targets](../docs/spec-proof-query-observation-targets.md).
Record: [status](20261028-execution-profiles.status.md).
Assignment source: `5540e15f`; current relation contracts retain `3e2212ed`'s meanings.

This task contributes to the [Lean simplification goal](../docs/lean-simplification-goal.md)
by replacing repeated relation, transport and singleton proofs. Count the common
profile, all consumer changes and tests in its net result. Preserve all existing
capabilities, including proof automation; no capability loss is authorized.

## Required behavior

A shared profile contains the actual observed result and the predicate of
permitted observed results. Four existing relations become equality of the
appropriate profiles, with their exact original meanings at every execution
context. The actual result remains separate from the permitted observations.

| Current owner | Relation | Observer retained |
| --- | --- | --- |
| `ExecutionEquivalence` | `Sql.EquivAt` | Complete `SqlRun`, including connection and trace. |
| `ExecutionObservations` | `Sql.ObservationEquivAt` | `SqlRun.observation`. |
| `ExecutionViewEquivalence` | `Sql.View.EquivAt` | `Sql.View.fullObservation`. |
| `ExecutionViewEquivalence` | `Sql.View.ObservationEquivAt` | `Sql.View.observation`. |

Branches select a complete `RunStep.executions` member before choosing an
observation of its output. Each continuation uses that member's next connection.
Retain alternate databases and errors even when the actual execution succeeds.
Full observers retain connection and raw output count where the current formula
does; weak observers retain their current value/trace meaning. View projection
does not erase the distinction between raw and projected step counts.

Remove the nine fixed-context `refl`, `symm`, `trans` wrappers under
`Sql.EquivAt`, `Sql.View.EquivAt` and `Sql.View.ObservationEquivAt`. Ordinary
equality supplies those laws. Keep the higher-level `EquivOn`, `Equiv`,
`ObservationEquivOn`, `ObservationEquiv`, `ReturnsIn`, setoid and notation APIs
listed in the inventory, with their original meanings.

One branch transport argument supplies both full-to-weak laws and the existing
frame-based strengthening/`with_outputs` claims. One singleton argument supplies
the three profile-based `of_one_branch` proofs. Preserve `hasOneBranch`,
`branch_iff_actual`, frame and projection evidence as independent premises.
The absence of result choices alone is insufficient: singleton execution also
excludes further executions. Correct the stale introduction in `ExecutionDeterministic`
to state that existing requirement.

Preserve the bind/view-bind, trace-index, branch-admission and continuation
premises. Profile equality alone supplies no unrestricted bind congruence.
Migration observations remain the union over every migration branch at its
connection and shifted raw index. Keep full-state and interface-scoped
simulation distinct. Preserve NOT IN/NOT EXISTS and IN/EXISTS equivalences with
their separate NULL, affinity, rowid-alias and resolution premises.

## Production ownership and consumers

The initial source inventory has nineteen surface modules under
`packages/belay/Belay/Sqlite`; it is an ownership boundary, not an implementation
order. Use a suitable lower owner for the common construction and reasoning.
Keep modules below 200 lines. Add no relation registry, typeclass hierarchy,
observer DSL or new executor induction.

| Change | Existing modules |
| --- | --- |
| Relation definitions and laws | `ExecutionEquivalence`, `ExecutionObservations`, `ExecutionViewEquivalence`, `ExecutionEquivalenceLaws`, `ExecutionViewEquivalenceLaws`. |
| Transport and singleton proofs | `ExecutionViewFrames`, `ExecutionDeterministic`. |
| Composition and identity | `ExecutionEquivalenceBind`, `ExecutionViewBindFrames`, `ExecutionViewEquivalenceBind`, `ExecutionViewObservationBind`, `ExecutionViewIdentity`, `ExecutionViewMonad`. |
| Migration relation construction | `MigrationPatternAfter`, `MigrationPatternQuiet`, `MigrationPatternLaws`, `MigrationApplicationLaws`. |
| Automation | `CounterexampleActual`, `CheckProof`. |

At assignment, `CounterexampleActual.refuteByActualRun?` projected an `actual`
field from a proof of each relation. Migrate it to obtain actual-observation equality
from the new representation. Preserve kernel-certified refutation for all four
relation forms, dependency exclusions and the current limit: actual-run
refutation does not find a difference solely in permitted branches.
At assignment, `CheckProof.tryProof` quoted `Sql.EquivAt.refl`; remove that obsolete tactic
alternative and its checked reference. Preserve ordinary reflexivity, successful
proof suggestions and their independent certification. The new equality representation
must retain counterexample outcomes at the existing checking budgets: eager reflexivity
must not consume the budget by executing different SQL programs before refutation.

Keep `ExecutionBranches`, `ExecutionBranchLaws`, `ExecutionViewProjection` and
`ScopedAgreement` semantics unchanged. Retain `ScopedAt.of_one_branch` as
independent relation-based simulation. Keep certificate, derived-column and
schema/control bridge formulas listed in the inventory; migration obligations
remain per branch and permit different table positions. Request coordination
before any newly necessary edit outside this source boundary.

The implementation audit also includes the formula-preserving caller repair in
`MigrationPatternComposition` and `MigrationPatternFrames`. Reversed and
composed equalities need explicit applications of their observation and frame laws. Additional actual-observation projections in the existing
fixtures `DerivedColumnExamples`, `MigrationExpansionCounter`,
`ApplicationCounterCalls`, `S6RulesNegativeClock`, `RebuildAffinity` and
`ApplicationMissingTrigger` must use the profile projection. Their scoped
simulation projections and all semantic assertions remain unchanged.

ADR 0025 owns preservation conditions, `ScriptSuccess`, `SendStatementsBranches`,
the model singleton consumer, `InsertSelectExecutions.lean` and its count entry
in `surface_execution_test.py`. Reuse that fixture unchanged. Coordinate the
driver's other edits and surface manifest/aggregation registrations. D5 owns
expression congruence and `surface_claims_test.py`; this task does not need those
files. Executable SQL, conformance inputs and judge claims remain unchanged.

## Acceptance checks

- Kernel-check all four original relation formulas against the new profiles
  under their existing quantifiers. These equivalences are temporary witnesses;
  there is one current representation in production.
- Preserve existing counterexamples separating weak from full equality by
  state and projected views by raw step counts. Check actual and possible
  observations separately, including alternate next databases and an execution
  that fails despite actual success. Reuse existing branch fixtures.
- Migrate constructor, projection and removed-name uses in the existing
  execution, composition, view, migration, frame and application fixtures named
  in the status/inventory. Retain their semantic cases. Equality reflexivity,
  symmetry and transitivity need no replacement test matrix.
- Run the existing `surface_s6_check_programs_test.py` owner for full, weak and
  view refutations, migration weak-view claims, native replay and printed-proof
  certification. Preserve its trust/dependency exclusions. Add the missing named-view
  reflexivity case to this owner's existing fixture and printed-proof checks. The
  existing NOT-IN checker owner retains its budgets and expected counterexamples.
- Nix compiles complete affected packages, checked documentation and all real
  bind/frame/migration/certificate/NOT-IN clients. Keep their mathematical
  assumptions. Audit the generic profile proofs and independent evidence with
  the existing axiom policy; remove redundant wrapper audits.
- Inspect implicit uses, attributes, exports and automation before deleting
  declarations. Report net source changes and any measured cost change without
  inferring build speed from line counts. Apply the repository's check cadence
  with timeouts and the coordinator's shared full Nix build slot.

After final Nix acceptance, retire redundant old/new relation witnesses and
registrations, preserving their accepted revision for replay. Keep unique
semantic, premise and trust coverage until a current consumer or focused
regression supplies it. The task is done when the implementation, acceptance
record and test retirement are committed, reviewed, integrated and pushed.
