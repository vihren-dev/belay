# Share query source agreement proofs

Date: 2026-10-28. Status: DONE on publication of this reviewed completion record.
Completion: [final acceptance record](20261028-source-agreement.status.md#completion-record).
Audience: the implementation team.
Specification: [ADR 0026 D2](../docs/adr-0026-semantic-proof-boundaries.md),
[agreement requirements](../docs/spec-proof-agreement.md) and
[exact targets](../docs/spec-proof-agreement-targets.md).
Record: [status](20261028-source-agreement.status.md).
Source baseline: `81163254`; the affected source formulas equal main `3e2212ed`.

This task contributes to the [Lean simplification goal](../docs/lean-simplification-goal.md)
by replacing mirrored proof traversals and retiring redundant migration tests.
All baseline capabilities remain required, particularly S06 two-state observation
and M13 proof guarantees; no capability loss or weakening of retained guarantees
is authorized.

## Required behavior

One agreement contract compares the database observations of each query source.
Current tables compare their full optional lookup in the two current databases.
Initial tables compare their full optional lookup through the two optional
initial databases. Pragma sources compare the optional result of
`PragmaRows.rowsOn`. JSON and derived sources require no further database
agreement when the evaluation context and intermediate source rows are common.

The contract retains table absence, table shape, unsupported pragmas and
database-dependent pragma rows. Equal row lists alone are insufficient. It
allows both databases to change at once when the selected observations agree,
including fixed-pragma queries excluded by the old current-origin read test.
It is a sufficient agreement contract; minimal read footprints are outside scope.

One join argument, one source-fold induction and one induction on arbitrary
subquery depth establish equality of source rows, correlated source rows, full
subquery runs and evaluation contexts. The full run includes faults, endings
and certainty fields. The argument works for arbitrary outer rows and
intermediate `SourceRows`, including failed source folds. Query `runOn` and
`possibleOn` equalities follow from the shared argument. Initial- and
current-origin read tests provide short adapters without separate traversals.

Replace the following fourteen helpers in namespace
`Belay.Sqlite.Model.Resolved`; delete their old names and duplicated proofs:

| Current owner | Declarations |
| --- | --- |
| `TwoStateReads` | `QuerySource.join_initial_irrelevant`; `foldlM_join_initial_irrelevant`; `Query.source_initial_irrelevant`; `Query.sourceAfter_initial_irrelevant`; `Query.subqueryRun_initial_irrelevant`; `subqueryContext_initial_irrelevant`; `statementContext_initial_irrelevant` |
| `TwoStateCurrentLaws` | `QuerySource.join_current_irrelevant`; `foldlM_join_current_irrelevant`; `Query.source_current_irrelevant`; `Query.sourceAfter_current_irrelevant`; `Query.subqueryRun_current_irrelevant`; `subqueryContext_current_irrelevant`; `statementContext_current_irrelevant` |

All fourteen formulas remain derivable under their original assumptions.
Preserve these three downstream formulas in `TwoStateStatementLaws`, with
their current names and assumptions, through the common argument:

- `Resolved.Query.runOn_initial_irrelevant`.
- `Resolved.Query.possibleOn_initial_irrelevant`.
- `Resolved.Query.possibleOn_current_irrelevant`.

The two statement-context formulas are already among the fourteen helpers;
there are seventeen distinct old formulas to recover, not nineteen. Preserve
the downstream statement, possible-output, step-output and two-state observation
guarantees listed in the target inventory. Public source/read predicates remain
available below the proofs that use them, with unchanged meanings.

## Ownership and boundaries

The assigned files are `TwoStateReads`, `TwoStateCurrentLaws`,
`TwoStateStatementLaws`, suitable lower domain owners for the common agreement
proofs and query read predicates, and demonstrated direct consumers.
`Resolution/QueryForm` already owns `Source.isInitial` and `Source.readsCurrent`.
`Query.readsInitial` and `Query.readsCurrent` currently live in `TwoStateReads`;
move each once to a suitable lower owner. Keep useful statement read predicates
and classification laws. Keep modules below 200 lines and avoid a general
utility collection. Update checked public documentation with the formulas.

The old `TwoStateCurrentLaws` introduction says pragma rows are fixed. Replace
that description with the precise fixed-versus-database-dependent contract.
The executable evaluators and accepted SQL remain unchanged. Do not change
conformance inputs, judge claims, expression congruence, query-output contracts
or execution-profile contracts in this task. Do not copy the old endpoints into
the common proof's import closure.

The relevant existing test owner is `tests/surface_two_state_test.py`, whose
`PUBLIC_THEOREMS` list contains three replaced helper names. Migrate that list
to the generic proofs and meaningful independent evidence. Its existing
`tests/two_state_support.py` helper can compile focused Lean examples; reuse
the existing Nix surface owner. Coordinate any source-input additions in
`build-support/tests.nix` with the ADR 0025 API worker. Model aggregation and
manifest edits are shared: request a short ownership window from the
coordinator before changing them. Other workers own atom preservation and the
deterministic module manifest repair.

## Acceptance checks

- Kernel-check all seventeen original formulas against the new argument with
  the baseline's assumptions. Universal witnesses cover arbitrary subquery
  depth and correlated traversal. Do not substitute closed examples for them.
- Keep focused checks of absent versus present tables, unequal table shape,
  a fixed pragma with both databases changed, and a database-dependent pragma.
  Reuse existing examples when they protect the same meaning. Establish that
  equal rows do not imply full lookup agreement. Check the generic core and
  independent adapters for forbidden axioms with the existing mechanism.
- Nix compiles the affected model, the complete surface, checked documentation
  and real clients of two-state statement/output laws. Preserve the existing
  native observation, changed-current-database and origin-swap checks.
- Inspect simp, instance and export registrations and all callers before
  deleting names. Report net Lean changes including new common proofs, read
  adapters, caller changes and tests. Import/count/name comparisons are
  one-time acceptance observations, not permanent snapshot tests.
- Apply the repository's per-edit, per-commit, end-of-slice and end-of-task
  checks with configured timeouts. Full Nix checks use the coordinator's shared
  build slot. No runtime semantics or mutant table changes are expected.

The old-formula witnesses are temporary migration evidence. After Nix acceptance
of this task's final contract, remove redundant witnesses and their source
registrations, and record the accepted historical revision for replay. A witness
that uniquely protects a premise or trust requirement remains until a current
consumer or focused regression covers it. Keep the focused current agreement
checks; add no permanent per-helper matrix or new test framework.

The task is done when the implementation, final acceptance evidence and test
retirement are committed, independently reviewed, integrated and pushed.
Expression congruence remains a separate ADR 0026 D5 assignment.
