# Generalize query output proofs

Date: 2026-10-28. Status: DONE on publication of this reviewed completion record.
Completion: [final acceptance record](20261028-query-output-facts.status.md#completion-record).
Audience: the implementation team.
Specification: [ADR 0026 D1](../docs/adr-0026-semantic-proof-boundaries.md),
[required behavior](../docs/spec-proof-observations.md) and
[exact endpoint inventory](../docs/spec-proof-query-observation-targets.md).
Record: [status](20261028-query-output-facts.status.md).
Source baseline: `a3dd5a9a`; all 45 endpoint statements match main `3e2212ed`.

This task contributes to the [Lean simplification goal](../docs/lean-simplification-goal.md)
by replacing repeated observation proofs with reusable semantic output facts.
Count new facts, retained helpers, migrated callers and tests together. All
baseline capabilities and existing mathematical guarantees remain required;
no capability loss or build-speed improvement is assumed.

## Required behavior

Each of seven query families has a semantic characterization of its complete
modeled output: aggregate, scalar column, count, EXISTS, NOT EXISTS, duplicate
keys, and table info. Filtered and unfiltered duplicate queries share their
grouping family. A caller can prove an arbitrary output predicate by rewriting
the characterization. Meaningful source, execution and result cases must be
visible; equality to an opaque executor call does not satisfy this contract.

Replace the inventory's 21 model and 24 surface endpoints. Each original formula
remains derivable with exactly its original assumptions. Delete the replaced
declarations, migrate all callers and checked documentation, and retain no
aliases or parallel public observation families. Preserve all eight independently
usable resolver-only transports with their weaker premises. Retain unique-lookup,
pairwise and repeated-key mathematical consequences through the semantic facts.

The general output foundation preserves this order: support gating, datatype
mismatch, overflow, function error, then optional window binding and results.
Keep unmodeled behavior and every alternative in `Output.ofResults`. A theorem
that characterizes clean rows must not replace a more general no-error theorem.
In particular, retain the current independent guarantees of
`resolvedStepOutput_query_isError` without a bound-window premise and
`resolvedStepOutput_simple_not_isError_of_faultless` without a clean-source
premise. An unmodeled result is not an error.

| Family | Required distinctions |
| --- | --- |
| Aggregate | Overflow and successful output remain distinct. Successful empty input still gives one aggregate row. Preserve all `possibleResults`. |
| Scalar column | Keep the outer scalar-subquery exclusion, `valuePlain`, resolver-shape quantification and all three calmness premises. Membership remains allowed. |
| Count | The count subquery result is certain. Outer scalar subqueries remain allowed; the scalar-column exclusion does not apply here. |
| EXISTS and NOT EXISTS | Preserve matching and nonmatching source-row quantifiers and the opposite polarity of these families. |
| Duplicate keys | Group `Resolved.keptRows`, including NULL grouping and collation. Keep filter, result-column and key calmness, result resolution/groupedness, aggregate-feed restrictions and `GroupTermResolvesIn`. False/NULL filters omit rows; fallible filters are outside the calm contract. |
| Table info | Retain shadowing checks and the two appended hidden cells in each metadata row. |

The integrated expression congruence facts remove duplicated equality reasoning;
they do not remove callers' independent calmness or fault-freedom assumptions.
Executable SQL, supported syntax, conformance inputs and judge claims remain
unchanged. No observer registry, DSL, tactic framework or general test runner
is required.

## Source ownership and consumers

Model owners are under `packages/belay-sqlite-model/Belay/Sqlite/Model`; surface
owners are under `packages/belay/Belay/Sqlite`. Keep modules below 200 lines and
place shared facts below their consumers without copied definitions or cycles.

| Change | Existing owners |
| --- | --- |
| Model output families | `AggregateQueryOutput`, `ScalarSubqueryOutput`, `CountSubqueryOutput`, `ExistsSubqueryOutput`, `NotExistsSubqueryOutput`, `DuplicateKeyOutput`, `TableInfoOutput`. |
| Surface endpoints and retained transports | `AggregateQuery`, `ColumnQuery`, `CountQuery`, `ExistsQuery`, `NotExistsQuery`, `DuplicateKeyQuery`, `FilteredDuplicateKeyQuery`, `FilteredDuplicateKeyEmpty`, `TableInfoQuery`. |
| Retained consumer | `UniqueLookupQuery`, plus pairwise/repeated consequences in the duplicate-key owners. |
| Shared output and context facts | `QueryStatementOutput`, `SimpleQuerySteps`, `EvalContextLaws`; `SelectOneSubqueryOutput` and `SelectOneRowsOutput` may need shared-fact or import changes. |

Reuse `SimpleSubqueryRowsOutput`, `CertifiedQueryOutputs` and `SimpleTableCalm`.
Keep semantic helpers outside the 45-name deletion set, including count values,
scalar rows, quiet subquery facts and useful generic projections. Preserve their
names where ownership moves. The inventory identifies each such declaration.

Eleven maintained Lean fixtures directly use removed names: `ClaimsSum`,
`ClaimsTableInfo`, `ClaimsExists`, `ClaimsDuplicateKeys`, `ClaimsCount`, `ClaimsIn`,
`ExpansionCountQueries`, `AccountSignupQueries`, `CustomerInsertQueries`,
`SuccessBalanceSuccess` and `SuccessUniqueEmail`. Migrate their proofs while
retaining their semantic assertions. Their owners are `surface_claims_test.py`,
`surface_assertion_examples_test.py` and `surface_success_test.py`.

The execution-profile worker owns execution relations, bind/migration laws and
program-check automation. The preservation-context worker owns conditions,
`ScriptSuccess`, `SendStatementsBranches` and `InsertSelectExecutions`; this task
needs no changes there. The expression-congruence implementation is frozen;
ownership of its shared context modules and claims driver transfers to this task.
Coordinate model/surface manifests and umbrella registrations with the root.
Report newly necessary caller repairs and coordinate overlaps before editing.

## Acceptance checks

- Kernel-check all 45 original formulas, with their original quantifiers and
  assumptions, through the new facts. Keep one temporary witness set using
  existing fixture helpers and suites; do not add another runner or public API.
- Migrate a real consumer that reasons about a meaningful output predicate
  beyond the replaced row/empty/error observations. Ordinary equality
  substitution needs no separate test.
- Retain error precedence, unbound-window, may-fault-source, empty-aggregate and
  multiple-possible-result cases. Reuse `ClaimsMayFail`, `ClaimsQueryCases`,
  `QueryWindowExamples` and `ScriptRunExamples`; add only missing checks of the
  new laws or independent premise boundaries.
- Preserve `ClaimsUniqueLookup`, `FilteredDuplicateKeyExamples`,
  `GlobalSignupInvariant` and existing S6 automation coverage. Keep filtered
  NULL/collation behavior and the weaker resolver-only assumptions. The existing
  claims, assertion-example and success suites own the migrated fixtures.
- Compile complete affected packages and checked documentation in Nix. Audit
  generic proofs and independent semantic evidence with the existing axiom
  policy; remove redundant projection audits. Inspect attributes, exports,
  implicit/automation uses and dependency references before deleting names.
- Report net source changes including helpers, callers and tests. Compare the
  resulting proof dependencies without adding a permanent inventory test or
  inferring speed from source size. Follow repository check/review cadence with
  timeouts and the coordinator's shared full Nix build slot.

After final Nix acceptance, retire redundant 45-formula migration witnesses and
their registrations. Record the accepted revision so the evidence remains
replayable. Retain unique semantic, premise and trust coverage until a current
consumer or focused regression supplies it. The task is done when implementation,
acceptance, retirement and records are committed, reviewed, integrated and pushed.
