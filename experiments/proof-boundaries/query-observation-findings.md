# Query outputs and observation equality

Date: 2026-10-26. Audience: designers and reviewers.
Scope: the query and observation experiments for the
[design task](../../plans/20261026-proof-boundaries-design.task.md).
Production source is unchanged. The standalone Nix experiment target supplies
the acceptance result and audited proof closures; local checks are diagnostic.

## Decision: adopt semantic query outputs, retain independent assumptions

The root cause is a repeated public matrix: each query family describes one
execution, then proves separate row, empty-row and error observations at both
model and surface layers. A caller with a different output predicate needs
another theorem, even though execution has already been characterized.

`QuerySemantic.query_source_output` gives one exact output formula. Under the
original clock, known-counter and source premises, it preserves the support
gate, mismatch, overflow and certain-function-error precedence, optional window
binding, and `Output.ofResults` of all possible results. It requires no premise
that the window binds. It therefore retains the weaker error-law assumptions.
`simple_output` retains an unmodeled case for a source with fault `.may`.
`simple_no_error` recovers the no-error claim without a clean-source premise.

For any exact output equality `observed = some output` and arbitrary predicate
`P : Output → Prop`, the reusable observation formula is:

```lean
(∃ value, observed = some value ∧ P value) ↔ P output
```

For a Boolean observer `test`, the corresponding formula is
`observed.any test = true ↔ test output = true`. Both are substitution followed
by `simp`. The experiment names these reductions to expose the contract, but a
production specification need not require public helper theorems for them.
Ordinary rewriting is sufficient. The substantive abstraction is the exact
semantic output, not a new framework for applying predicates.

Two families and one surface application establish the boundary:

- `QueryCount.count_semantics` computes the count-subquery context once and
  gives the exact outer output plus its condition value. The three following
  acceptance theorems recover the original model formulas and assumptions.
- `QueryAggregate.aggregate_output` computes source, run and context once. It
  retains integer-overflow errors; the three acceptance theorems recover the
  original rows, never-empty and error formulas. An aggregate over an empty
  table can still produce one result row.
- `QuerySurface.surface_count_holds` copies the original long resolver
  premises and conclusion of `Holds.iff_selectOne_count`. It uses the existing
  resolver-only `Script.outputOn_selectOne_count`, then the new count semantics
  through its row projection. It calls no old observation endpoint.

The core proofs use source, context and run facts, not the specialized endpoints
being replaced. `Output.ofResults` preserves every alternative represented by
`.oneOf`; the prototypes do not select one result. No concrete nondeterministic
family was migrated. Five of the seven families remain an implementation
acceptance obligation, not an experimentally established migration.

### Affected declarations and consumers

There are 21 authored surface endpoints and 21 matching model endpoints in this
inventory. These are candidates for replacement, not 42 redundant proofs or a
claim about net source savings. Locations are relative to the two package roots
`packages/belay/Belay/Sqlite` and
`packages/belay-sqlite-model/Belay/Sqlite/Model`.

| Family | Surface file and first endpoint | Model file and first endpoint |
| --- | --- | --- |
| Aggregate | `AggregateQuery.lean:57` | `AggregateQueryOutput.lean:21` |
| Scalar column | `ColumnQuery.lean:64` | `ScalarSubqueryOutput.lean:109` |
| Count | `CountQuery.lean:54` | `CountSubqueryOutput.lean:102` |
| Exists | `ExistsQuery.lean:44` | `ExistsSubqueryOutput.lean:64` |
| Not exists | `NotExistsQuery.lean:45` | `NotExistsSubqueryOutput.lean:17` |
| Duplicate key | `DuplicateKeyQuery.lean:48` | `DuplicateKeyOutput.lean:79` |
| Table info | `TableInfoQuery.lean:47` | `TableInfoOutput.lean:51` |

The selected report has three named, source-visible consumers of these surface
endpoints: `Holds.iff_selectOne_noDuplicateKeys_pairwise`,
`Empty.iff_selectOne_noDuplicateKeys_repeated`, and
`Holds.selectOne_count_unique_lookup`. Their mathematical content remains useful;
only their dependency on the observation matrix should change. The report does
not enumerate all tests, anonymous examples or external callers. Implementation
must search source and compile the complete affected packages.

### Ownership and real overhead

The four query experiment files contain 304 lines, including documentation,
imports, audit commands and the seven formula regression theorems. No production
lines were deleted. Count's original three proof bodies are already three lines
each; the new certificate is not a local line-saving result for that family.
It removes repeated context setup as an API obligation and serves arbitrary
observers. Aggregate's three proofs repeat source lookup and run classification;
the new certificate performs that reasoning once. Net savings require the full
migration and deletion of the old matrix, not adding certificates beside it.

`QuerySemantic` now imports model laws only. `QueryStatementOutput` still owns
both the foundational exact equation and its old projections. `SimpleQuerySteps`
owns bound-context definitions and context facts beside its old projections.
`CountSubqueryOutput` owns count values and context facts beside its endpoints.
Production must put these definitions and semantic facts below the projection
consumers. The experiment does not copy these helpers merely to avoid their
current file ownership. `QueryAggregate` directly imports the lower run/source
laws; it does not import `AggregateQueryOutput`.

## Decision: adopt equality of observation profiles

`ObservationAlgebra.observationProfile` uses the ordinary pair:

```lean
(observe actual, fun value => ∃ result, branches result ∧ observe result = value)
```

The first component retains the actual result's observation separately from
the possible-observation predicate. Equality of the pair supplies ordinary
reflexivity, symmetry and transitivity. No new setoid or relation-law framework
is needed. The module imports only `Std`, so this algebra has a lower owner
than every SQL relation it serves.

`ObservationApplications` proves exact iff adapters for four existing relations:
ordinary full and weak equivalence, and projected full and weak equivalence.
Their observers stay different. The adapters allow comparison against unchanged
production contracts during the experiment; they are not a proposed second API.

`observationProfile_transport` proves branch matching once. It transfers equality
when matching old observations imply matching new observations on each pair of
branches, with actual results admitted as branches. Applications establish:

- full view equality implies weak view equality;
- weak view equality becomes full only with the original complete-connection
  and raw-step-count frame assumptions;
- view equality composes by ordinary equality transitivity;
- single-branch programs compare under any observer from actual agreement.

The proofs do not invoke the old transport or deterministic-view endpoints.
Full state remains observable where the original relation observes it. This
does not merge full-state simulation with interface-scoped simulation, and it
does not prove arbitrary sequential composition from observation equality.

### Affected declarations, consumers and overhead

The existing public structures are in `ExecutionEquivalence.lean:11`,
`ExecutionObservations.lean:17`, and `ExecutionViewEquivalence.lean:12,30`.
There are nine authored reflexivity/symmetry/transitivity wrappers in
`ExecutionEquivalenceLaws.lean:10–21` and
`ExecutionViewEquivalenceLaws.lean:9–43`. Two duplicated view single-branch
introductions are at `ExecutionDeterministic.lean:86,144`. Repeated branch
matching also occurs in `ExecutionViewEquivalenceLaws.lean:64` and
`ExecutionViewFrames.lean:33,57`.

Actual consumers include `MigrationPatternFrames.lean:36` for full-state frame
strengthening and `ExecutionViewEquivalenceBind.lean:29` for start-trace
transport. Their frame and composition obligations must remain explicit.

The observation prototype adds 186 lines: 77 for the generic algebra and 109
for SQL adapters and applications, with documentation and audits included.
During experimentation the old relations coexist with their exact adapters, so
the prototype grows the source. Production simplification requires replacing
the old representations and deleting obsolete wrappers, not keeping the adapters
as compatibility layers. The experiment establishes shared reasoning and exact
contracts; it measures neither net migration size nor compilation speed.

## Proposed implementation acceptance

Require exact recovery of all original independent observation guarantees under
their original assumptions, including source-fault and unbound-window cases.
Require remaining query families to preserve possible results, error codes and
precedence, resolver restrictions and empty-input behavior. Keep resolver-only
laws with their weaker assumptions and retain useful pairwise and lookup laws.
Use semantic characterization plus direct rewriting for arbitrary predicates.

Require exact relation characterizations for all four observer choices and
applications of the shared branch transport to existing frame and singleton
claims. Retain separate full-state and interface-scoped simulation semantics.
Update callers and remove replaced declarations without aliases. Place shared
facts below consumers in the import graph. Audit prototype and migrated proof
closures and compile affected public examples. Report actual source changes and
measure performance separately if a performance claim is desired.
