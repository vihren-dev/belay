# Query outputs and execution observation proofs

Date: 2026-10-26. Status: PROPOSED; ready for implementation assignment review.
Audience: implementers and reviewers.
Decision: [ADR 0026 D1 and D4](adr-0026-semantic-proof-boundaries.md).
Evidence: [query and observation findings](../experiments/proof-boundaries/query-observation-findings.md).
Targets: [exact declarations, owners and caller migrations](spec-proof-query-observation-targets.md).

## Required query behavior

The public proof API characterizes execution once for each of the seven
families: aggregate, scalar column, count, exists, not exists, duplicate key and
table info. A caller can rewrite the characterization to prove an arbitrary
predicate of the output. The characterization describes the meaningful source,
run and result cases; an equality to an opaque invocation of the executor does
not meet this requirement.

All 42 model/surface row, empty and error endpoints listed in the findings are
replaced. Each old formula is derivable with the same assumptions. The
implementation removes the old public declarations and updates actual callers,
exports, tests and documentation. Temporary migration witnesses can be anonymous
Lean examples; they do not become a permanent matrix of public names or tests.

Resolver-only output transport remains independently usable. The stronger
duplicate-key pairwise/repeated and count unique-lookup claims remain available
as mathematical results expressed through the new semantic facts. Useful
generic output and simplification lemmas also remain.

The semantic equation preserves the support gate, datatype mismatch, integer
overflow and certain function-error ordering. It preserves unmodeled behavior,
optional window binding and every possible result represented by `Output.ofResults`.
No possible result is replaced by a chosen deterministic representative.
An aggregate over an empty input may still return one row.

The no-error formulas retain their independent strength. In particular, a
may-fault source may give an unmodeled output without giving an error. Such a
claim does not require the clean source needed by some row formulas. The general
source output formula also covers a window that fails to bind.

## Required execution observation behavior

One profile construction contains the actual observed result and the predicate
of permitted observed results. The existing full, weak, full-view and weak-view
relations use equality of the appropriate profiles. Exact characterizations
recover the original four meanings at every execution context.

Relation reflexivity, symmetry and transitivity use ordinary equality rather
than the three existing parallel relation-law implementations. One branch transport argument
serves weakening and the existing frame-based strengthening. One singleton
argument serves full and weak deterministic comparisons.

Full observers retain the connection and raw output count where specified by
the existing relations. Weak observers retain their existing value/trace meaning.
Profile equality alone does not authorize arbitrary bind congruence. Existing
bind/view-bind obligations, branch admission of actual execution, frame
assumptions and trace-index behavior remain explicit. Migration simulation
semantics retain the distinction between full state and a permitted interface.

Delete replaced structural relation-law wrappers and duplicate singleton proofs
after caller migration. The experiment's iff adapters compare the old and new
representations; they are acceptance witnesses, not a permanent second API.
Use direct rewriting for trivial output-predicate transport. A general theorem
registry, typeclass hierarchy or new observer DSL is outside this scope.

## Boundaries that matter

`QueryStatementOutput` combines the foundational equation with its old
projections. `SimpleQuerySteps` owns bound-context facts; `CountSubqueryOutput`
owns count values and context facts. Shared definitions and semantic facts must
be importable below projection consumers, without cycles or copied definitions.

Execution definitions are in `ExecutionEquivalence`, `ExecutionObservations`
and `ExecutionViewEquivalence`. Actual frame/composition consumers include
`MigrationPatternFrames` and `ExecutionViewEquivalenceBind`. The production
implementation must inspect their formulas, not infer replaceability from names.
All paths here are module basenames under the model or surface package.

Count, aggregate and one surface count endpoint have compiled prototypes. The
other five query families remain migration work. The observation prototype
establishes all four exact relation adapters and representative transport and
singleton applications; it does not migrate the complete bind/migration API.
No whole-migration line reduction or performance improvement is established yet.

## Acceptance checks

- Kernel-check every removed query endpoint's exact old formula using the new
  API and original hypotheses as migration evidence. Include all seven families
  at both layers.
- Exercise an arbitrary predicate through a migrated real consumer; a separate
  test of equality substitution is unnecessary. Retain error precedence,
  unbound-window, may-fault source, aggregate-empty-input and possible-result
  regressions. At least one case must retain multiple possible results.
- Kernel-check the old four relation formulas against the new profiles. Retain
  examples where weak equality holds but full equality fails because of state,
  and projected views where raw step counts differ. Check actual and possible
  observations separately.
- Compile the existing frame, deterministic, bind, migration and public-example
  consumers after migration. Retain their original mathematical premises.
- Audit generic proofs and independently proved instances for the existing
  standard axioms only, without duplicate audits of trivial projections. Compile
  checked documentation and inspect source registrations/exports as well as
  dependency-report references before deleting declarations.
- Report removed and added source, including helpers, adapters that remain,
  migrated callers and formula tests. Compare dependency structure after the
  migration; any performance claim requires a separate controlled measurement.

Use the repository's existing model/surface proof tests, Nix checks and review
cadence. New checks have explicit timeouts. SQL predictions and judge inputs
remain unchanged. No new production CI framework is required.

## Test lifetime

The complete 42-formula matrix and four old/new relation adapters are temporary
acceptance witnesses under ADR 0026. Retire redundant witnesses after final
Nix acceptance and caller migration; keep their recorded revision for replay.
Import/source measurements and old-dependency inspections are one-time checks.

Permanent coverage protects distinct current contracts and semantic boundaries.
Reuse the existing claims, frame, bind and migration fixtures, including
`ExecutionEquivalence`, `ExecutionViewComparisons` and `ExecutionViewChoices`.
They already distinguish state, raw steps, actual results and possible results.
Add only uncovered premise checks, especially no-error without a clean source
and output reasoning without a bound-window premise. A witness that uniquely
protects such a requirement stays until a consumer or focused regression covers
it. Ordinary equality-law tests and duplicate singleton fixtures are unnecessary.
Use existing suites and record retirement in the existing status file.

## Assignment and coordination

Query output and execution profile work can be assigned independently. Their
shared constraint is ownership below their consumers. Coordinate import moves
with the foundational specification; ADR 0025's preservation work remains
separate. Create task/status files at assignment, with the exact current
formula inventory attached and any branch drift recorded.
