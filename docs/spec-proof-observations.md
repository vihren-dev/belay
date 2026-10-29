# Query outputs and execution observation proofs

Date: 2026-10-26. Status (2026-10-29): D1 and D4 implementation complete.
The [D1 completion record](../plans/20261028-query-output-facts.status.md) and
[D4 completion record](../plans/20261028-execution-profiles.status.md) record
proof acceptance, retirement and publication. The separate
[CI repair](../plans/20261028-proof-refactor-ci.status.md) remains in progress.
Audience: implementers and reviewers.
Decision: [ADR 0026 D1 and D4](adr-0026-semantic-proof-boundaries.md).
Evidence: [query and observation findings](../experiments/proof-boundaries/query-observation-findings.md).
Targets: [exact declarations, owners and caller migrations](spec-proof-query-observation-targets.md).
Source reviewed on 2026-10-28 against main `3e2212ed6983`. Compiled prototype evidence
is historical, against `3fe5caef`; this revision makes no current-main compile claim.

## Required query behavior

The public proof API characterizes execution once for each of the seven
families: aggregate, scalar column, count, exists, not exists, duplicate key
(filtered and unfiltered forms), and table info. A caller can rewrite it to prove
an arbitrary predicate of the output. The characterization describes the meaningful source,
run and result cases; an equality to an opaque invocation of the executor does
not meet this requirement.

All 45 endpoints in the current target inventory are replaced: 21 model and
24 surface row, empty and error claims. Each current formula remains derivable
with the same assumptions. Remove the old declarations and update actual callers,
exports, tests and documentation. Temporary migration witnesses can be anonymous
Lean examples; they do not become a permanent matrix of public names or tests.

Resolver-only output transport remains independently usable. The stronger
duplicate-key pairwise/repeated and count unique-lookup claims remain available
as mathematical results expressed through the new semantic facts. Useful
generic output and simplification lemmas also remain.

The duplicate-key model now accepts a WHERE condition and grouped scalar result
column. Preserve `Resolved.keptRows`, grouping collation and NULL grouping.
False or NULL filters exclude a row; a fallible filter is not treated as false.
Retain result-column resolution, groupedness, aggregate-feed restrictions and
`GroupTermResolvesIn`, plus independent filter, result-column and key calmness.
The filtered resolver-only transport remains usable without these calmness
premises. Keep its filtered pairwise consequence alongside the unfiltered claims.

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

Branches select a complete member of `RunStep.executions`, then an allowed
observation of that member's output. Each continuation uses that member's next
connection. Preserve alternate databases and errors, not just `.oneOf` row
choices sharing the actual connection. `Sql.hasOneBranch` requires no further
execution as well as no result choice; observation-profile equality uses all branches.

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

The `NotInQuery` equivalences are meaningful consumers, not observation
wrappers to delete. Preserve both NOT IN/NOT EXISTS and IN/EXISTS claims with
their key bounds, table presence, rowid-alias and `RowsAliased`, non-TEXT affinity,
statement resolution and result-column premises. Only the negative form needs
the inner non-NULL premise; both allow independent collations. The SELECT-step
bridge retains its SELECT syntax and no-further-execution facts. Mere output
equality does not establish those facts for an arbitrary write.

Migration observation transport now uses the union of replacement observations
over every migration branch, at that branch's connection and shifted raw index.
`ReadCertificate.preservesAt` needs obligations for each reached connection;
do not add a uniform-end-state premise to this weak preservation claim.
Certificates find the same named table at possibly different catalog positions.
Full `ReadCertificate.commutesOn` still needs uniform connections/output counts,
a constant clock and the admitted-context frame. Its sent-script shortcut
still excludes INSERT from a query; the general preservation rule does not.

## Boundaries that matter

`QueryOutputFacts` owns the foundational output equations and shared query
definitions. `QueryStatementOutput` consumes them for generic row and error
projections. `SimpleQuerySteps` owns bound-context facts; `CountSubqueryOutput`
owns count values and context facts. Shared definitions and semantic facts must
be importable below projection consumers, without cycles or copied definitions.
Reuse current exact-output facts in `SimpleSubqueryRowsOutput` and
`CertifiedQueryOutputs`; their clean/calm premises do not replace weaker guarantees.
The latter's `runScriptStep_simpleTable_output_agree` already handles different
statements, table positions and filters, with the same result columns and
the same keep decision on every original row. Its append specialization finds tables by name.
Reuse this generalization and `SimpleTableCalm`; do not reconstruct their proofs.

Execution definitions are in `ExecutionEquivalence`, `ExecutionObservations`
and `ExecutionViewEquivalence`. Actual frame/composition consumers include
`MigrationPatternFrames` and `ExecutionViewEquivalenceBind`. The production
implementation must inspect their formulas, not infer replaceability from names.
All paths here are module basenames under the model or surface package.
`DerivedColumnMigration`, `DerivedColumnReads` and `DerivedColumnQueries` replaced
the production `NormalizedField*` modules. Retain their general expression,
stored-affinity and filter-agreement premises; lowercase is now a fixture instance.
The schema/control `Sql.check_send_*` rules are semantic clients with explicit
state/error premises, not additions to the 45 query endpoint removals.

Count, aggregate and one surface count endpoint have historical compiled prototypes.
The other five families, including generalized filtered duplicates, remain migration
work. Historical observation adapters cover all four relation meanings, but predate
alternative execution states. Current acceptance must compile their replacements
against the updated branch relation and migrate the complete affected client API.
No whole-migration line reduction or performance improvement is established yet.

## Acceptance checks

- Kernel-check every removed query endpoint's current pre-refactor formula using the new
  API and current hypotheses as migration evidence. Include all seven families
  at both layers and both duplicate-key surface forms.
- Exercise an arbitrary predicate through a migrated real consumer; a separate
  test of equality substitution is unnecessary. Retain error precedence,
  unbound-window, may-fault source, aggregate-empty-input and possible-result
  regressions. At least one case must retain multiple possible results.
- Kernel-check the old four relation formulas against the new profiles. Retain
  examples where weak equality holds but full equality fails because of state,
  and projected views where raw step counts differ. Check actual and possible
  observations separately, including alternative next connections and an execution
  that fails when the actual execution succeeds.
- Compile the existing frame, deterministic, bind, migration and public-example
  consumers after migration. Retain their original mathematical premises,
  including named-table moves and preservation across differing migration end states.
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

The complete 45-formula matrix and four old/new relation adapters are temporary
acceptance witnesses under ADR 0026. Retire redundant witnesses after final
Nix acceptance and caller migration; keep their recorded revision for replay.
Import/source measurements and old-dependency inspections are one-time checks.

Permanent coverage protects distinct current contracts and semantic boundaries.
Reuse the existing claims, frame, bind and migration fixtures, including
`ExecutionEquivalence`, `ExecutionViewComparisons` and `ExecutionViewChoices`.
They already distinguish state, raw steps, actual results and possible results.
Reuse `FilteredDuplicateKeyExamples`/`GlobalSignupInvariant`, `S6NotBlocked`/
`S6NotBlockedLaw`, and `InsertSelectExecutions` for filtered groups, NULL/collation
premises, alternative databases and execution failures. Keep their existing drivers.
Also reuse `CertificateAfterDrop` in `surface_schema_script_test.py`,
`RebuildKeeps` in `surface_rebuild_test.py`, and the derived-column/affinity cases
in `surface_derived_column_test.py`. The lowercase fixture chain is shared by the
existing assertion, migration and application drivers; retain its scoped simulation.
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
