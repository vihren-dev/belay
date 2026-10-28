# Primitive ownership and surface import task status

Date: 2026-10-28. Status: DONE on publication of this reviewed completion record.
Audience: the implementation team.
Task: [primitive ownership and imports](20261028-proof-primitive-imports.task.md).
Specification: [ADR 0026 D6](../docs/adr-0026-semantic-proof-boundaries.md).
Production baseline: `3e2212ed`; assignment baseline: `3ef94b97`.

## Completion record

Final implementation source is `23a3427b`, published as `9eb179de` in [PR
297](https://github.com/vihren-dev/sqlite-verifier/pull/297). The [combined
acceptance record](20261028-proof-refactor-ci.status.md) owns the final Nix
reports and source identities.

The three unchanged primitive proofs have lower owners; explicit surface
imports retain their complete bodies and public instances. ComparisonLaws stays
outside executable classifiers.

Original-formula witnesses passed Nix at `53a346e1` before redundant copies
were retired. Final `23a3427b` passed the full suites, verdict, configured Nix
checks, scheduled writers, public documentation and API reference. Final
dependency inspection and the [Nix cost sample](20261028-expression-congruence.status.md#final-nix-proof-cost-sample)
complete the shared measurements. The [goal ledger](../docs/lean-simplification-goal.md#milestones-and-decisions)
records 87,018 maintained Lean lines and all 30 fixed capability groups retained.

The implementation and retirement are published. Integration and publication of
this reviewed closing record complete this task. The separate CI task still
awaits hosted mutation measurements. Record checks: `tests/docs_test.py` and
independent `just review`. Following sections preserve historical checkpoints;
their pending notes are superseded by this completion record.

Final Nix comparison acceptance compiles and detects all three original mutants,
including `text_without_case`, under the unchanged limits. Its one test has no
failure, error or skip; command wall time is 134.852 seconds. JUnit:
`/nix/store/zv8w1pxdwyc5l7ciwnd2l0d0pqvgsdv5-sqlite-verifier-test-mutants-comparison-boundary-1/junit.xml`.

## Implementation

The owner authorized implementation of ADRs 0025/0026 on 2026-10-28. This task
has a disjoint edit surface from ADR 0025 foundations. The coordinator released
the shared model aggregation and manifest for additive registrations.

- `Collation.compare_eq_of_binary` now belongs to `ComparisonLaws`, outside the executable classifier closure.
- `Database.tableAt_of_table` now belongs to `Database`, next to `Database.table`.
- `Database.table_of_findTable` now belongs to `DatabaseLookup`, whose imports
  are `Database` and `Resolution.CatalogSpec`.

The three declaration statements and proof bodies are identical to the assignment
baseline. Former owners import the lower provider, and direct consumers use the
lower imports. `Database.tableAt_of_table` stays separate from the named lookup:
it needs no resolver proof imports. At the initial D6 integration, the three owners' project import closures
contained 5, 42 and 245 modules respectively, including each owner; none contained
`ForeignKeySelfLookup`, `AddColumnFromValid` or `TableSourceLaws`.
`LiteralData.generatedCells_plain` remains in `AdmittedCellLaws`.

`Values`, `Script` and `ValueDisplay` now import their actual model providers.
Their non-import source is identical to the baseline, including declarations,
checked documentation, instances and attributes. The model manifest retains
its umbrella root and adds the eight provider roots used by these modules:
`Comparison`, `Declarations`, `StoreValue`, `StoreValueLaws`, `Truth`,
`Resolution.Syntax`, `SqlAdvance` and `OutputRepr`. `DatabaseLookup` is registered
as a build module and imported by the model umbrella. Compilation also requires
explicit provider imports in `Program`, `Database`, `Run`, `ReplayValues` and
`SampleHints`. Their providers add five public roots: `Output`,
`DatabaseConstraintChecks`, `ForeignKeyFacts`, `Resolution.Defaults` and
`ScriptRunAppend`. Further compiler-required repairs in `Queries`,
`TwoStateObservation`, `SqlDocObservation` and `SqlDiagnostics` add the public
roots `QueryOutputs`, `ResolveStatementSingle`, `TwoStateQuery`, `OutputTable`
and `Resolution.ErrorNames`. All repaired surface module bodies remain unchanged.
All prior model build modules remain registered; integration must also retain
ADR 0025 registrations.

## Import observations and capability effect

The one-time source inspection uses the historical experiment's project-source
scope and traversal from explicit imports, against assignment `3ef94b97`:

| Surface module | Before | After |
| --- | ---: | ---: |
| `Values` | 756 | 76 |
| `Script` | 756 | 153 |
| `ValueDisplay` | 756 | 158 |

These are import-scope observations, not compilation-time measurements or CI
thresholds. The move preserves formulas and changes no executable SQL behavior,
feature scope, judge input or corpus. No capability loss is proposed.

Relative to assignment `3ef94b97`, the complete production diff adds 35 physical
Lean source lines and 20 manifest lines, including new ownership scaffolding,
all caller imports and public-root registration. These counts include comments
and blank lines; they are not the long-term goal's non-comment code metric.
There are no test-file changes and no additional theorem formula or proof body.

## Validation and remaining work

The required diagnostic build is `just dev-build`. Affected source checks are
`tests/surface_layers_test.py`, `tests/test_lean_categories.py` and
`tests/docs_test.py`. These local checks do not supply acceptance evidence.
Current Nix acceptance is pending.

Implementation commit `2adf12a3` has independent Claude review with zero must and
zero should findings, recorded in
[review 20261028T112837Z](../reviews/20261028T112837Z-2adf12a3/review.json).
The review did not run checks. The coordinator receives this reviewed source for
combined acceptance; no standalone Nix acceptance result is claimed.

The coordinator will combine the independently reviewed implementation with
ADR 0025 and the separately owned acceptance repair, then run the required
Nix package, surface, checked documentation, full-suite, verdict, Nix-source and
scheduled-check gates once on that integrated source. No mutant table changes.

No active duplicate proof witness, baseline/narrow source copy, import-count
check or new test framework was added. Historical experiments remain replayable
at their recorded revisions, outside normal CI. Current package compilation and
existing surface fixtures supply the retained contract coverage after acceptance.
Final Nix evidence, integration, push and workspace cleanup remain pending.
This task is not DONE.

## Comparison proof placement follow-up

The coordinator audited the changed executable import closure after the first
combined contract acceptance. The existing `text_without_case` mutant invalidated
the moved collation proof inside `Comparison`, before the harness could observe its changed SQL verdict.
A compilation error cannot count as a detected mutant. This diagnosis led to
the proof-owner correction below; its acceptance requires the Nix measurement.

The existing task now requires a foundational proof owner outside the executable
classifier's import closure and the existing three-mutant Nix measurement.
The theorem's name, formula and proof body, all SQL definitions, mutant edits,
targets and deadlines remain unchanged. This ownership correction changes no
mathematical contract accepted at `53a346e1`. The separate witness retirement
continues; final combined acceptance must include the ownership correction.
Claude reviewed scope clarification `684e46a2` with zero must and zero should
findings (`reviews/20261028T151652Z-684e46a2/review.json`). A separate worker is
assigned the ownership correction. It owns no retirement files and uses no
Nix build slot until the coordinator releases one.


## Comparison placement implementation

The worker implemented the follow-up in `sqlite-verifier-comparison-proof-boundary`,
assigned at `40d7233c`. `ComparisonLaws` imports only `Comparison` and owns the
unchanged collation theorem. `ForeignKeySelfLookup` and `PlainInsertRows` import
that proof provider directly. The model umbrella and explicit module list each
add `ComparisonLaws`; the public roots are unchanged. No executable definition,
mutant, target, test or mathematical contract is edited.

Independent writable package caches were copied from the coordinator workspace
only after its package sources were confirmed identical. The copies contain no
symlinks and share no file inodes with their source.

The relocated declaration, its docstring and its complete proof body are
byte-identical to `40d7233c` (SHA256
`68a34ac00d4b165bf4883c76dfc8105b13b1799cca4ca84a5106ec55bea1cd0d`).
Removing that block is the only change to `Comparison`. The two consumers change
only their provider import. The new owner has 26 lines and six project modules in
its import closure. The classifier closure has 290 project modules and excludes
`ComparisonLaws`; both proof consumers include it. These are one-time source
observations, not new permanent checks or timing claims. The correction adds ten
physical Lean lines, including module scaffolding and the umbrella import, and
one explicit build-module registration. No test files change.

The ignored `build/comparison-boundary/selected.nix` selects only
`test_every_comparison_mutant_changes_a_verdict` from its existing Nix owner,
retaining its inputs, tools, all three mutants and deadlines. The coordinator
must point it at the final integrated source for acceptance. No Nix invocation
was made in this workspace. Final combined Nix acceptance remains pending; the
task is not DONE.

Claude reviewed implementation `3406b716` with zero must and zero should findings
in [review 20261028T153453Z](../reviews/20261028T153453Z-3406b716/review.json).
It read the move, consumer imports, registrations, documentation and status, but
did not run checks. The first response reported no findings but omitted the
required result format; its retained record is
[review 20261028T153350Z](../reviews/20261028T153350Z-3406b716/review.json).
The permitted retry returned a well-formed result and exit code 0. The source is
ready for coordinator integration and the pending Nix comparison measurement.

## Comparison correction integration

The coordinator integrated reviewed source `0a65f381` with the completed witness
retirement and CI repair. All package sources match that reviewed worker source
exactly. The theorem and executable definitions retain their original bodies;
the change is proof ownership and its imports. This record omits local diagnostic
results in accordance with the repository evidence policy. Final combined Nix
acceptance, the comparison measurement, publication and workspace cleanup remain.
Integration `23a3427b` received independent Claude review with zero must and zero
should findings (`reviews/20261028T154339Z-23a3427b/review.json`). The reviewer
confirmed the exact package-source match with `0a65f381`.
