# Primitive ownership and surface import task status

Date: 2026-10-28. Status: IN PROGRESS; acceptance and integration pending.
Audience: the implementation team.
Task: [primitive ownership and imports](20261028-proof-primitive-imports.task.md).
Specification: [ADR 0026 D6](../docs/adr-0026-semantic-proof-boundaries.md).
Production baseline: `3e2212ed`; assignment baseline: `3ef94b97`.

## Implementation

The owner authorized implementation of ADRs 0025/0026 on 2026-10-28. This task
has a disjoint edit surface from ADR 0025 foundations. The coordinator released
the shared model aggregation and manifest for additive registrations.

- `Collation.compare_eq_of_binary` now belongs to `Comparison`.
- `Database.tableAt_of_table` now belongs to `Database`, next to `Database.table`.
- `Database.table_of_findTable` now belongs to `DatabaseLookup`, whose imports
  are `Database` and `Resolution.CatalogSpec`.

The three declaration statements and proof bodies are identical to the assignment
baseline. Former owners import the lower provider, and direct consumers use the
lower imports. `Database.tableAt_of_table` stays separate from the named lookup:
it needs no resolver proof imports. The three owners' project import closures
contain 5, 42 and 245 modules respectively, including each owner; none contains
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

The coordinator will combine the independently reviewed implementation with
ADR 0025 and the separately owned acceptance repair, then run the required
Nix package, surface, checked documentation, full-suite, verdict, Nix-source and
scheduled-check gates once on that integrated source. No mutant table changes.

No active duplicate proof witness, baseline/narrow source copy, import-count
check or new test framework was added. Historical experiments remain replayable
at their recorded revisions, outside normal CI. Current package compilation and
existing surface fixtures supply the retained contract coverage after acceptance.
Independent review, final Nix evidence, integration, push and workspace cleanup
remain pending. This task is not DONE.
