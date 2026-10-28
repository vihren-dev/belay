# Lower shared proof primitives and narrow surface imports

Date: 2026-10-28. Status: IN PROGRESS; implementation assigned.
Audience: the implementation team.
Specification: [ADR 0026 D6](../docs/adr-0026-semantic-proof-boundaries.md),
[foundation requirements](../docs/spec-proof-foundations.md) and
[exact targets](../docs/spec-proof-resolver-foundation-targets.md).
Record: [status](20261028-proof-primitive-imports.status.md).
Source baseline: `e8f46dae`, whose production packages equal main `3e2212ed`.

## Required behavior

Shared comparison and database lookup laws are available from their domain's
foundational modules without importing the features that currently own them.
Move these declarations, preserving their names and exact formulas, and remove
the old definitions:

- `Collation.compare_eq_of_binary` from `ForeignKeySelfLookup`.
- `Database.tableAt_of_table` from `AddColumnFromValid`.
- `Database.table_of_findTable` from `TableSourceLaws`.

Use existing domain owners when their dependencies and size permit it. Keep
lookup absence and row-list behavior; add no validity, admission or row-shape
premise. Migrate direct consumers to the lower owners. Each declaration has one
definition and remains available through the public model aggregation. Reuse
`LiteralData.generatedCells_plain` in its current `AdmittedCellLaws` owner.

The surface modules `Values`, `Script` and `ValueDisplay` import their actual
model providers instead of `Belay.Sqlite.Model`. Their complete declaration
bodies, checked documentation, exports, instances and registrations remain
unchanged. Downstream clients that relied on the umbrella get explicit provider
imports. Public umbrella entry points remain available. No executable SQL,
resolution, theorem formula, judge input or corpus changes are permitted.

## Ownership and relevant code

The assigned source owners are the three model files above, suitable comparison
and lookup foundations, and direct import consumers such as `PlainInsertRows`,
`TableByName` and `DerivedColumnTable`. The surface owns the three named modules
and any downstream explicit-import repairs demonstrated necessary by compilation.

`Comparison` and `DatabaseFacts` are candidate lower owners, not prescribed
destinations. The named lookup proof also needs `Resolution.CatalogSpec`; check
that its location does not introduce a reverse dependency or a broad import.
Keep modules below 200 lines and avoid a miscellaneous utility collection.

Historical provider roots are `Comparison`, `Declarations`, `StoreValue`,
`StoreValueLaws`, `Truth` for `Values`; `Declarations`, `Resolution.Syntax`,
`SqlAdvance` for `Script`; and `Declarations`, `OutputRepr` for `ValueDisplay`.
Keep the latter's Lean delaborator import. Current compilation, including
attributes and syntax, decides sufficiency.

ADR 0025 foundations proceeds in a separate workspace. Its `AdmittedPlainWrites`,
`RowLocal*`, `RowEngineFacts`, `RunHoldsStep`, atom contracts and preservation
proofs are outside this worker's edit surface. Unchanged theorem names and lower
imports in the former owners keep those clients usable. Coordinate additive
`Model.lean` and `lakefile.toml` registrations with the coordinator before editing
them. Ask for coordination before any newly required overlapping edit.

## Acceptance checks

- Nix compiles the relocated declarations with exactly their previous formulas
  and their model/surface consumers. Inspect imports to establish that the lower
  owners do not depend on the former feature owners. No duplicate proof body or
  compatibility alias remains.
- Nix compiles the complete surface and checked public documentation. Existing
  surface tests cover literal/coercion instances, Script append and bound values,
  value display and the integer unexpander. Reuse them before adding a check.
  Explicit-import repairs must preserve exported names and attributes.
- Measure before/after project import closures for the three surface modules
  with the same scope as the historical experiment. Report net source changes
  including new owners, caller imports and test changes. These are one-time
  observations, not permanent thresholds or claims of faster builds.
- Apply the repository's per-edit, per-commit, end-of-slice and end-of-task check
  cadence. Commands have configured timeouts. Full Nix suites use the coordinator's
  shared build slot. No affected mutant table or runtime semantics is changed.

Use existing package, documentation and surface Nix suite owners. Keep only
checks of distinct repository contracts. Duplicate formula probes and baseline/
narrow module copies are temporary; record final Nix acceptance and remove
redundant active witnesses before completion. Preserve any unique premise or
trust check until a current consumer or focused regression covers it. Historical
experiments stay replayable at their recorded revisions, outside normal CI.

The task is done when the changes and required acceptance evidence are committed,
independently reviewed, integrated without conflicting ownership and pushed.
Resolver certificates, query outputs, source/expression agreement and execution
profiles are separate ADR 0026 assignments, not delivered by this task.
