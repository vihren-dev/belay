# Share the resolved-statement certificate

Date: 2026-10-28. Status: IN PROGRESS.
Audience: the implementation team.
Specification: [ADR 0026 D3](../docs/adr-0026-semantic-proof-boundaries.md),
[foundation requirements](../docs/spec-proof-foundations.md) and
[exact resolver targets](../docs/spec-proof-resolver-foundation-targets.md).
Record: [status](20261028-resolver-certificate.status.md).
Assignment source: `5dc38c0a`, including the reviewed preservation-context work.

This task contributes to the [Lean simplification goal](../docs/lean-simplification-goal.md)
by replacing three statement-syntax proof dispatches with one. Count the
certificate, transports, moved definitions, callers and tests together. Retain
every baseline capability and existing mathematical guarantee; no capability
loss or timing improvement is assumed.

## Required behavior

For every successful `resolveStatement`, one certificate gives three
independently conditional facts:

- The next state equals `state.after resolved`, with no validity or mode premise.
- For any supplied limits, validity of the input catalog under those limits
  implies the resolved statement's schema link to that catalog. This field
  needs neither saved-state validity nor execution mode.
- Execution mode and full input-state validity at the context profile's limits
  imply full next-state validity at those limits. Full validity includes both
  the current catalog and any saved transaction catalog.

One complete syntax dispatch proves these fields together. Reuse existing leaf
resolver facts and common catalog/write transport. Keep prepare errors, write
rule wrapping, resolved statement kind and current/saved catalog behavior.
Bundling does not add the strongest field's assumptions to the other fields.
Resolution-only mode receives no execution-mode validity guarantee.

Delete `resolveStatement_after`, `resolveStatement_schemaLink` and
`resolveStatement_valid` after migrating all callers. Their exact formulas remain
derivable through the certificate. Keep no aliases or hidden parallel dispatches,
and ensure the common proof does not invoke these replaced proofs through
helper dependencies. Retain independent leaf facts with semantic or caller value.

Cover all current syntax constructors, including RENAME TABLE/COLUMN, DROP COLUMN
and INSERT SELECT. Reuse `RenameOutcome`, `DropOutcome`, their `applyCatalog` and
`valid` facts, and `resolveInsertQuery_form`/`resolveInsertQuery_same`. Keep the
drop outcome's prepare-error alternative and successful droppable/supported
evidence. Resolved rewrite, drop-column and insert-select schema-link cases stay
vacuous; their actual catalog actions remain distinct.

Preserve `resolveStatement_applyCatalog_valid` for every resolved statement,
including transaction controls and settings. Controls leave `applyCatalog`
unchanged even when the next state's catalog or saved catalog changes. The
certificate must retain this distinction.

Keep the result/trace projection from `resolveStatementRun` through
`resolveStatementTraced` to `resolveStatement`, the existing `statement_arms`
equations and name traces. Preserve the executable/proof import boundary:
`Resolution/Resolve` imports `ResolveStatement`; proof clients import
`StatementArms` explicitly. Certificate placement must keep equation proofs out
of executable and resolver-mutant import closures. Add no parallel resolver,
trace certificate or new proof framework. SQL execution, feature scope,
conformance inputs and judge claims remain unchanged.

## Ownership and consumers

All production owners below are model modules under
`packages/belay-sqlite-model/Belay/Sqlite/Model`. Keep source files below 200 lines.
Shared prerequisites have one lower owner without copied definitions or cycles.

| Change | Owners and declarations |
| --- | --- |
| Replace complete dispatches | `Resolution/ResolveStateSpec.resolveStatement_after`, `ResolveStatementFacts.resolveStatement_schemaLink`, `ResolveStatementValid.resolveStatement_valid`. |
| Place prerequisites below the dispatch | `ResolveState.after`, `ResolveState.after_of_isControl`, `ResolveState.Valid`, `Resolved.Statement.SchemaLink`, with existing names and formulas. |
| Preserve script/catalog consumers | `ResolveStatementApplied.resolveStatement_applyCatalog_valid`, `ResolveStatementValid.resolve_valid`, `Resolution/ResolveFoldSpec.resolveFrom_after` and `resolve_after`, `ScriptRunApplied`'s database/snapshot and applied-validity bridges. |
| Migrate direct step/run consumers | `ScriptRunLaws`, `ScriptRunConstraints`, `SuccessfulScriptEffects`, `FailedStepFrame`, `PlainWriteFrame`, `ReadOnlyFrame`, `ControlStepLaws`, `PragmaStepLaws`, `ExecutionEffects`, `AdmittedRunsConditionExamples`. |

`runScriptAllFrom_admittedWith` now uses the shared execution-aware preservation
conditions. Keep its guarantee for every complete execution, including INSERT
SELECT alternatives. Existing step consumers retain `.continued output next
others`, their actual/alternative distinction and the specific premises that
establish absence of further executions. Resolver certification alone does not
prove singleton execution. Retain unconditional state equations in frame laws.

Reuse the leaf and catalog/write transports listed in the inventory, including
`Resolution/ApplyCatalogSpec` and `ResolveStatementLink`. Keep schema/script,
read-certificate and derived-column downstream claims with their existing
resolution, calmness, width, frame and per-branch assumptions.

The preservation-context worker's source is frozen at assignment. D1 owns query
outputs and shared evaluation context facts; D4 owns execution profiles and their
surface consumers. Neither overlap is required here. Coordinate model manifests
and umbrella registrations with the root. Report necessary additional callers
and resolve ownership before editing shared files.

## Acceptance checks

- Kernel-check the three original dispatch formulas and the full applied-catalog
  validity formula with their original assumptions. Keep one temporary witness
  set in existing fixtures/suites, without another runner or constructor matrix.
- Retain concise coverage of independently conditional fields: unconditional
  state equality, schema linkage at arbitrary limits and execution-mode state
  validity including saved catalogs. The universal proof covers every syntax
  constructor. Reuse existing control, rename, DROP COLUMN, INSERT SELECT,
  write-rule and trace cases; add only missing semantic or premise coverage.
- Migrate the existing `admitted_atoms_resolver_facts_test.py` owner, retaining
  independent leaf guarantees and auditing the generic proof with the existing
  axiom policy. Retire duplicate projection audits when they add no guarantee.
- Compile all affected packages, checked documentation, frame and complete-run
  consumers. Reuse `surface_schema_script_test.py`, `surface_name_trace_test.py`
  and `conformance_trace_test.py` for their existing semantic/trust boundaries.
- Inspect source/proof dependencies to verify one dispatch without replaced
  proof dependencies and the executable/mutant import boundary. Use the existing
  affected resolver-mutant check in `conformance_resolve_mutants_test.py`; its
  source-file groups retain all eleven mutants and their authored cases.
- Report net source changes including helpers, callers and tests. Apply the
  repository's check/review cadence with timeouts and the coordinator's shared
  full Nix slot. No permanent old-name or import-count gate is required.

After final Nix acceptance, retire redundant projection witnesses and their
registrations, retaining the accepted revision for replay. Keep unique semantic,
premise and trust coverage until a current consumer or focused regression supplies
it. The task is done when implementation, acceptance, retirement and records are
committed, reviewed, integrated and pushed.
