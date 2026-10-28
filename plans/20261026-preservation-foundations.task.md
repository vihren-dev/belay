# Consolidate preservation foundations and table-atom dispatch

Date: 2026-10-26. Status: DONE on publication of this reviewed completion record.
Completion: [final acceptance record](20261026-preservation-foundations.status.md#completion-record).
Audience: the implementation team.
Specification: [ADR 0025 D2 and D4](../docs/adr-0025-compositional-preservation-proofs.md).
Record: [status](20261026-preservation-foundations.status.md).
Targets: [ownership, primitive and dispatch inventory](../docs/spec-preservation-proof-targets.md).
Baseline reviewed 2026-10-28: production revision `3e2212ed6983`.
Present problem: repeated statement case analyses and backwards proof imports
prevent use of the general lemmas already in the model.

## Required behavior

The general effect/database preservation facts are available below the
invariant instances that use them. `TableAtom` owns the shared empty/sublist/rename/drop
contract. Rename agreement means equal rows and equal `blankNames` shapes.
The drop field preserves the atom under `Table.dropColumn` when the table's
shape satisfies `CatalogTable.DropsCleanly`; it is distinct from row deletion.
Row-local evidence supplies those facts and its constraint fact;
it does not maintain a second independent implementation of the frame laws.

The existing general `Database.Every.setRows` proof serves both table-local
and catalog/position-dependent uses. The row-local checked-write and insert
outcome claims use the existing general results. Replaced implementations
are deleted, and callers use the remaining primitives or meaningful evidence.

The table-atom statement theorem owns the full constructor dispatch for both
the row-local and distinct-rowid families. Both old whole-statement formulas
remain derivable with precisely their original hypotheses. Their bodies no
longer duplicate the complete statement match. Atoms still supply the local
ADD/DROP COLUMN, INSERT-query, plain-write and row-engine facts their preservation needs.
The complete dispatch includes `rewrite`, `dropColumn` and `insertSelect`. Its independent
`selects` premise covers INSERT from a query without rules. Keep the existing
source-failure and upsert evidence, and the rule-bearing write behavior.

Imports are acyclic. Foundational primitives do not import the invariant
instances that they serve. No blanket admitted-database, row-shape or readiness
premise is added to make the layering easier. Modules stay below 200 lines.

## Acceptance checks

- Nix compiles exact-formula checks for both `3e2212ed6983` whole-statement guarantees,
  including arbitrary clock/counters/parameters and all statement constructors.
  These formulas concern the canonical `.effect`; their all-effects lifting in
  `InsertSelectKeeps` must remain available to preservation certificates.
  The replacement proofs do not call the old whole-statement proofs. Their
  closures use only the existing standard axioms.
- Nix compiles the four primitive replacement formulas from
  `DispatchPrimitives.lean`: table-local and unique-key row replacement,
  row-local checked writes, and row-local insert outcomes. Preserve the missing
  row-list behavior supported by `Database.Every.setRows`; no `RowsShaped`
  premise may be introduced.
- Existing atom statement/engine examples and theorem suites pass for all
  affected invariant families, including rename, DROP COLUMN, INSERT-query
  source failure, success and carried constraint FAIL. Reuse existing semantic
  examples and native column-drop conformance; do not add a per-atom DROP matrix.
  Existing native conformance behavior is unchanged.
- Inspect the production import graph: general frame/write modules are below
  the specialized facts, and neither removed whole-statement implementation
  is a hidden dependency of its replacement. Delete obsolete roots and imports.
- Report the resulting proof bodies, modules and dependency changes. The
  historical experiment compares two declarations totaling 139 lines with replacements
  totaling 39 lines plus a 4-line adapter; this is feasibility evidence, not a required formatting
  target or a performance claim.

Use the existing Nix test suites and repository check cadence, with bounded
commands. Production package edits require the local development build as
specified in `AGENTS.md`; local diagnostics are not acceptance evidence.

## Test lifetime

The old whole-statement and four primitive replacement witnesses, dependency
inspection and source measurements are migration acceptance work under ADR
0025 D4. Universal proofs cover all statement constructors; this does not
require a new example for each constructor. After final Nix acceptance, retire
duplicate witnesses covered by the generic proof contracts and migrated clients.
Keep focused checks for independent atom premises, missing row-list behavior
without `RowsShaped`, success and carried FAIL wherever existing coverage is
insufficient. Keep axiom coverage of generic proofs and independent instances.
Record retirement in the existing status file and use existing suites only.

## Relevant code and design constraints

At assignment, `AdmittedAtomFrames` imported `RowLocalFrame`, which imported
`RowLocalAtoms`, and `AdmittedPlainWrites` imported `RowLocalWrites`. Adding the
reverse imports would create cycles. The implementation moves these general
contracts to `EffectSatisfies`, `TableAtomFrames` and `TableAtomWrites`.

`AdmittedTableAtomStatement`, `RowLocalStatement` and
`AdmittedDistinctStatement` contain the relevant statement analyses.
`RowEngineFacts`, `TableAtomFrames`, `KeysUniqueFrame`, `RowLocalWrites` and
`TableAtomWrites` contain the remaining primitive owners and consumers. `StatementRewrite`,
`StatementDropColumn` and `InsertSelectLaws` supply the newer leaf evidence.
Rename execution now checks only `sameOutline`; selected FK parent equality
is a separate caller premise. DROP COLUMN uses `runsDropColumn` and the
`dropped`/`renamed` table fields. Preserve these boundaries. The historical experiment
predates those statement forms; it does not establish current dispatch formulas
or perform the production module relocation. Recheck the four primitive formulas.

Unique keys need catalog-selected keys, and foreign keys need cross-table
relationships and intermediate counter facts. Their whole statement/engine
proofs are not required to become `TableAtom` instances. Generalizing those
engines, executable semantics and package boundaries is outside this task.
