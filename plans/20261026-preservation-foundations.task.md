# Consolidate preservation foundations and table-atom dispatch

Date: 2026-10-26. Status: READY; implementation has not started.
Audience: the implementation team.
Specification: [ADR 0025 D2 and D4](../docs/adr-0025-compositional-preservation-proofs.md).
Record: [status](20261026-preservation-foundations.status.md).
Targets: [ownership, primitive and dispatch inventory](../docs/spec-preservation-proof-targets.md).
Present problem: repeated statement case analyses and backwards proof imports
prevent use of the general lemmas already in the model.

## Required behavior

The general effect/database preservation facts are available below the
invariant instances that use them. `TableAtom` owns the shared empty/sublist
contract. Row-local evidence supplies those facts and its constraint fact;
it does not maintain a second independent implementation of the frame laws.

The existing general `Database.Every.setRows` proof serves both table-local
and catalog/position-dependent uses. The row-local checked-write and insert
outcome claims use the existing general results. Replaced implementations
are deleted, and callers use the remaining primitives or meaningful evidence.

The table-atom statement theorem owns the full constructor dispatch for both
the row-local and distinct-rowid families. Both old whole-statement formulas
remain derivable with precisely their original hypotheses. Their bodies no
longer duplicate the complete statement match. Atoms still supply the local
ADD COLUMN, plain-write and row-engine facts their preservation needs.

Imports are acyclic. Foundational primitives do not import the invariant
instances that they serve. No blanket admitted-database, row-shape or readiness
premise is added to make the layering easier. Modules stay below 200 lines.

## Acceptance checks

- Nix compiles exact-formula checks for both old whole-statement guarantees,
  including arbitrary clock/counters/parameters and all statement constructors.
  The replacement proofs do not call the old whole-statement proofs. Their
  closures use only the existing standard axioms.
- Nix compiles the four primitive replacement formulas from
  `DispatchPrimitives.lean`: table-local and unique-key row replacement,
  row-local checked writes, and row-local insert outcomes. Preserve the missing
  row-list behavior supported by `Database.Every.setRows`; no `RowsShaped`
  premise may be introduced.
- Existing atom statement/engine examples and theorem suites pass for all
  affected invariant families, including success and carried constraint FAIL.
  Existing native conformance behavior is unchanged.
- Inspect the production import graph: general frame/write modules are below
  the specialized facts, and neither removed whole-statement implementation
  is a hidden dependency of its replacement. Delete obsolete roots and imports.
- Report the resulting proof bodies, modules and dependency changes. The
  experiment compares two declarations totaling 139 lines with replacements
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

`AdmittedAtomFrames` imports `RowLocalFrame`, which imports `RowLocalAtoms`.
`AdmittedPlainWrites` imports `RowLocalWrites`. Simply importing the general
modules back into those older files creates cycles. Relocate their existing
general contracts and proofs to a lower dependency layer as necessary.

`AdmittedTableAtomStatement`, `RowLocalStatement` and
`AdmittedDistinctStatement` contain the relevant statement analyses.
`RowEngineFacts`, `RowLocalFrame`, `KeysUniqueFrame`, `RowLocalWrites` and
`AdmittedPlainWrites` contain the primitive candidates. The experiment proves
formula compatibility; it does not perform the production module relocation.

Unique keys need catalog-selected keys, and foreign keys need cross-table
relationships and intermediate counter facts. Their whole statement/engine
proofs are not required to become `TableAtom` instances. Generalizing those
engines, executable semantics and package boundaries is outside this task.
