# Proof simplification experiments and implementation specifications

Date: 2026-10-26. Status: DONE. Audience: the implementation team.
Owner request: create a separate workspace, run experiments, and prepare ADRs
and tasks for simplifying the model's theorem and proof API before implementation.
Record: [design record](20261026-proof-simplification-design.status.md).

## Required outcome

The design has reproducible, kernel-checked experiments for replacing specialized
preservation endpoints with generic applications, sharing table-atom statement
dispatch, and expressing execution conditions with the inputs they need. Each
experiment states what it establishes and what remains unproved. Nix checks
provide the acceptance evidence. Production packages remain unchanged.

The resulting ADR and implementation tasks specify observable guarantees,
acceptance checks, dependency boundaries, deletion scope, and semantic traps.
Tasks describe outcomes, not an implementation procedure. They distinguish
measured removals from estimates and avoid promises about build speed without
measurements. The owner explicitly requested these implementation specifications;
preparing them now does not start or assign their implementation.

## Checks

The experiment check compiles representative old formulas through the proposed
generic API and audits their axioms. Shared statement proofs must retain their
current hypotheses. Contextual run proofs must account for stopped suffixes,
saved transaction databases, and the different readiness obligations of raw and
surface execution. A rejected generalization is recorded as such.

Each completed specification is independently reviewed against the repository
checklist. Links and cited definitions are checked against the frozen base.
Existing conformance claims, judge inputs, executable semantics and CI targets
are outside this design task.

## Relevant code and constraints

The base is integration commit `6413afe3ff50`, in the separate jj workspace
`sqlite-verifier-proof-simplification`. Concurrent name-trace work is not part
of this frozen base and must be considered when implementation is integrated.

The main proof families are `RunHolds`, `RunHoldsReady`, `ScriptRunHolds`,
`ScriptRunDerived`, `AdmittedTableAtomStatement`, `RowLocalStatement`,
`AdmittedDistinctStatement`, `RowLocalFrame`, and `AdmittedAtomFrames`, under
`packages/belay-sqlite-model/Belay/Sqlite/Model`.

ADR 0022 and older task files require some named endpoints. The proposed
replacement must identify the exact superseded obligations. Independent atoms,
conditional foreign-key laws, partial FAIL, rollback snapshots, and useful raw
resolved-statement claims remain available. There are no compatibility aliases.

The experiments reuse existing abstractions where possible. A new generic
framework, interpreter rewrite, package split, and general foreign-key engine
refactor require evidence beyond deleting wrapper theorems and are outside scope.
