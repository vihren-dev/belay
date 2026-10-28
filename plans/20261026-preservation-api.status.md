# Preservation API task status

Date: 2026-10-26. Status: IN PROGRESS; implementation accepted, retirement review and integration pending.
Audience: the implementation team.
Task: [API replacement](20261026-preservation-api.task.md).
Specification: [ADR 0025](../docs/adr-0025-compositional-preservation-proofs.md).
Base for design evidence: `6413afe3ff50`.

## Preparation

The owner requested these specifications before assigning implementation.
The API experiment derives 11 representative formulas using existing generic
rules and records 84 candidate removals. The shared
[design record](20261026-proof-simplification-design.status.md) holds the Nix
evidence and independent reviews. It does not certify a completed migration.

## Historical preparation, 2026-10-27 through assignment

On 2026-10-27 the owner requested detailed targets. The task now links the
source-checked endpoint, predicate and caller inventory. Implementation remains
unassigned; this refinement changes no production code or acceptance policy.

Reconciled on 2026-10-27 with main `daa15385`: the live inventory has 84 targets,
including 18 `runScriptAllFrom_` names. The earlier JSON records the historical
names only. Implement current all-execution formulas and acceptance checks;
this branch has made no production refactor.
Coordinate generic interface edits with the execution-condition task.

Reconciled again on 2026-10-28 with main `3e2212ed`. The 84 names remain;
their current DROP COLUMN and FK rename premises govern migration acceptance.
Implementation remains unassigned.

## Implementation, 2026-10-28

Assigned after reviewed foundations integration `85ef8387`; the implementation
workspace is `sqlite-verifier-adr25-api`. Production source migration is complete; acceptance remains pending.
The earlier preparation notes describe the unassigned specification stage.

- Removed all 84 inventoried endpoints and six pure-wrapper modules, including
  their root imports and Lake entries. No compatibility aliases remain.
- Replaced the five unique-key effect/state/outcome declarations and six
  duplicated run-condition declarations with the generic predicates and laws.
  Database/table uniqueness and distinct statement conditions remain.
- Migrated the six production endpoint callers, FK semantic examples, checked
  references and live owner links. The Valid helpers retain every complete
  surface execution; the additional invariant helper remains generic.
- Captured the 84 current declarations and checked their signatures against
  `3e2212ed6983` before deletion. Four anonymous fixture files restate them through
  generic applications. The only formula substitutions expand removed aliases;
  support, admission, fixed/selected mappings and all-execution premises remain.

## Migration checks and retirement

`tests/surface/PreservationApiWitnesses1.lean` through `PreservationApiWitnesses4.lean`
contain exactly one witness per retired endpoint, with the former name in a comment.
The existing `valid_atoms_theorems_test.py` compiles them in the existing model
suite; `build-support/tests.nix` adds only those four inputs. No suite or runner
is added. The generated `ATOMS` × run-prefix matrix and the other old endpoint
checks are removed now, so they do not duplicate these witnesses.

Keep this set through the execution-condition task's final Nix acceptance,
record that exact revision, then delete its four source inputs and parameterized
compile check. The five foundation witnesses remain shared until that point.
Lasting coverage consists of generic proof/primitive audits, independently
proved invariant evidence, whole-statement atom contracts with their distinct
premises, the four used Valid contracts, uniqueness lookup and semantic fixtures
for FAIL, rollback, missing saved-state invariants and fixed/selected FK mappings.
Existing rename, DROP COLUMN and INSERT-query cases remain unchanged.

## Validation and acceptance

Checks before the implementation commit: `just dev-build`; the four existing
model theorem test files (`valid_atoms_theorems_test.py`,
`keys_unique_theorems_test.py`, `admitted_atoms_run_theorems_test.py`,
`admitted_atoms_statement_theorems_test.py`); the five changed FK surface fixtures;
`docs_test.py`, `surface_layers_test.py`, `test_test_ownership.py`,
`test_lean_categories.py` and `test_nix_test_targets.py`. These are local
diagnostics, not acceptance evidence. An additional broad `test_source_identity.py`
selection exceeded its 90-second outer command bound without a reported assertion
failure; it is outside this change's targeted checks. The root coordinates the
integrated Nix gates; this task remains IN PROGRESS until their results are recorded.

The production delta against assignment revision `85ef8387` is 95 fewer named
declarations, six fewer modules and 1,207 fewer textual Lean lines (including
comments and blanks). The four temporary fixtures add 683 textual Lean lines
outside production, and replace the old duplicate matrices. These are source
size observations, not the goal's scc metric or a claim about build speed.
No execution semantics or capability was removed.

Independent Claude review of `5c0fdaf5` reported zero must findings and two
R19 should findings. The follow-up labels the old unassigned notes as historical
and states that the model suite now compiles the four temporary witnesses.
The historical experiment imports remain at their recorded revision and are
explicitly outside the active-source deletion check.

The documentation follow-up `69c431c4` passed its documentation diagnostic and
independent Claude review with zero must and zero should findings
(`20261028T115625Z-69c431c4`). Both findings from the implementation review are
recorded as fixed. The reviewed changes are ready for the root's integrated
Nix acceptance; the shared migration fixtures remain in place.

## Final-contract witness retirement

The coordinator confirmed final affected-contract Nix acceptance at
`53a346e1899f7221c67faa3c6df379862e16edb8` before this retirement.
The accepted formulas remain replayable at that revision; the
[combined acceptance record](20261028-proof-refactor-ci.status.md) records the Nix evidence.
This entry supersedes the earlier pending-acceptance notes.

The four `PreservationApiWitnesses` fixtures and both frozen-condition helpers
are retired with `test_preservation_api_migration`. The model suite again uses
`modelInputs` without those six additions; its existing test owners remain.
Independent atom premises, actual raw/surface clients, validity helpers,
selected-FK mapping, failure and transaction examples retain their coverage.

Affected existing checks: `valid_atoms_theorems_test.py`,
`admitted_atoms_statement_theorems_test.py` and Nix test-source selection.

The cleanup removes only temporary fixtures and their inputs. A bounded diagnostic
run checked the six changed Python test owners plus `test_test_ownership.py` and
`docs_test.py`: 34 cases passed. It used independent copies of the coordinator's
compiled libraries with `LEAN_NUM_THREADS=2`; it is not Nix acceptance.
The log is `/tmp/adr25-26-retirement-diagnostics.log`.

Retirement Nix acceptance, independent review, integration and push remain pending.
No production package, execution semantics or capability changes in this cleanup.
