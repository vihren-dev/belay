# Preservation foundations task status

Date: 2026-10-26. Status: IN PROGRESS; implementation accepted, retirement acceptance and integration pending.
Audience: the implementation team.
Task: [foundations and dispatch](20261026-preservation-foundations.task.md).
Specification: [ADR 0025](../docs/adr-0025-compositional-preservation-proofs.md).
Base for design evidence: `6413afe3ff50`.

## Preparation

The owner requested these specifications before assigning implementation.
The dispatch experiment gives two whole-statement proofs and four primitive
applications with the original hypotheses. It identifies the minimum import
boundary repairs. The shared
[design record](20261026-proof-simplification-design.status.md) holds Nix
evidence and independent reviews.

## Remaining work

On 2026-10-27 the owner requested detailed targets. The task now links the
source-checked ownership, primitive and dispatch inventory. Required targets
and consolidation candidates are separate; implementation has not started.

Implement the task's production consolidation and acceptance checks. The
experiment does not perform the module relocation or migrate callers. General
`Database.Every.setRows` can stay in its existing cycle-safe location; only
move definitions when the required dependency boundary needs it.

Reconciled on 2026-10-27 with main `daa15385`: include the `renamed` field and
`rewrite`/`insertSelect` cases, retaining the independent `selects` premise.
Historical dispatch experiments predate those cases. Current formula and
all-execution adapter acceptance remain implementation obligations.

Reconciled again on 2026-10-28 with main `3e2212ed`: both atom contracts now
include `dropped`, and complete dispatch includes DROP COLUMN. Preserve
`DropsCleanly`, renaming and the current separate FK rewrite conditions.
Implementation is assigned to the ADR25 foundations workspace.

## Implementation, 2026-10-28

The production consolidation is implemented; Nix acceptance and review remain.

- `EffectSatisfies` owns the effect predicate, its two introduction laws and
  the existing four-way conjunction. `RunHoldsStep` imports general execution
  definitions directly, without invariant instances.
- `TableAtomFrames` owns `TableAtom`, table quantification, row replacement,
  the append case split and empty-table append. `RowLocalAtom` extends that
  contract and supplies only the independent constraints fact. `RowLocalFrame`
  is deleted, and CREATE callers pass the inherited contract directly.
- `Database.Every.setRows` serves table-local and selected-unique-key updates.
  `TableAtomWrites` owns generic checked writes, insert outcomes and plain
  INSERT/UPDATE/DELETE. Row-local callers use those general facts; the separate
  checked-write and insert-outcome wrappers are deleted.
- Both whole-statement proofs apply `runStatement_tableAtom`. Their original
  hypotheses remain, including the row-local ADD COLUMN premise. INSERT-query
  evidence stays separate. The shared dispatch still handles every constructor,
  clean drops, renames, source failure, upsert and rule-bearing writes.
- Unused `rowsKeys_rowLocal` and `runStatement_rewrite_rowLocal` are deleted.
  Live ownership links point to the remaining files. Historical experiments stay
  at their recorded revisions.

The source import audit finds no row-local, admitted-atom, unique-key or valid-atom
instance modules in the transitive closures of `EffectSatisfies` (53 modules),
`TableAtomFrames` (101), `TableAtomWrites` (102), or `RunHoldsStep` (84).
Both replacement statement modules import the shared dispatch; neither imports
the other whole-statement module. These are one-time observations, not CI gates.

Checks before the implementation commit: `just dev-build`; focused
`docs_test.py`, `test_lean_categories.py`, `test_nix_test_targets.py`; and direct
compilation of the affected `valid_atoms_theorems_test.py`,
`admitted_atoms_statement_theorems_test.py` and `keys_unique_theorems_test.py` sources. These are local diagnostics,
not acceptance evidence. Nix results will be recorded below after review.

## Migration checks and lifetime

The existing `valid_atoms_theorems_test.py` and
`admitted_atoms_statement_theorems_test.py` now run in the existing Nix model
suite. The first contains temporary exact-formula witnesses for four primitive
replacements and the generic row-local statement theorem. The second already
contains the distinct-rowid whole-statement formula. They remain through the
last ADR25 API/context change and its Nix acceptance, then redundant formulas
and registrations can retire under ADR25 D4. No extra suite or runner was added.

Generic primitive and shared-dispatch axiom checks, independently proved atom
instances and independently different premises remain covered. The permanent
`RowLocalExamples.missingRows_preserved` regression applies generic row replacement
to a database that does not satisfy `RowsShaped`. Existing rename, DROP COLUMN,
INSERT-query, carried FAIL and engine examples remain the semantic coverage.

The current declarations of `runStatement_rowLocal` and
`runStatement_rowidsDistinct` shrink from 77 and 88 lines at assignment to 26
and 21 lines, respectively. Those counts include signatures and proof bodies,
exclude docstrings, and are not a performance claim. Three small general modules
replace the deleted frame module; the local maximum of those new modules is
130 lines. Final whole-suite Nix checks will run on the root's integrated ADR25
and ADR26 tree to avoid duplicate builds; task completion remains pending them.

Independent Claude review of `50a3d18e` reported no must findings and one
R2 should finding: the missing-row-list regression's docstring described the
general law instead of its concrete conjuncts. The follow-up states both
concrete conjuncts and points to the general `Database.EachTable.setRows` law.
The follow-up `a9002cbd` completed its development build and received zero
must and zero should findings from Claude (`20261028T112326Z-a9002cbd`).
Reviewed implementation commits are ready for the root's integrated Nix checks.

## Final-contract witness retirement

The coordinator confirmed final affected-contract Nix acceptance at
`53a346e1899f7221c67faa3c6df379862e16edb8` before this retirement.
The accepted formulas remain replayable at that revision; the
[combined acceptance record](20261028-proof-refactor-ci.status.md) records the Nix evidence.
This entry supersedes the earlier pending-acceptance notes.

The four primitive and two whole-statement migration formulas are retired:
five inline examples in `valid_atoms_theorems_test.py` and the distinct-rowid
example in `admitted_atoms_statement_theorems_test.py`. Current independent
atom contracts and all generic/instance axiom audits remain. `RowLocalExamples`
retains missing-row-list preservation without `RowsShaped` and the ADD premise;
existing write, source-failure and carried-FAIL examples remain.

Affected existing checks: `valid_atoms_theorems_test.py` and
`admitted_atoms_statement_theorems_test.py`.

Independent Claude review of `ca180788` reported zero must findings and one
should finding. The finding is fixed: these acceptance records omit local
diagnostic results, as required by `AGENTS.md`.
The coordinator integrated reviewed retirement `e3ae5e92` with the current
proof branch. Package and test sources match that reviewed retirement exactly;
the other integration changes are documentation and review records only.
Retirement Nix acceptance and push remain pending.
No production package, execution semantics or capability changes in this cleanup.
