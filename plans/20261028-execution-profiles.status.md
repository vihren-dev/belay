# Execution profile task status

Date: 2026-10-28. Status: IN PROGRESS; implementation reviewed, Nix acceptance pending.
Audience: the implementation team.
Task: [execution observation profiles](20261028-execution-profiles.task.md).
Specification: [ADR 0026 D4](../docs/adr-0026-semantic-proof-boundaries.md).
Assignment source: `5540e15f`.

## Assignment audit

The source-agreement worker audited the current four relations, nine structural
wrappers, transport/singleton proofs and their actual consumers. Nineteen surface
modules form a disjoint production assignment from ADR 0025 conditions and D5
expression congruence. The existing execution test driver and surface package
registrations need short coordination windows.

The audit added two automation consumers: `CounterexampleActual` projects the
old relation's `actual` field, and `CheckProof` quotes the removed reflexivity
wrapper. Existing program-check tests supply acceptance for the former.
No owner-level specification decision was identified.

Fixtures requiring caller migration include `ExecutionEquivalence`,
`ExecutionComposition`, `ExecutionViewComparisons`, `ExecutionViewChoices`,
`ExecutionViewComposition`, `MigrationPatterns`, `MigrationComposition`,
`MigrationFrameBoundaries`, `MigrationApplicationComposition`,
`ApplicationRestrictedDomain` and `ApplicationWeakBridges`. Their existing
execution, migration-pattern and application drivers remain the test owners.

Assignment commit `1c56167f` passed independent Claude review with zero must
and zero should findings (`reviews/20261028T122247Z-1c56167f`). The earlier
wording finding about absence of result choices was fixed and recorded.

The worker implements this task in an isolated workspace. The sections below
record the current implementation and the acceptance work that remains.

## Implementation in progress

The common construction is `observationProfile` in `ExecutionProfile`, with shared
actual projection, component characterization, observer transport and singleton
reasoning. The four relation names now denote profile equality. Nine fixed-context
structural wrappers are removed. All 66 retained theorem headers in changed
existing production owners are unchanged, apart from whitespace. This is a source
audit, not acceptance evidence.

The caller audit added `MigrationPatternComposition`, `MigrationPatternFrames`
and six existing fixtures:
`DerivedColumnExamples`, `MigrationExpansionCounter`, `ApplicationCounterCalls`,
`S6RulesNegativeClock`, `RebuildAffinity` and `ApplicationMissingTrigger`.
The coordinator approved these formula-preserving caller changes. Scoped
simulation remains a separate representation.

Surface registration adds only `ExecutionProfile` to `Belay/Sqlite.lean` and
`lakefile.lean`. The execution driver's `InsertSelectExecutions` entry remains
owned by ADR 0025. D4 removes nine redundant wrapper audits, audits shared profile
proofs, and adds two semantic checks that reuse the existing INSERT-SELECT cases.
`ExecutionProfileMigration` holds four temporary universal formula witnesses;
retirement waits for the coordinator's Nix acceptance.

Local diagnostic commands include targeted Lake builds with one thread, the
source documentation/category/layer tests, and the affected surface test owners.
These diagnose changes only. The complete development build has run after the final
production changes. Nix acceptance, witness retirement,
integration and push remain pending.

The NOT-IN diagnostic found a real automation regression: ordinary reflexivity on
profile equality reduced different SQL runs and exhausted the existing 400,000-unit
budget before counterexample search. Reducible-only reflexivity avoided that work but
lost proofs through named aliases. `CheckProof.tryProof` now uses Lean's congruence
closing tactic for profile equality and reducible logical closing; other propositions
keep their existing tactics. No checking budget or expected counterexample changed.
The existing program checker fixture adds one named-view proof and checks the printed
suggestion again in the kernel. The unchanged NOT-IN owner checks the original failure.

Diagnostic commands run before the implementation commit:

- `just dev-build`, with two threads and a 1,200-second timeout.
- The execution and migration-pattern owners, including shared-proof axiom audits
  and the four temporary formula witnesses.
- The application, derived-column, migration-example and rebuild-affinity owners,
  plus `test_commutation_rule_refuses_a_moving_clock` from the S6 rules owner.
- `surface_s6_check_programs_test.py` and `surface_s6_not_blocked_test.py`, with
  their original budgets and a 900-second suite timeout.
- `docs_test.py`, `test_lean_categories.py` and `surface_layers_test.py`, using
  `--source-checks` and a 120-second timeout.

These local runs are diagnostics. The coordinator owns complete Nix acceptance
and its record; no Nix acceptance is claimed for this implementation yet.

Implementation commit `19e8e4c7` passed independent Claude review with zero must
and zero should findings (`reviews/20261028T133016Z-19e8e4c7`). Sources are at rest.
Retirement removes only `tests/surface/ExecutionProfileMigration.lean` and its
four-audit entry and temporary-witness sentence in `tests/surface_execution_test.py`.
The permanent `ExecutionProfileBranches`, existing `ExecutionEquivalence` and
`ExecutionViewChoices` cases retain alternate end states/errors and independent
actual/possible observations. Existing view/frame and application fixtures retain
weak/full and scoped/full distinctions. The S6 program owner retains the alias
proof and independently checked printed suggestion.

Source-size diagnostic with the baseline counter, relative to the assignment
parent: changed production files contain 32 fewer code lines; tests add 90.
The temporary formula fixture accounts for 48 of those lines. After its retirement,
this slice adds ten maintained standalone Lean code lines overall, including its
semantic regressions and shared-proof audits, plus one embedded Lean declaration for
printed-proof checking. It removes duplicated proof ownership but
does not by itself reduce the total maintained source count. No build-time
improvement is inferred from this count.
