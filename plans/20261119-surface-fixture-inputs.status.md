# Status of surface suite inputs

Created 2026-11-19. Open. [Task](20261119-surface-fixture-inputs.task.md).

Each suite declares the fixtures that its Python tests open. The Nix source
includes the transitive Lean imports and SQL resources of those fixtures.
tests/test_source_identity_derivations.py compares all six derivation paths.
Changing CheckConsumerSize changes only surfaceChecks. Changing the shared
LowercaseFilters fixture changes surface, surfaceClaims and surfaceS6.
Python helpers now load SqlFileProbe on demand so other suites can import
the helpers with their restricted fixture tree. The proof-cost run reached
its independent timing limit, recorded in issue 453. Whole-suite checks
and independent code review are pending.
