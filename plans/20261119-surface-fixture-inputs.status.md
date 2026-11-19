# Status of surface suite inputs

Created 2026-11-19. DONE. [Task](20261119-surface-fixture-inputs.task.md).

Each suite declares the fixtures that its Python tests open. The Nix source
includes the transitive Lean imports and SQL resources of those fixtures.
tests/test_source_identity_derivations.py compares all six derivation paths.
Changing CheckConsumerSize changes only surfaceChecks. Changing the shared
LowercaseFilters fixture changes surface, surfaceClaims and surfaceS6.
Python helpers now load SqlFileProbe on demand so other suites can import
the helpers with their restricted fixture tree. The proof-cost run reached
its independent timing limit, recorded in issue 453.

Review clarified the SQL resource list, the identity check and why the probe
is read on demand. The root list includes the literal INSERT fixture from issue 419.

The second review found no issues. The six restricted suites are included
in the full Nix test target.

The complete Nix run found a missing SqlFileProbe in surfaceS6.
surface_sql_check_roots_test.py builds a same-name project through a Python
helper that reads this Lean file. Both consuming suites now list the probe.
The derivation-identity regression covers its two consumers. The Nix
verdict passed for this layer. All 70 tests passed in the corrected
S6 suite. The full Nix test target passed with all six restricted surface
suites: surface, surfaceChecks, surfaceClaims, surfaceProofCost, surfaceS6
and surfaceSelect. The Nix host tests and scheduled checks also passed on
the combined stack.
