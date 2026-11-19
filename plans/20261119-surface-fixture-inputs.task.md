# Surface suite inputs follow the fixtures each suite uses

Created 2026-11-19. Open. [Issue 438](https://github.com/vihren-dev/belay/issues/438).

Changing a private fixture changes the Nix derivation of its surface suite
alone. Changing a shared fixture changes all suites that consume it, even
when the dependency crosses a Lean import. Each suite still has the files
that its Python tests load, the Lean modules those files import and the SQL
resources read by those modules. A suite still runs all of its assigned tests.

## Acceptance

Compare the six derivation paths before and after an edit to a fixture used
by only surfaceChecks. In a separate case, change a transitive dependency
shared by suites and compare the set of changed paths with the actual
consumers. Run the surface suites on their restricted Nix sources.

The shared surfaceSuite definition is in build-support/tests.nix.
tests/nix_suites.json assigns Python tests to suites. Fixture files under
tests/surface are grouped by code ownership, and tests locate them by file
name. Some test modules also import helper functions from other test modules.
