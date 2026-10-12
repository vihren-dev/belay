# Verifier library as a package

Created 2026-10-12. Status: NOT STARTED.
Decision: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md),
section 7, stage 1. Proposed; this task starts after the owner accepts the ADR.
Depends on: [case folders](20261012-case-manifests-and-lean-categories.task.md)
and [Lake builds in the verifier](20261012-lake-builds-in-the-verifier.task.md).

## Outcome

1. All Lean code that is not a case, a direct fixture or excluded is in a Lake
   package under `packages/<name>/`, each with its own `lakefile.toml`:
   - the verifier library (`SqliteVerifier`, `SqliteVerifier.lean`);
   - the gate, bundle checker and exporter executables with `GateCore` and
     `GatePaths`, in the verifier package or a package of their own;
   - the test-only conformance library and runner (`VerifierConformance`,
     `ConformanceRunner.lean`);
   - the documentation tool (`tools/PublicDocInventory.lean`,
     `tools/PublicDocSyntax.lean`).
2. Each package is built by its own Nix derivation, which depends on the
   derivations of the packages it requires. Its output is the package's Lake
   workspace, which Lake replays without compiling.
3. The category test of the case-manifest task no longer lists package sources
   outside `packages/`.
4. The shipped runtime, the API reference, the documentation inventory and all
   test targets build from the new locations. Public module names do not
   change.

## Tests

- The category test with the explicit package list removed.
- A Nix check that each package derivation's output, required by a generated
  workspace, compiles no module of that package.
- The existing runtime, API reference and documentation inventory builds, and
  all Nix test targets, pass.
- The pages of the API reference for our modules are the same as before,
  except for source links that now name the new paths.

## Relevant source and constraints

- `lakefile.toml` (root) declares `SqliteVerifier`, `EngineeringExamples`,
  `GatePaths`, `GateCore`, the three executables, `VerifierConformance` and
  `conformance-runner`, and requires `lean4export` and `belaySqlite`.
- `build-support/default.nix` (`leanRuntime`, `conformanceRuntime`,
  `inventoryTools`), `build-support/runtime.nix`, `build-support/sources.nix`,
  `build-support/api-reference*.nix` and `build-support/public-documentation.nix`
  name today's paths.
- `tools/api_reference.py` builds source links from file paths; links of
  public modules change with the move.
- `packages/belay-sqlite` is the model for a package's layout and Nix build
  (`build-support/model-package.nix`).
- `docs/`, `README.md` and `AGENTS.md` name source paths; they change in the
  same commit as the code (CLAUDE.md, "Replaced code").
