# Status: verifier library as a package

Created 2026-10-12. Status: IN PROGRESS.
Task: [task](20261012-verifier-library-package.task.md).
ADR: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md), accepted.

Relevant files: `lakefile.toml`, `SqliteVerifier/`, `SqliteVerifier.lean`, `GateCore.lean`,
`GatePaths.lean`, `ProofChecker.lean`, `BundleChecker.lean`, `ProofExporter.lean`,
`VerifierConformance/`, `ConformanceRunner.lean`, `tools/PublicDoc*.lean`,
`build-support/default.nix`, `build-support/runtime.nix`,
`build-support/sources.nix`, `build-support/api-reference*.nix`,
`build-support/public-documentation.nix`, `build-support/model-package.nix`,
`tools/api_reference.py`.

## Progress

- 2026-10-12: task and status files created with ADR 0010 (PR #76). Work
  starts after the owner accepts the ADR.
- 2026-10-12: updated with ADR 0010: `verify` is deprecated (owner decision)
  and out of scope; `prepare` builds the user's proofs project; cases take the
  layout of a user's project.
- 2026-10-12: ADR 0010 accepted with the owner's decisions; the task is
  ready. CI times are recorded from the first pull request (section 11).
- 2026-10-12: started, stacked on PR #99 (task 3).
  - Layout: `packages/sqlite-verifier` (library, engineering examples,
    `GatePaths`, `GateCore`), `packages/verifier-gate` (the three executables;
    requires the library and `lean4export`), `packages/verifier-conformance`
    (conformance library and runner; requires only the model). The root
    `lakefile.toml` and `lake-manifest.json` are gone; the root
    `lean-toolchain` stays as the pin that `lean-toolchain.nix` reads.
  - Decision: the installed runtime keeps its layout (`.lake/build` at the root,
    `packages/belay-sqlite`), so `runtime.py`, the conformance tools and the
    tests that read it do not change. `library_lakefile.py` now copies the
    package's lakefile and moves its requirement to the runtime's folder.
  - `build-support/lean-package.nix` builds each package (and `lean4export`,
    and the model, replacing `model-package.nix`) in a copy of the repository
    layout. Lean modules compile only in their own package; a consumer that
    links an executable compiles only the C objects of what it imports.
    `leanRuntime` and `conformanceRuntime` assemble outputs; the API
    reference and the documentation inventory read the built library.
  - Replay check: suite `packages` (`tests/lean_packages_test.py`) builds the
    libraries and the executables' root modules of each package output in a
    workspace that requires it. It found that the `Export` library target
    does not build `Export.Parse`; `lean4exportPackage` now builds it.
  - API reference: built from the task 3 state and from the new layout; the
    16 changed pages differ only in the `packages/sqlite-verifier/` prefix of
    their source links.
  - Checks: all 12 Nix test targets pass, `just test-source` 545,
    host Nix tests 79, `apiReferenceBase` and `publicDocumentation` build.
  - Not changed: `judge/compare.py` and `judge/outputs.py` name
    `VerifierConformance/*.lean` in docstrings about history; the judge lock
    covers them, so a change needs its own owner-approved pull request.
  - Found while checking: since task 2, `just test-cases` with the checkout
    as runtime root cannot build proofs projects (the root is not a complete
    Lake package); use `SQLITE_VERIFIER_RUNTIME_ROOT=build/runtime`.
  - Next: the documentation tool package, then the category test without
    exceptions.

