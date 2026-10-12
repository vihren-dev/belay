# Status: verifier library as a package

Created 2026-10-12. Status: READY.
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
