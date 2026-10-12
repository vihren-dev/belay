# Case seeds in CI

Created 2026-10-12. Status: NOT STARTED.
Decision: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md),
sections 8 and 9. Proposed; this task starts after the owner accepts the ADR.
Depends on: [case folders](20261012-case-manifests-and-lean-categories.task.md)
and [Lake builds in the verifier](20261012-lake-builds-in-the-verifier.task.md).

## Outcome

1. Nix has one seed derivation for each case folder, found from the folders
   and their `case.toml` files, not from a list in a Nix file. A seed runs
   `prepare` and then `verify-bundle` on its case with one cache in a temporary
   directory, then `lake cache stage` into its output, so it holds the outputs
   of both the proofs project and `verify-bundle`'s workspace.
2. Each Nix test target that runs `prepare` or `verify-bundle` takes the seeds
   of the cases its tests use. Tests of the deprecated `verify` take none.
   Before its tests start, it unstages them into one writable cache in its
   `$TMPDIR`. The tests pass that cache to the verifier through the child
   environment (`runtime_environment` in `conftest.py`).
3. A test that runs a case unchanged compiles no Lean module. A test that
   changes a case compiles only the changed modules.
4. A named set of tests runs with `--no-cache` and ignores the seeds.
5. A test checks that the pinned `lean --version` reports the toolchain's
   commit hash, not only a release tag.
6. A change to one case rebuilds only that case's seed and the targets that use
   it. Seeds are kept in the saved CI cache like other build outputs.
7. Host runs of `just test-cases` use a persistent cache under `build/`.

## Tests

- A Nix check (in the existing Nix test of test targets): every case folder has
  a seed derivation, and each verifier target depends on the seeds of the cases
  its tests use.
- In a verifier target: after unstaging, running each unchanged case reports
  zero compiled modules. The verifier must report the number of compiled
  modules in its JSON output or a log that the test can read.
- The toolchain commit test of item 5.
- The `--no-cache` set of item 4 passes.
- Hosted CI: one run of a pull request that changes no Lean or case file, and
  one that changes one case, with target times recorded in the status file.

## Relevant source and constraints

- Targets and their inputs: `build-support/tests.nix`, `tests/nix_suites.json`,
  `tests/test_nix_test_targets.py`. `just test` builds `developmentTests`.
- Cache saving in CI: `tools/ci_store_gc.py` and `.github/workflows/ci.yml`;
  only successful `main` jobs save.
- `lake cache unstage` must run inside a generated workspace, because Lake
  stores mappings for each package (`experiments/lake-cache/seed_flow.py`).
- `experiments/lake-cache/seed.nix` is a working prototype: a seed derivation
  and a second derivation that unstages it and builds fresh copies with zero
  compiled modules, in the Nix sandbox (experiment finding 16).
- Read-only caches fail on a miss when the workspace enables the cache; the
  target needs a writable copy (experiment finding 8).
- Lake's key includes module and package names, so seeds must be produced by
  the verifier's own commands, not by a hand-written workspace.
- A seed depends on the runtime and the Python code that generates
  `SchemaInputs` and `SqlInputs`; targets already rebuild on those changes.
- The kernel suite compiles its fixtures directly (`tests/kernel_gate`); it
  takes no seed.
- [ledger/ledger#3270](https://github.com/ledger/ledger/pull/3270): a Lean
  built by Nix that reports a tag gets no cache hits.
