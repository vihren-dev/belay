# Status: case seeds in CI

Created 2026-10-12. Status: READY.
Task: [task](20261012-case-seeds-in-ci.task.md).
ADR: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md), accepted.

Relevant files: `build-support/tests.nix`, `tests/nix_suites.json`,
`tests/test_nix_test_targets.py`, `conftest.py`, `tools/ci_store_gc.py`,
`.github/workflows/ci.yml`, `justfile`, `experiments/lake-cache/seed_flow.py`.

## Progress

- 2026-10-12: task and status files created with ADR 0010 (PR #76). Work
  starts after the owner accepts the ADR.
- 2026-10-12: updated with ADR 0010: `verify` is deprecated (owner decision)
  and out of scope; `prepare` builds the user's proofs project; cases take the
  layout of a user's project.
- 2026-10-12: experiment round two (`experiments/lake-cache/`, findings 11–16)
  confirmed the design; the task records the prototypes and the measured
  numbers.
- 2026-10-12: ADR 0010 accepted with the owner's decisions; the task is
  ready. CI times are recorded from the first pull request (section 11).
- 2026-10-12: started, stacked on PR #96.
  - Design choice (told to the owner): a seed's output is the Lake cache
    folder that `prepare` and `verify-bundle` filled; a test target merges
    the seeds by copying them into one writable cache. `lake cache unstage`
    needs a workspace whose package name matches each mapping file, so the
    staged form would need dummy workspaces. The copy depends on Lake's cache
    layout; the test that unchanged cases compile nothing fails if an upgrade
    changes it.
  - `build-support/case-seeds.nix` and `case_seed.py`: one seed per case
    folder, with only the files its `belay.toml` names as inputs; the seed
    requires the case's expected status.
  - `tests.nix`: `suite` takes `seeds`; the `bundle` target copies them into
    `$TMPDIR/lake-cache` and sets `BELAY_TEST_CACHE` and `BELAY_TEST_SEEDED`.
    `conftest.py` gives children that cache; `just test-cases` keeps one
    under `build/lake-test-cache`. Tests that need a cold cache pass
    `--cache` themselves.
  - Tests: `tests/case_seeds_test.py` (unchanged cases compile nothing),
    the toolchain commit check, and Nix evaluation tests (one seed per case
    folder; a case change rebuilds only its seed). The CI store tool keeps
    seeds already: it roots the test targets with `keep-outputs`.
  - Checks: Nix target `bundle` with seeds 93 passed in 176 s (229 s for 86
    tests before the seeds, locally); `cli` 17, `atuin` 12; `just test-source`
    544 passed. `verify-bundle` now reports `compiled_modules` for a
    refutation too (`Rejection` details), so the refutation case can be checked.
  - Review of the first commit (3 "should" findings, fixed): the runtime held
    all examples, so one case change rebuilt every seed. Seeds now build with
    `seedRuntime`, the runtime without `examples/`; the Nix evaluation tests
    use the real runtimes. With that runtime, Atuin's `Check` missed the
    cache: `discover_sources` kept imports in a set, so the module order of
    the generated audit module changed with Python's string hashing. The
    graph now keeps import order; `project_phases_test.py` pins Atuin's order.
    `bundle` 94 passed in 174 s; `just test-source` 544 passed.
  - Fix: `tests/test_source_identity.py` checks the exact attributes of
    `sources.nix`; it now includes `runtimeWithoutExamples`. `just test-nix`
    68 passed.
