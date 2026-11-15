# Status: a root Lake package, so that Reservoir can index Belay, and version 0.2.0

Created 2026-11-14. Task: `20261114-root-package-for-reservoir.task.md`. Owner request, 2026-11-14.
Status: DONE (2026-11-15).

## References

- Specifications: ADR 0006 (the model package), ADR 0010 section 7 (build categories), ADR 0016 D2
  and D3 (layers and names), ADR 0021 (the removed product and its tags), ADR 0023 fact 8 (Nix
  workspaces).
- The surface package: `packages/belay/lakefile.lean`, `packages/belay/lake-manifest.json`.
- Tests and helpers: `tests/test_lean_categories.py`, `tests/surface_support.py`,
  `tests/sql_file_support.py`, `tests/runtime_fixtures.py`, `tests/test_source_identity.py`,
  `tests/surface_layers_test.py`, `tests/test_nix_test_targets.py`.
- Nix: `build-support/default.nix`, `build-support/sources.nix`, `build-support/tests.nix`.
- User instructions: `README.md`, `examples/table-rebuild/README.md`,
  `skills/belay/templates/lakefile.toml`, `skills/belay/SKILL.md`, `packages/belay/README.md`.
- Reservoir: <https://reservoir.lean-lang.org/inclusion-criteria>; the indexer is in
  <https://github.com/leanprover/reservoir> (`scripts/testbed-analyze.py`).
- Prototype: jj change `mxzxnpzq` (local, not for merge).

## Progress

- 2026-11-14: prototype and owner decisions 1 to 5; task and status files.
- 2026-11-15, implementation plan (informal): (1) rename the surface package to `belaySurface` and
  its callers; (2) the root package (`lakefile.toml`, `lake-manifest.json`, `BelayRoot.lean`), its
  source identity `rootPackage` in `build-support/sources.nix`, its files in `surfaceRoot`, and the
  tests; (3) the user documents and the ADR amendments; (4) the end-of-task checks.
- 2026-11-15: choices where the task leaves room. The root module is `BelayRoot` in
  `BelayRoot.lean` of the top-level folder, a direct fixture with its own category rule. The
  version tags are `{ all = [{ startsWith = "v" }, { not = { startsWith = "v0.1." } }] }`: Lake's
  TOML accepts a preset only at the top level of the pattern, so `verLike` cannot be combined with
  the exclusion. `surfaceRoot` links the files of `sources.rootPackage` at their paths, and
  `root_layout` in `tests/surface_root_package_test.py` copies them into the layout of the tests.
  The root manifest pins Plausible as a `git` package; the layout pins it by the path of the
  surface's Nix output, because the sandbox has no network (the same localization as
  `surfacePackage` in `build-support/default.nix`). The Reservoir form of the requirement is
  `scope = "vihren-dev"` with `rev = "v0.2.0"`: Lake 5.0 looks up a requirement with a scope and no
  source on Reservoir (`Lake/Load/Materialize.lean`).
- 2026-11-15: `lean_libraries` (`tests/runtime_fixtures.py`) now requires
  `ConformanceRunner.olean` in the runtime's library folder, because in the repository that folder
  also holds the build of the root package.
- 2026-11-15, commit "refactor(surface): rename the surface package to belaySurface": the
  lakefile, the manifest, `tests/surface_support.py` (`libbelaySurface_Belay`), the requirements of
  `tests/sql_file_support.py` and of the example. The stale `libbelay_Belay.so` files of this
  workspace's build folder were deleted. Review: one "should" finding (R13, the user documents
  still show the old requirement); fixed by the commit "docs: require Belay from the repository root".
- 2026-11-15, commit "feat: a root Lake package for Reservoir": `lakefile.toml`,
  `lake-manifest.json`, `BelayRoot.lean`, `sources.rootPackage`, `surfaceRoot`, the fixture
  `lean_libraries`, and the tests `tests/surface_root_package_test.py` (surface suite),
  `tests/test_root_package.py` (host), `tests/test_lean_categories.py` and
  `tests/test_source_identity.py`.
- 2026-11-15, commit "refactor(tests): test that lean_libraries requires the runner module": the
  review of the root package commit found no test for the new requirement of `lean_libraries`
  (R11, should). `tests/test_pytest_harness.py` now runs a probe with a runtime root whose library
  folder has only `BelayRoot.olean`. The second finding of that review (R13, should: the documents)
  is fixed by the commit "docs: require Belay from the repository root". Its review found one
  "should" (R19: the status said "fixed" before the documents commit existed); fixed by the same
  commit.
- 2026-11-15, commit "docs: require Belay from the repository root": `README.md` ("Install"),
  `examples/table-rebuild/README.md` and `skills/belay/templates/lakefile.toml` show the `git`
  requirement on the repository root with `rev = "v0.2.0"` and the Reservoir form
  (`scope = "vihren-dev"`); the README says that the Reservoir form works only after Reservoir
  lists the package. `packages/belay/README.md` names the package `belaySurface`. Dated
  amendments: ADR 0010 section 7, ADR 0016 D3 and ADR 0023 (the `subDir` text).
  `skills/belay/SKILL.md` needs no change: Lake clones the root requirement into
  `.lake/packages/belay`, so its paths stay correct.
- 2026-11-15, end-of-task checks on commit 1cf11947 ("docs: require Belay from the repository
  root"), after a passing `just dev-build`: `just test-full` passed on its second run (all suites,
  among them `surface` with `tests/surface_root_package_test.py`). Its first run failed in
  `surfaceChecks`: `test_consumer_size_claim_is_false_and_replays` gave "SQL check: unknown; the
  search reached its time limit" under a load average of about 11; the rerun of that suite passed
  (32 tests). `just verdict` passed (5,768 AGREE and 2,100 MODEL_UNSUPPORTED, no disagreement). `just test-nix`
  passed (98 tests) and `just test-scheduled-checks` passed.
- 2026-11-15: DONE. The tag `v0.2.0`, the GitHub release and the Reservoir listing are not in this
  task: the owner creates the tag after the pull request is on `main`.
