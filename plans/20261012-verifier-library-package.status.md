# Status: verifier library as a package

Created 2026-10-12. Status: DONE (2026-10-13).
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
- 2026-10-12: documentation tool in `packages/public-doc-tools` (`docTools`).
  `tools/public_doc_inventory.py` takes the built package (`--tools`) instead
  of compiling `PublicDocSyntax` itself, so its fixture test moved from the
  host checks to the new Nix suite `documentation`. The inventory of the
  public library is the same as before, apart from source paths (482
  authored, all checked). The category test now has `packages/` as its only
  package rule. Checks: suites `documentation` 12 and `packages` 5 passed,
  `just test-source` 533 (12 tests moved), host Nix tests 84.

- 2026-10-12: PR #100 (base `tasks/adr10-case-seeds`). CI at `590da027`:
  Linux 892 s, macOS 6 s (checks skipped on pull requests). PR #99: 900 s;
  baseline `main` `0adb73dc`: 467 s. Like #99, the run rebuilds what the
  unmerged PRs #95 and #96 change, because the CI cache is saved only on
  `main`; this task adds no time. Compare again after the merges.
- 2026-10-12: GitHub merged #100 into `tasks/adr10-case-seeds`, so PR #99
  carries tasks 3 and 4. Merged `main` (#97, ADR 0008 step 1b) into it.
  #97 changed Lean files that this task moved; the move did not change
  their contents, so `main`'s versions went to the new paths. New modules:
  `GateInputs` (library, `packages/sqlite-verifier`), `migration-resolver`
  (executable, `packages/verifier-gate`, shipped in `leanRuntime`) and
  `VerifierConformance.Native`. All Nix test suites, `just test-source` 465
  and host Nix tests 84 pass. `conformanceCoverage` fails on `main` too:
  #97 removed `Case.names`, which `conformance/instrument_model.py` still
  inserts into the runner; not changed here.
- 2026-10-13: DONE. PR #99 merged into `main` as `6c9ec7a6`. CI on `main`:
  Linux 1043 s, macOS 1717 s. The run before it (`1a606217`, #97): Linux
  765 s, macOS 1693 s; the ADR's baseline (`0adb73dc`): Linux 467 s, macOS
  1366 s. Linux is +278 s over #97, above the 20 % limit; investigated:
  - Both runs rebuilt the Lean runtime from an empty cache, because both
    commits change Lean sources. This run also built every new package
    derivation, `lean4export` and the six seeds for the first time.
  - Suites that this work does not change were 30 % to 65 % slower in this
    run (146 tests: 99 → 136 s; 27 tests: 75 → 123 s; host Nix tests:
    38 → 74 s), so most of the increase is load from the first-time builds
    that run next to them, not slower tests.
  - The recurring cost needs a run with a warm cache. The agent app cannot
    re-run workflows, and a manual run selects all checks. Open: compare the
    next `main` run that changes code with this one, and investigate if
    Linux stays above 918 s (765 s + 20 %).
- 2026-10-13: warm measurement. `main` `c844e1c5` (#101, judge claims, no
  Lean change), scope `package`, the same suites as the baseline run
  (`0adb73dc`): Linux 592 s (baseline 467 s, +125 s), macOS 1276 s (1366 s).
  Linux is just above the threshold (2 minutes). Causes:
  - host Nix tests 27 → 59 s (65 → 84 tests): the new evaluation tests of
    seeds and packages evaluate the real runtime derivations (tasks 3, 4);
  - installed acceptance 63 → 96 s: installed `prepare` runs Lake and the
    audit (task 2);
  - harness 69 → 94 s (56 → 68 tests): #97, not ADR 0010.
  Accepted for now. A follow-up can make the evaluation tests cheaper, for
  example by evaluating the seed and target derivations in one Nix call.
