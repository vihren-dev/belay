# Status: Lake builds in the verifier

Created 2026-10-12. Status: DONE (2026-10-13).
Task: [task](20261012-lake-builds-in-the-verifier.task.md).
ADR: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md), accepted.

Relevant files: `migration_check/compile.py`, `migration_check/contract.py`,
`migration_check/prepare.py`, `migration_check/bundle.py`,
`migration_check/source_closure.py`, `migration_check/import_path.py`,
`migration_check/runtime.py`, `migration_check/process.py`,
`migration_check/stage_store.py`, `migration_check/cache_eligibility.py`,
`build-support/default.nix`, `build-support/runtime.nix`, `examples/`,
`docs/trust-boundary.md`, `docs/adr-0003-agent-proof-preparation.md`.

## Progress

- 2026-10-12: task and status files created with ADR 0010 (PR #76). Work
  starts after the owner accepts the ADR.
- 2026-10-12: updated with ADR 0010: `verify` is deprecated (owner decision)
  and out of scope; `prepare` builds the user's proofs project; cases take the
  layout of a user's project.
- 2026-10-12: ADR 0010 section 10 added: generate, check and export phases;
  the check is `lake build` with a generated `Check` module and an audit
  command. Outcome item 4 and the audit and loop-speed tests added.
- 2026-10-12: experiment round two (`experiments/lake-cache/`, findings 11–16)
  confirmed the design; the task records the prototypes and the measured
  numbers.
- 2026-10-12: ADR 0010 accepted with the owner's decisions; the task is
  ready. CI times are recorded from the first pull request (section 11).
- 2026-10-12: started, stacked on the case-folder task's branch (PR #95).
  Implementation steps: (A) runtime ships Lake library packages; (B) a
  bounded Lake workspace builder; (C) `verify-bundle` builds the contract
  with Lake; (D) `prepare` builds the user's proofs project, and the cases
  become proofs projects; (E) cache options and clean command; (F) the
  elaboration warning; (G) generate, check, audit and export phases with
  the shared allowlist; (H) remove the stage store; documentation.
- 2026-10-12: design findings while implementing:
  - Lake has no option that bounds its parallel jobs (`lake build --help`
    lists none); to be resolved in step H or recorded as a limit.
  - A proofs project's lakefile must require the runtime by a path that
    differs per machine. `prepare` keeps a project-relative symbolic link,
    `.belay/runtime`, that points at the installation; the lakefile requires
    `.belay/runtime`, so it is portable and the examples work after a copy.
    Lake resolves a symbolically linked package (checked).
  - Lake knows only the modules that a library lists in `roots` or `globs`;
    helper modules in the same folder are not found (checked with Atuin's
    contract). The proofs project's lakefile therefore lists every contract
    and candidate module, and `prepare` reports a missing one with the fix.
  - `run_process` admits `LAKE_CACHE_DIR` in addition to `LEAN_PATH` and
    `LEAN_SYSROOT`; Lake finds `lean` without `PATH`.
  - Tests give each child its own `BELAY_CACHE_DIR` (`conftest.py`), so no
    test writes to the user's cache.
- 2026-10-12: steps A–E done in one commit (they share the CLI and the Nix
  inputs):
  - A: `build-support/library_lakefile.py` writes the runtime's library-only
    lakefile from the root `lakefile.toml`; `leanRuntime` keeps `ir`; the model
    package copy turns the cache off. `tests/lake_runtime_package_test.py`: a
    workspace requiring the installed runtime compiles no library module.
  - B: `migration_check/lake_workspace.py` (lakefile text, bounded
    `lake build`, compiled and failed modules from Lake's output).
  - C: `verify-bundle` builds the contract and `SchemaInputs` with Lake
    (`migration_check/contract_build.py`) and reports `compiled_modules`.
  - D: `prepare --project` builds the user's proofs project; `init` creates
    one; the six checked-in cases are proofs projects (lakefile and
    `lean-toolchain`; `.belay/` and `Generated/` are ignored and pruned from
    Nix sources). `module_keys.py` and its test are removed.
  - E: `--cache`, `--no-cache`, `BELAY_CACHE_DIR`, the per-user default with a
    subfolder per runtime build (`migration_check/cache_location.py`), and
    `clean-cache`.
  - Checks: Nix targets `cli`, `atuin`, `bundle` (72 passed); `just
    test-source` (549 passed); installed package tests on `build/runtime`
    (14 passed; `test_installed_gc_roots` needs a real archive install).
  - Docs: `data-path.md`, `install.md`, `source-staging.md`,
    `trust-boundary.md`.
  - Remaining: F (elaboration warning), G (phases, audit, shared allowlist),
    H (remove the stage store and eligibility registry; batched header
    reading; the parallel-jobs bound).
- 2026-10-12: step F done: `prepare` reports approved commands that run code
  during elaboration (`migration_check/elaboration_commands.py`) in
  `warnings` and prints them; `tests/prepare_warning_test.py` (bundle target,
  74 passed).
- 2026-10-12: step G done:
  - `SqliteVerifier/AxiomPolicy.lean` holds `allowedAxioms`, which
    `GateCore.lean` and the new `SqliteVerifier/Audit.lean` (`#belay_audit`)
    both read. Only `Audit` imports `Lean`.
  - Commands `generate`, `check`, `audit`, `export` (`project_phases.py`,
    `project_discovery.py`, `cli_project.py`); `prepare` runs them and audits
    before it exports; `export` alone does not audit, so a bundle from other
    tools still reaches `verify-bundle`, the judge.
  - The audit module `Check` is generated; its library `Audit` is not a
    default target. `generate` refuses `debug.skipKernelTC` in the lakefile.
  - CODEOWNERS: `SqliteVerifier/AxiomPolicy.lean`, `contract_build.py`,
    `lake_workspace.py` and `project_phases.py` join the product trust base
    (owner review in the pull request).
  - Checks: Nix targets `bundle` (81 passed), `cli`, `atuin`, `kernel`; `just
    documentation-inventory`; `just test-source` (554 passed).
- 2026-10-12: step H:
  - `StageStore`, `MIGRATION_CHECK_STAGE_STORE`, the measurement override,
    `cache_eligibility.py`, `tests/test_stage_store.py` and
    `tests/stage_reuse_test.py` are removed; the deprecated `verify` compiles
    freshly. ADR 0003's "Approved contract reuse" points to ADR 0010; the
    trust boundary, source staging and data path documents follow.
  - Batched header reading (item 5) was already on `main`
    (`fc3c3d5d`, `migration_check/lean_headers.py`): one `lean --deps-json`
    process per discovery round, each header read once per process.
  - Parallel jobs: Lake has no jobs option, but `LEAN_NUM_THREADS` bounds its
    thread pool (Atuin from an empty cache: 4.75 s default, 5.57 s with two
    threads, 8.97 s with one). `lake_build` sets it to the processor count,
    at most 8.
  - New tests: separate agent and verifier caches, warm cache against
    `--no-cache` for every checked-in case (`tests/cache_domains_test.py`), a
    compile error naming the module, a Lake build stopped at its deadline.
- 2026-10-12: loop timing with the real commands (Linux x86_64, 8
  processors, warm cache, installed `build/runtime`):

  | | small | Atuin |
  | --- | --- | --- |
  | `check` after a proof edit | 0.61–0.65 s | 0.62–0.66 s |
  | `audit` | 1.00 s | 1.12 s |
  | `prepare` after a proof edit (all phases) | 1.99 s | 2.21 s |
  | first `prepare`, empty cache | 3.06 s | 7.37 s |

  The per-edit loop (`check`) is about 0.6 s against 1.4–2.0 s for the old
  `prepare`; about 0.25 s of it is Python start and runtime checks, so `lake
  build` in the project is faster still (0.34–0.46 s in the experiment). A full
  `prepare` after an edit is slightly slower than the old one (it adds the
  audit and Lake's overhead); the fast path is `check`. macOS was not
  measured: the macOS CI job skips its checks on pull requests.
- 2026-10-12: all outcome items and tests of the task are in place; the pull
  request records its CI times (ADR 0010 section 11).
- 2026-10-12: CI of PR #96 (run 38254870761, `package`): Linux 928 s against
  the 467 s baseline (+461 s, +99 %). Investigated: the Lean library rebuilt
  once (new `SqliteVerifier.AxiomPolicy` and `Audit`, changed `GateCore.lean`),
  and the `bundle` target took 374 s for 86 tests against 210 s for 69 in
  PR #95 (+164 s; mostly `cache_domains_test`, the phase tests and the audit in
  `prepare`). Recorded on the pull request; the case-seed task addresses the
  recurring part. Owner approved PR #95 and PR #96 on 2026-10-12.
- 2026-10-13: DONE. The owner approved and PR #96 merged into `main` on
  2026-10-12. CI times after all four ADR 0010 tasks: see the library package
  status file.
