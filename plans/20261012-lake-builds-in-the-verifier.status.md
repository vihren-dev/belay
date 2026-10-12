# Status: Lake builds in the verifier

Created 2026-10-12. Status: READY.
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
