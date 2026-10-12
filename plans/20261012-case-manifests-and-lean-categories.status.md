# Status: case folders and Lean file categories

Created 2026-10-12. Status: READY.
Task: [task](20261012-case-manifests-and-lean-categories.task.md).
ADR: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md), accepted.

Relevant files: `conftest.py`, `tests/cli_test.py`, `tests/bundle_test.py`, `tests/atuin_cli_test.py`,
`tests/proof_exporter_test.py`, `tests/runtime_package_test.py`,
`tests/generated_inputs_test.py`, `tests/test_application_keys.py`,
`experiments/adr-0003-latency/cases.py`, `build-support/tests.nix`,
`build-support/runtime.nix`, `build-support/sources.nix`, `examples/`.

## Progress

- 2026-10-12: task and status files created with ADR 0010 (PR #76). Work
  starts after the owner accepts the ADR.
- 2026-10-12: updated with ADR 0010: `verify` is deprecated (owner decision)
  and out of scope; `prepare` builds the user's proofs project; cases take the
  layout of a user's project.
- 2026-10-12: ADR 0010 accepted with the owner's decisions; the task is
  ready. CI times are recorded from the first pull request (section 11).
- 2026-10-12: the case file is `belay.toml`, the tool's project configuration
  file, with test-only data in a `[test]` table (owner decision).
- 2026-10-12: started after PR #76 merged. The task's test list said that
  paths leaving the case folder are refused, which contradicts item 6 (no Lean
  file moves) because three cases share `examples/approved/`. The owner
  decided: paths may leave the case folder but must stay inside the folder
  that holds the cases. The task text says so now.
- 2026-10-12: implemented on top of `main` `0adb73dc`.
  - `migration_check/project_config.py` reads and validates `belay.toml`
    (`load`, `discover`, `case_names`); `tests/test_project_config.py`.
  - A `belay.toml` in each of the six checked-in cases; `[test]` holds the
    expected status and the Nix target (`suite`, `cli` by default; Atuin is
    `atuin`).
  - `cli_test.py`: one test, parametrized from the runtime's `examples/`,
    replaces the four per-case status tests. `runtime_package_test.py` does the
    same for the installed archive. `atuin_cli_test.py`, `bundle_test.py`,
    `proof_exporter_test.py`, `model_roots_test.py`,
    `generated_inputs_test.py` and `experiments/adr-0003-latency/cases.py`
    take case inputs from `belay.toml`. `test_application_keys.py` runs no
    example case and is unchanged.
  - `tests/test_lean_categories.py`: every `.lean` file is in exactly one
    category; a stray file in `examples/` is reported.
  - Nix: the reader is in every target's common inputs; the `bundle` target
    gets `examples/` because `cases.py` reads it.
  - Review: two rounds with "must" findings in the reader (a list status
    raised `TypeError`; path-like module names escaped the root; then tests
    that passed without the fix), all fixed; the third round had none.
- 2026-10-12: CI baseline (ADR 0010 section 11), successful `main` runs, scope
  `package`, Nix cache restored:

  | Run | Commit | Linux | macOS |
  | --- | --- | --- | --- |
  | 38243172224 | `0adb73dc` | 467 s | 1366 s |
  | 38238221252 | `de61b7c5` | 885 s | 1679 s |

  The reference for this task's pull request is `0adb73dc`. The `docs`
  scope takes about 10 s and is not compared.
