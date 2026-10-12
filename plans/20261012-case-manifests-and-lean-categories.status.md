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
