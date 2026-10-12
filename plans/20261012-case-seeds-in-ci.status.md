# Status: case seeds in CI

Created 2026-10-12. Status: NOT STARTED.
Task: [task](20261012-case-seeds-in-ci.task.md).
ADR: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md), proposed.

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
