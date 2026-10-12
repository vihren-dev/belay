# Status: Lake builds in the verifier

Created 2026-10-12. Status: NOT STARTED.
Task: [task](20261012-lake-builds-in-the-verifier.task.md).
ADR: [ADR 0010](../docs/adr-0010-lake-builds-and-artifact-cache.md), proposed.

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
