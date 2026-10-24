# Status: API reference compound SELECT limit

Created 2026-10-24. Status: OPEN.
Task: [task file](20261024-reference-compound-limit.task.md).
Spec: ADR 0009 and the owner's PR #242 CI failure report.

## Current state

The owner reported that PR #241 passes and #242 fails the Linux API reference
build at 532 selected public modules. The recorded exception is in doc-gen4's
`read:transitive_imports`; its VALUES seed participates in a recursive UNION.
The intended fix preserves the root set and closure at the query boundary.
No implementation or Nix acceptance is claimed yet.

## Progress

- Created isolated workspace `reference-compound-limit` on published #242
  head `975f31eb`. Compared `.envrc`, `shell.nix`, `tools/check_resources.py`
  and `nix/dev-shell.nix` with approved S4 `c0097b21`: every `cmp` exited 0.
  Under the owner's standing authorization, `direnv allow` exited 0.
- Assigned to `s4_part1` after task review. Its S7 proof-cost prototype remains
  safely preserved in its own workspace, with no active process. The urgent
  reference fix has separate source ownership and will update the existing
  stack by descendant commits, preserving all active workspaces.

## Failure evidence and review

PR #242 Linux check: [run 40113812092, job 120930821938](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40113812092/job/120930821938).
At 2026-10-24 17:07:02 UTC, the log records:
`Exception in read:transitive_imports after 0ms: too many terms in compound SELECT (error code: 1)`.
The failed fromDb invocation has 532 public module roots. PR #243's Linux check
also failed at [run 40115952880](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40115952880).
Review `20261024T173525Z-e5ac4243` has no musts and two should findings. The
record now uses durable CI evidence and names the shell comparison/authorization
checks. Both findings are fixed; implementation scope is unchanged.

- Review `20261024T173642Z-9725e388` has no findings. The task is handed to
  `s4_part1` for the narrow dependency fix and compiled-reader regression.
  Root coordinates heavy reference builds and descendant stack integration.
