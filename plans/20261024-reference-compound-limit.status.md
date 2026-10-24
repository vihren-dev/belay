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
  head `975f31eb`. Its dev-shell configuration matches approved S4; the owner's
  standing authorization covers it. Shell authorization succeeded.
- Assigned to `s4_part1` after task review. Its S7 proof-cost prototype remains
  safely preserved in its own workspace, with no active process. The urgent
  reference fix has separate source ownership and will update the existing
  stack by descendant commits, preserving all active workspaces.
