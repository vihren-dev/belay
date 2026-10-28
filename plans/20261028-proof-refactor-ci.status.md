# Proof refactor acceptance repair status

Date: 2026-10-28. Status: READY for immediate assignment.
Audience: the implementation team.
Task: [restore acceptance checks](20261028-proof-refactor-ci.task.md).
Source baseline: PR 295, `e8f46dae`; production `3e2212ed`.

The coordinator fetched the failed Linux check and resolver mutant job logs.
The installed-layout helper's read-only links and the timed-out combined mutant
test are confirmed source boundaries; the shared-library rebuild cause still
needs diagnosis. This is separate from the active ADR25/26 production edits.

API-reference build and verdict passed on PR 295. The other CI results do not
establish acceptance of the failing suites. Implementation, independent review,
Nix verification and subsequent hosted verification remain pending.

The existing native-artifact task requires dependency replay; its producing
shared facets already exist. The new task explicitly retains that requirement,
including shared-library replay, rather than allowing a writable fixture to
hide invalid artifact traces. Documentation checks passed before task commit.
