# Primitive ownership and surface import task status

Date: 2026-10-28. Status: READY for immediate assignment.
Audience: the implementation team.
Task: [primitive ownership and imports](20261028-proof-primitive-imports.task.md).
Specification: [ADR 0026 D6](../docs/adr-0026-semantic-proof-boundaries.md).
Production baseline: `3e2212ed`; full specification baseline: `e8f46dae`.

The owner authorized implementation of ADRs 0025/0026 on 2026-10-28. This task
is created at assignment, with a disjoint edit surface from ADR 0025 foundations.
The source audit confirmed the three current primitive owners and the three
surface umbrella imports. Historical experiments remain feasibility evidence;
current implementation and Nix acceptance are pending.

The coordinator owns shared registration coordination and permits one full Nix
acceptance run at a time. No production edits or new test infrastructure are
part of this assignment record. Update this status with every implementation
commit, final evidence, temporary-check retirement and workspace cleanup.
