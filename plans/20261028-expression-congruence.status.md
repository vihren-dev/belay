# Expression congruence task status

Date: 2026-10-28. Status: IN PROGRESS; assignment review pending.
Audience: the implementation team.
Task: [shared expression congruence](20261028-expression-congruence.task.md).
Specification: [ADR 0026 D5](../docs/adr-0026-semantic-proof-boundaries.md).
Source baseline: `9ead5e38`; original target formulas match `3e2212ed`.

## Assignment

The owner authorized ADR 0025/0026 implementation on 2026-10-28. This task is
assigned to the CI repair worker after its reviewed handoff. It owns expression
congruence and its direct consumers, disjoint from the active atom-preservation
and source-agreement workers. Shared registrations require coordinator sequencing.

## Progress and evidence

- Assignment: inspected all four current target proofs, their direct consumers,
  the existing claims fixture runner and the historical expression experiment.
  Confirmed the target files have no source difference from `3e2212ed`.
- Pending: implementation, independent review, Nix acceptance, temporary
  witness retirement, integration and push. No implementation acceptance is
  recorded by the historical experiment.
