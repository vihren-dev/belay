# Preservation foundations task status

Date: 2026-10-26. Status: READY; implementation has not started.
Audience: the implementation team.
Task: [foundations and dispatch](20261026-preservation-foundations.task.md).
Specification: [ADR 0025](../docs/adr-0025-compositional-preservation-proofs.md).
Base for design evidence: `6413afe3ff50`.

## Preparation

The owner requested these specifications before assigning implementation.
The dispatch experiment gives two whole-statement proofs and four primitive
applications with the original hypotheses. It identifies the minimum import
boundary repairs. The shared
[design record](20261026-proof-simplification-design.status.md) holds Nix
evidence and independent reviews.

## Remaining work

Implement the task's production consolidation and acceptance checks. The
experiment does not perform the module relocation or migrate callers. General
`Database.Every.setRows` can stay in its existing cycle-safe location; only
move definitions when the required dependency boundary needs it.
