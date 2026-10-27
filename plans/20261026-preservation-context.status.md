# Execution-condition task status

Date: 2026-10-26. Status: READY; implementation has not started.
Audience: the implementation team.
Task: [execution-aware conditions](20261026-preservation-context.task.md).
Specification: [ADR 0025](../docs/adr-0025-compositional-preservation-proofs.md).
Base for design evidence: `6413afe3ff50`.

## Preparation

The owner requested these specifications before assigning implementation.
The contextual experiment derives the two old raw-run and two old surface-run
generic formulas through one induction per executor. Boundary laws cover
composition, stopped suffixes and the additional counter-readiness check.
The shared [design record](20261026-proof-simplification-design.status.md)
holds Nix evidence and independent reviews.

## Remaining work

On 2026-10-27 the owner requested detailed targets. The task now links the
source-checked condition, induction and certificate inventory. Retained transport
and resolver bridges are explicit; implementation has not started.

Implement the new production interface, migrate evidence and callers, and
complete the task's acceptance checks. Delete old condition predicates and
parallel traversals. Experiment-only old-formula conversions must not become
production compatibility paths. Coordinate final names with API removal.
