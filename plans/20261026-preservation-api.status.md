# Preservation API task status

Date: 2026-10-26. Status: READY; implementation has not started.
Audience: the implementation team.
Task: [API replacement](20261026-preservation-api.task.md).
Specification: [ADR 0025](../docs/adr-0025-compositional-preservation-proofs.md).
Base for design evidence: `6413afe3ff50`.

## Preparation

The owner requested these specifications before assigning implementation.
The API experiment derives 11 representative formulas using existing generic
rules and records 84 candidate removals. The shared
[design record](20261026-proof-simplification-design.status.md) holds the Nix
evidence and independent reviews. It does not certify a completed migration.

## Remaining work

On 2026-10-27 the owner requested detailed targets. The task now links the
source-checked endpoint, predicate and caller inventory. Implementation remains
unassigned; this refinement changes no production code or acceptance policy.

Implement all outcomes and acceptance checks in the task. Reconcile the frozen
inventory with the selected integration revision, including concurrent
name-trace work. No production code, caller or public endpoint has changed yet.
Coordinate generic interface edits with the execution-condition task.
