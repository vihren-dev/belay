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

Reconciled on 2026-10-27 with main `daa15385`: the live inventory has 84 targets,
including 18 `runScriptAllFrom_` names. The earlier JSON records the historical
names only. Implement current all-execution formulas and acceptance checks;
this branch has made no production refactor.
Coordinate generic interface edits with the execution-condition task.
