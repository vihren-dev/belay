# Status: ADR17 guide and integrated acceptance

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-adr17-guide-acceptance.task.md).
Specs: ADR17 and its accepted decisions; explicit ADR deferrals remain in force.

## Prerequisites

All required feature tasks and their Nix acceptance precede this final gate.
S4, query sources and FK work are active. S5, S7 files, editor and doc-block
tasks are specified. S6 production execution contracts are reviewed; remaining
S6 assertions/patterns/automation and S8 await their tasks. The owner accepted
observation views, contextual S8 pairing, the fresh-run helper and the separately
named interface-scoped simulation.
Proof-cost production needs the specified collector experiment.

The product default workspace contains earlier unpublished S2/S3 guide edits.
Published profile/header corrections and current S4 guide edits use separate
workspaces. Final publication must reconcile those relevant changes without
including unrelated private history or copying private contents publicly.

## Progress

- 2026-10-24: specified a final capability and guide audit, installed-consumer
  integration, proof checks and publication boundary. Review is pending.
  ADR17 remains OPEN; this task file claims no completed feature or test result.
- 2026-10-24: review `20261024T145218Z-e244461b` has no findings.
- 2026-10-24: review `20261024T145825Z-2e5e2ef5` found one should:
  update the task's conditional wording after the view and S8 decisions were
  accepted. The task now names those accepted contracts and the separate
  still-pending fresh-run helper decision.
