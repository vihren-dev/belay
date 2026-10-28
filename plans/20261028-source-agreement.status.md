# Source agreement task status

Date: 2026-10-28. Status: IN PROGRESS; assignment review pending.
Audience: the implementation team.
Task: [shared query source agreement](20261028-source-agreement.task.md).
Specification: [ADR 0026 D2](../docs/adr-0026-semantic-proof-boundaries.md).
Source baseline: `81163254`; original source formulas match `3e2212ed`.

## Assignment

The owner authorized ADR 0025/0026 implementation on 2026-10-28. This task is
assigned to the primitive/import worker after its integration build. Its source
owners are disjoint from the ADR 0025 API worker and the CI repair worker.
Shared manifests and Nix source registrations require coordinator sequencing.

The inventory has fourteen source helpers and three additional query endpoints.
The two statement-context endpoints are included in the fourteen. Current and
initial origin paths differ in their read adapters; the shared traversal must
retain complete lookup and pragma observations. Existing two-state tests are
the acceptance owner. No task implementation or Nix acceptance is recorded yet.

## Progress and evidence

- Assignment: inspected the three current source files, lower read predicates,
  exact target inventory and existing two-state test helper/axiom list.
- Pending: implementation, independent review, Nix acceptance, temporary
  migration-witness retirement, integration and push.
