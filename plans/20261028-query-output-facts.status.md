# Query output task status

Date: 2026-10-28. Status: IN PROGRESS; assignment review pending.
Audience: the implementation team.
Task: [generalize query output proofs](20261028-query-output-facts.task.md).
Specification: [ADR 0026 D1](../docs/adr-0026-semantic-proof-boundaries.md).
Assignment source: `a3dd5a9a`, after expression-congruence integration.

## Assignment audit

The expression-congruence worker inspected the current endpoint signatures,
actual consumers and test owners. All 45 target statements match `3e2212ed`:
21 model and 24 surface endpoints. The task records the seven model owners,
nine surface endpoint owners, unique-lookup consumer and lower semantic owners.
No owner-level specification decision was identified.

The audit found eleven direct maintained fixture callers and no removed-name
references in `CheckProof`, `CounterexampleActual`, SQL automation or simp
registrations. D4 and ADR 0025 conditions remain disjoint. Shared model/surface
registrations require coordination; the frozen expression work releases the
claims driver and shared context modules to this task.

The weaker no-error and optional-window formulas remain acceptance obligations.
The historical count/aggregate prototype does not establish their coverage.
No current implementation, Nix acceptance or line reduction is recorded yet.

Pending: assignment review, implementation, original-formula checks, independent
review, Nix acceptance, temporary witness retirement, integration and push.
