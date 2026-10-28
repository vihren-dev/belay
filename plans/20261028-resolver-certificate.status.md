# Resolver certificate task status

Date: 2026-10-28. Status: IN PROGRESS.
Audience: the implementation team.
Task: [shared resolved-statement certificate](20261028-resolver-certificate.task.md).
Specification: [ADR 0026 D3](../docs/adr-0026-semantic-proof-boundaries.md).
Assignment source: `5dc38c0a`, including preservation-context implementation
`1773d573` and its reviewed handoff `5a0c9b32`.

## Assignment audit

The coordinator read the three current dispatches, applied-catalog and
complete-run consumers, statement equations, direct-call search and existing
resolver test owner. The three independent premises, control/saved-catalog
distinction and source/trace split match the governing specification.

The direct-call inventory matches the current source. The preservation-context
implementation changes its shared condition application but retains the
schema-link consumer and every-complete-execution guarantee. No owner-level
specification decision was identified.

The task reuses the existing admitted-resolver, schema/script, name-trace,
conformance-trace and resolver-mutant test owners. The CI repair now partitions
eleven resolver mutants into six source-file groups without dropping cases.
No new runner or permanent per-constructor test matrix is assigned.

Assignment commit `969b6d77` passed independent Claude review with zero must and
zero should findings (`reviews/20261028T130545Z-969b6d77`). The prior review's
status-heading ambiguity was fixed and recorded. Documentation source checks
passed. The assigned worker completed its source audit and found no mismatch;
implementation is released. No implementation acceptance is recorded yet.

Pending: implementation, independent review, original-formula checks, Nix
acceptance, temporary witness retirement, integration and push.
