# Shared proof boundary design status

Date: 2026-10-26. Status: ACTIVE.
Audience: the implementation team.
Task: [design task](20261026-proof-boundaries-design.task.md).
Workspace: `/home/codex/work/sqlite-verifier-proof-boundaries`.
Production baseline: `3fe5caef` (the generated dependency report).
Prior design baseline: `0cadcde9` (ADR 0025 and its checked experiments).

## Progress

- Created an isolated jj workspace with both reviewed baselines as parents.
- Recorded the current experiment/design scope immediately before assignment.
- Production implementation remains outside this task. Specifications will
  follow measured prototype results; implementation task files are deferred
  until implementation work is about to be assigned.
- Completed seven candidate assessments and authored proposed ADR 0026 plus
  three outcome specifications. Adopt query outputs, source agreement, resolver
  certification, observation profiles and the demonstrated import moves. Narrow
  expression work to congruence. Defer the row-engine abstraction after both
  prototypes added interface/witness complexity.
- A second review caught an extra non-control premise in the applied-catalog
  witness. The corrected witness handles controls and retains the full original
  formula. All experiment sources are at rest.
- Independent Claude review of `771604b5` found no must findings and two should
  findings. Clarified the owner's present import-cleanup request and the boundary
  with ADR 0025; recorded both resolutions. No experimental source changed.

## Evidence

Standalone Nix experiment target passed:
`/nix/store/sr7akfqnx2ry220gsis4v74dnm9y5vnr-proof-boundaries-experiments`.
It compiled 22 prototypes, their combined import, and six baseline/narrow
surface copies, without Lean warnings. All 70 requested proof-closure audits
use only the allowed standard axioms. Exact logs, paths and module closures
are retained in the output. See the [evidence record](../experiments/proof-boundaries/README.md).

The production packages, runtime/build integration, tests, judge and conformance
inputs remain unchanged. Independent commit review and final existing Nix
checks are pending; this design task is not yet marked DONE.
