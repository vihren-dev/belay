# Shared proof boundary design status

Date: 2026-10-26. Status: DONE.
Audience: the implementation team.
Task: [design task](20261026-proof-boundaries-design.task.md).
Workspace: `/home/codex/work/sqlite-verifier-proof-boundaries`.
Production baseline: `3fe5caef` (the generated dependency report).
Prior design baseline: `0cadcde9` (ADR 0025 and its checked experiments).

## Progress

- Created an isolated jj workspace with both reviewed baselines as parents.
- Recorded the current experiment/design scope immediately before assignment.
- Production implementation remains outside this task. Specifications follow
  measured prototype results; implementation task files remain deferred until
  implementation work is about to be assigned.
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
- Independent Claude review of `cc487d53` passed with no findings. The initial
  task commit `80ca2061` also passed with no findings.
- Completion-record commit `dae1686c` passed independent Claude review with no
  findings. All review records and resolutions are retained under `reviews/`.
- Completed the existing required check recipes. Production implementation and
  implementation task-file creation remain outside this completed design task.

## Evidence

Standalone Nix experiment target passed:
`/nix/store/sr7akfqnx2ry220gsis4v74dnm9y5vnr-proof-boundaries-experiments`.
It compiled 22 prototypes, their combined import, and six baseline/narrow
surface copies, without Lean warnings. All 70 requested proof-closure audits
use only the allowed standard axioms. Exact logs, paths and module closures
are retained in the output. See the [evidence record](../experiments/proof-boundaries/README.md).

## Repository acceptance

The required `just test-full`, `just verdict`, `just test-nix` and
`just test-scheduled-checks` recipes all completed successfully. Unchanged Nix
inputs reused their accepted outputs:

- Full test reports:
  `/nix/store/s6rzxwmnqyg68lrn79fmydjnlyqip7xx-sqlite-verifier-test-reports`.
- Checked public documentation:
  `/nix/store/x8scdjxfyn7dbzkgg63b2hrhazv3nh50-sqlite-verifier-public-documentation-1`.
- Conformance verdict:
  `/nix/store/pv8yv3gjwkbwli4bd5h3akpf50ysnrhi-sqlite-verifier-verdict`.
- Scheduled checks:
  `/nix/store/id752rh1ffdllb1v7dw9xszj4jbfyhy1-sqlite-verifier-scheduled-check-reports`.

The first host source-check attempt reached the existing 30-second limit for
`SyntaxEquality` during a concurrent fresh development build. After that build,
the full recipe passed with the original timeouts. No source or test change was
needed. Host recipe diagnostics are not additional semantic acceptance evidence.

The final diff against production baseline `3fe5caef` has no changes under
packages, runtime/build integration, tests, judge, integrity or conformance.
No mutants, claims, corpora or native oracle changed. Specifications are proposed
for implementation review; no production refactor is represented as delivered.

## Amendment: test lifetime, 2026-10-26

The owner approved the lean-suite recommendation. ADRs 0025 and 0026, their
implementation specifications and the existing ADR 0025 task files now separate
temporary exhaustive migration witnesses from lasting contract/semantic checks.
One shared witness set lasts through the final affected contract change; final
Nix acceptance is recorded before redundant sources and registrations retire.
Unique premise, semantic and trust coverage stays until a migrated client or
focused regression covers it. Historical experiments remain outside normal CI.

All task-file edits for this decision are batched in one commit. No new task,
runner, test manifest, CI suite or production change was introduced. Per-commit
checks use the existing `tests/docs_test.py` and independent Claude review.
The previously accepted Nix experiment and production check inputs are unchanged;
their evidence above remains applicable. Amendment review is pending.
