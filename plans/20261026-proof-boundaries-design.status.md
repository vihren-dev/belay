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

## Historical experiment evidence, 2026-10-26

Standalone Nix experiment target passed:
`/nix/store/sr7akfqnx2ry220gsis4v74dnm9y5vnr-proof-boundaries-experiments`.
It compiled 22 prototypes, their combined import, and six baseline/narrow
surface copies, without Lean warnings. All 70 requested proof-closure audits
use only the allowed standard axioms. Exact logs, paths and module closures
are retained in the output. See the [evidence record](../experiments/proof-boundaries/README.md).

## Historical repository acceptance, 2026-10-26

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
their evidence above remains applicable. Claude reviewed `b5d92aeb` with no
must findings and one should finding: date the owner-approved amendment in
the ADR text itself. Both ADRs now contain that date; the resolution is recorded.
Claude reviewed clarification commit `03d0f498` with no findings. Amendment
review is complete; production and experiment inputs remain unchanged.

## Amendment: grouped implementation targets, 2026-10-27

The owner requested concrete files, theorem names and propositions grouped by
the change to attempt. Added five linked inventories across ADRs 0025 and 0026:
preservation API removals/callers; preservation proof foundations/conditions;
query/observation changes; source/expression agreement; resolver/foundation
changes. They enumerate required replacements, retained facts, definition moves,
direct callers, reused evidence and deferred row-engine work separately.

Names and owners were checked against the unchanged production revision
`3fe5caef`; the older 84-name preservation inventory still matches those sources.
Future module names remain implementation choices where experiments establish
only the required import boundary. The approved temporary-test retirement rule
is unchanged. No production, experiment, CI or new task file was added.
Existing task links for this decision are batched in one commit.

Per-commit checks are the existing `tests/docs_test.py`, one-time source/link
inspection and independent Claude review. These are documentation diagnostics;
the accepted Nix experiment and production inputs above remain unchanged.

The existing documentation checks passed (three checks). One-time inspection
confirmed all 205 inventory links, the 84-name preservation expansion and the
under-200-line limit for each inventory and both ADRs. Source review corrected
the description of reverse import paths: adding opposite imports would create
cycles; the existing graph is acyclic. Independent Claude review of `186f9595`
returned no must or should findings. The refinement is complete.

## Amendment: rebase and source reconciliation, 2026-10-27

At the owner's request, fetched origin and rebased `plans/proof-boundaries`
onto remote main `daa15385` (PR #281). The branch had two shared prerequisites:
the ADR 0025 design and dependency-report implementation. Replayed private copies
of those prerequisites on main, then rebased this branch's own commits. The
original `plans/proof-simplification` and `tasks/theorem-dependencies` bookmarks
and their workspaces remain unchanged. Resolved the one Nix suite-name conflict
with both `surfaceChecks` and `theoremDependencies` present. No conflicts remain.

The current specifications and five inventories were reviewed against that
main revision. They now require all-effect/all-execution preservation, each
branch's reached state and counters, RENAME and INSERT SELECT dispatch/evidence,
and the current names of surface run guarantees. The preservation removal count
stays 84; 18 surface names changed to `runScriptAllFrom_`. The query count grows
from 42 to 45 through filtered duplicate-key observations. Retained NOT IN/IN
equivalences, traced resolver equations, existing rename certificates, new
frame consumers and read-certificate boundaries are explicit. At that revision
(`daa15385`), source/expression targets and four primitive/three import edits
were unchanged. The 2026-10-28 amendment below records the later delivered move.

Experiment READMEs now give explicit historical replay revisions. Their Nix
results above remain valid for those sources only; no current-main prototype
compile or full production acceptance is inferred from the rebase. Current
all-execution and extended query/resolver formulas remain implementation gates.
Production package files equal main. No new tests, tasks or permanent checks
were introduced; task-file edits for this decision are batched in one commit.

Validation for this amendment uses the documentation checks, one-time target
and link inspections, the dependency-report Nix suite and focused report/build
integration diagnostics. Independent review follows the specification commit.

The dependency-report suite passed in Nix: 27 tests, result
`/nix/store/7lxsb52rlnlkmzjjm7x3gngl8hp0kimx-sqlite-verifier-test-theoremDependencies-1`.
This validates the retained report tooling, not the historical proof prototypes.
Focused report/layer/build-ownership diagnostics also passed; local diagnostics
are not additional semantic acceptance evidence.

The documentation checks passed. One-time inspection confirmed all 84 live
preservation targets, all 45 query targets, the five inventories' 231 local
links and file-size limits. Independent Claude review of `b22163ec` returned
no must or should findings. Rebase reconciliation is complete; the current
specifications describe implementation obligations, not a delivered refactor.

## Amendment: current-main reconciliation, 2026-10-28

Fetched origin and rebased the private spec history onto main `3e2212ed`
(PR #292), preserving the other workspaces and bookmarks. Resolved the single
suite-registration conflict by retaining `theoremDependencies`, `surfaceChecks`
and the new `surfaceS6`. The branch has no conflicts; production packages equal main.

Rechecked ADRs 0025/0026 and their inventories against current source. The
84 preservation and 45 query targets remain. Preservation now includes clean
column drops and explicit FK rewrite conditions; the rename executor's
`sameOutline` guard no longer supplies selected-parent equality. Resolver
certification reuses `DropOutcome` and preserves the executable/proof import
split of PR #292. Read certificates retain moved table positions and obligations
for every migration branch. New derived-column and schema-script proofs are
retained consumers; their generalization is already delivered on main.

Only three primitive moves remain: `LiteralData.generatedCells_plain` already
lives in `AdmittedCellLaws`. Expression agreement retains the distinct DROP COLUMN
transformation proof, outside the fixed-expression experiment. Removed live links
to deleted `NormalizedField*` modules. Historical experiment sources and their
accepted evidence remain unchanged; current-main prototype acceptance is not claimed.
All existing task-file edits for this decision are batched in one commit.

The dependency-report Nix suite passed all 27 tests:
`/nix/store/naqz980nkkjif62hdx0n4nfp2sbhy2hv-sqlite-verifier-test-theoremDependencies-1`.
Focused report, layer and build-ownership diagnostics passed, as did the
documentation checks. One-time checks confirmed 84 preservation and 45 query
names, 284 local links across ten ADR/spec files, and their size limits.
Independent review follows this commit. These checks do not constitute production
proof-refactor acceptance.

Claude reviewed `3023b981` with no must findings and two should findings.
Clarified the earlier baseline's historical four-primitive scope and separated
unchanged required expression replacements from newly listed retained consumers.
Both findings are resolved. Claude reviewed clarification commit `1a49a919`
with no findings. Reconciliation is complete; implementation remains unassigned.

2026-10-28: recorded the owner's [long-term reduction goal](../docs/lean-simplification-goal.md).
Its fixed baseline, capability accounting, Nix count and milestones govern later work.
Checks: `tests/docs_test.py` passed; Nix count is in the goal; Claude reviewed `b2725083` with no findings.
