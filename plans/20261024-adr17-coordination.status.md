# ADR 0017 coordination status
Created 2026-10-24. Status: OPEN. ADR 0017 is not complete.
This record coordinates the task/status files; it adds no implementation scope.

## Standing owner instructions

Continue until ADR 0017 is complete. Specify each task before delegating its
implementation to a subagent. Parallel tasks need separate jj workspaces,
disjoint edit surfaces and enough VM resources. Integrate useful modularity
improvements. Push completed task PRs without another permission request.
Clean completed workspaces after the code is pushed, retaining any workspace
needed for an active review. Batch task-file edits into one commit per decision;
write new task files only shortly before assignment (owner, 2026-10-24).
`direnv allow` is authorized, reaffirmed for isolated ADR17 workspaces with
unchanged approved shell configuration on 2026-10-24. Ask for owner judgment
when a specification is wrong or incomplete, with options and a recommendation.
Owner override on 2026-10-24: close all herdr review tabs and open no new ones
before Monday, 2026-10-26 UTC. Automated independent reviews continue normally.
All three tabs were closed; waits returned `closed_without_review`, not approval.

The 2026-10-24 handoff's check override remains: relevant mutants only by `-k`,
no broad local `test-scheduled` or `test-mutants`; task-end scheduled checking
uses `test-scheduled-checks`. No garbage collection without permission. Keep
10 GiB free on `/` and `/nix/store`. Those share a smaller filesystem than the
workspace filesystem. Reserve at most two heavy build/check processes here.

## Accepted decisions

- S5 default search infers small schemas and targeted values, with explicit
  schemas and custom generators also available.
- S5 background checks are enabled by default. Only a kernel-confirmed
  counterexample is an error; measure and expose the budget.
- ADR 0022 slice 5 splits parent-schema compatibility from row-reference truth.
  Its explicit-mapping primitive and exact engine-selected convenience helper
  preserve the existing SQLite meaning, including repeated key columns.
- ADR 0019 slice 4 supports nonrecursive CTEs. Actual recursion is excluded
  regardless of spelling, and the RECURSIVE keyword remains excluded.
- Keep current DQS-on and initial-FK-off defaults. Correct the guide and enable
  enforcement explicitly before transactions in the affected examples.
- SQL doc-block headers use double-quoted strings and named closed Lean values
  for other types, following pinned Verso's grammar.
- S4's exact query-success iff describes the default run. Keep sufficient
  bridges to universal `Succeeds`; no universal-to-default converse is claimed.
- Correct the shared FK NULL helper to use the selected child projection,
  including repeated columns; keep declaration fallback when no mapping exists.
  Add native regressions and revise the default split API/proofs.
- ADR 0019 slice 5 models exact INSERT SELECT streaming/materialization,
  including its error ordering and partial writes.
- S7 keeps exact SQLite metadata and native Lake input tracking. Correct the
  blanket promise that whitespace/comment edits never rebuild importers.

The owner accepted all three remaining recommendations on 2026-10-24 and
resumed the goal. S4 recorded its default-run decision in reviewed `73b9f65b`.
The owner accepted both S6 recommendations on 2026-10-24: `≈` compares full
connection state and every branch outcome, with weaker visible comparisons
named separately. Universal insert/lookup and purge-frame guide claims gain
explicit schema/trigger/FK effect premises and retain the native counterexamples.
ADR17 records the exact strong relation. The owner also accepted explicit
observation views for quiet migration segments and full contextual commutation
for every S8 call pair, including queries. Weak query-output translation stays
available but cannot alone establish the whole-program theorem.
All three later recommendations are accepted: an explicit fresh-run helper,
selected [FK action targets](20261024-foreign-key-atoms.task.md), and explicit
interface-scoped simulation beside the full-state relation. Expansion/write
orders have equal rows but total_changes
3 versus 4; retain that full-state refutation.

## Resolved findings
The repeated-column FK correction is recorded in its task; preservation remains open.

The INSERT SELECT streaming/materialization counterexample and accepted scope
are now in ADR19 D4. The formatting counterexample is reflected in ADR17 D6:
SQLite can preserve expression spelling in column names. These accepted changes
remove the prior planning blocks; they are not implementation-completion claims.

## Active implementation and ownership

- S4 is DONE in PR #244 at `70705018`, checked source `24ca8b4c`.
  Full 865, Nix 70, scheduled 47, verdict and unchanged 53-file predictions
  passed. The checked API reference contains 543 modules and 5,037 source links.
  Both private email extracts and the full balance proof pass the installed
  runtime with only standard logical axioms. Final review has no findings.
- `s4_part1` implements S5 in isolated `s5-counterexamples` on published
  `0569149b`, with reviewed handoff `e50e1f9e`. Plausible compatibility passed
  in Nix. Explicit certification and policy follow-up `76504977` passed 11 Nix
  checks and clean review. Sampler `593caf88` passed 12 Nix checks, including
  the row-bound regression. Slot 1 runs inference checks (`52260`); replay and
  background checking remain open.
- `s6_prerequisite_audit` completed derived-source part 1, published in #243.
  Separate evidence head `5d69e3fa` retains draft v53's 38 agreements and
  four restrictions. Combined acceptance is recorded in its task status.
  CTE part 2 is DONE in PR #248, head `e3d6aa38`, above #247. Full 923,
  final focused 36 and verdict 4,869/2,503 passed. All prior predictions are
  unchanged; two become agreeing and 69 retain unsupported with changed reasons.
  All changes are classified; publication reviews are resolved. Views remain
  OPEN. Origin-metadata source `86e15af9` passed 17 Nix fixtures and unchanged
  53-file predictions (`30578`, exit 0); independent review is running.
- The S6 foundation prototype is DONE in PR #246 at `334d9645`, above #245.
  Original full 813/Nix 67/scheduled 47 and verdict passed. The final focused
  integration checks all five modules and 28 audits against S4; review is clean.
  No production S6 API is implemented by this prototype.
- `text_build_boundaries` owns FK preservation. Split-API/action part 1 passed
  full 826, 35 native cases, four mutants and the unchanged frozen predictions.
  FK owns atom/check/frame exports, ForeignKeyPlan, TriggerClosure and ParentKeys.
  S4 supplied exact pragma laws. Current workspaces are `fk-statement-preservation`
  and `fk-ddl-preservation`; DDL follows the accepted engine induction.
  No shared ancestor may be rebased while descendants are active.
  Corpus v53 is reserved for query-sources, v54 for FK; each uses a separate
  judge/evidence workspace and protected PR after measured model comparisons.

S4 retains `sqlite-verifier-product-s4-guide` for later integrated-guide acceptance.
Reviewed private head `5dbc6f15` adds physical-table premises to both email copies
and balance; all pass installed runtime `b6n8f8xys0ax45ldilp9rqw2030q8pwa` with standard axioms.
Final acceptance must selectively reconcile unpublished S2/S3 product-default changes.

FK engine checkpoint `b1a163df` passed 11 Nix fixtures/203 axiom audits at
`grsxi5rjsqz0w3311nf5xv3l2yiilv6m`; review is clean. Statement/run checkpoint
`a8bf73ae` passed 14 Nix fixtures/236 audits at `04dmvlj39cmypsa26ia21rhnskqxsjp1`
and resolved review. CREATE/plain-DROP gate `19966` is running. Enforced DROP
and NULL-default ADD proofs continue independently. A nonempty child table
with enforcement on exposes an ADD REFERENCES/non-NULL-default discrepancy;
the owner is asked to extend the explicitly limited execution-change scope.
The prerequisite through `9350aa31` is published in PR #247 at `b1130903`,
above #246. Final integration passed 19 focused Nix cases, the frozen verdict
4,867/2,505, and all 53 predictions match published S4 output `ifmznfzp`.
The combined full suite was not rerun for this prerequisite publication.
The API-reference repair is DONE in #242 `b6864447` and #243 `2cb4c5e3`:
12 Nix reader cases cover 0 through 640 roots; complete 532/538-module builds
passed. Their task statuses retain full/Nix/scheduled evidence. CI and Verdict
are green for #242 through #247. #248 Verdict is green; CI is running.
Both repair workspaces are removed; their logs/report XML are archived under S4 build/.
S7 prototype PR #245 `0569149b` is DONE: full 872/Nix 70/scheduled 47; accepted scope reviewed.
## Published work and cleanup

- Public [PR #240](https://github.com/vihren-dev/sqlite-verifier/pull/240),
  `tasks/text-build-boundaries`, head `2f86e45a`, base #239, stack 231: DONE.
  Full 792, Nix 67 and scheduled 47 passed; verdict 4,838/2,534, all 53
  predictions/7,372 cases byte-identical. Full report is
  `/nix/store/ykfdsmryx18cplw9zrf1dy3xakqlbydj-sqlite-verifier-test-reports`.
- Public [PR #241](https://github.com/vihren-dev/sqlite-verifier/pull/241),
  `tasks/prediction-source-filter`, head `529ff779`, base #240, stack 231: DONE.
  Full 792, Nix 70 and scheduled 47 passed; same verdict/predictions, all 55
  locked parts unchanged. Protected judge source change still needs owner merge.
- Private product PR #7, `docs/guide-profile-defaults`, head `17666ac9`, base
  published `c1471940` (PR #6): DONE. Nine pinned native checks passed; two
  Verso-header corrections preserve the SQL bodies. No unrelated unpublished
  ancestor was included in publication.
- Private product PR #8, `docs/guide-success-and-inputs`, head `c09f415e`, base
  #7: reviewed email/balance table premises, proofs and planned named-cost contract.
  Native metadata and installed-consumer checks are recorded in its private status.

Herdr waits `w1:t3T`/78895, `w1:t3V`/78368 and `w1:t3W`/56689 returned
`closed_without_review`; no approval is inferred. Clean, pushed workspaces
text-build-boundaries, prediction-source-filter and profile-publication were removed
after confirming no active process and remote reachability. Earlier cleanup removed
profile-guide, the unused editor workspace, adr19s2/adr19s3/adr22s2/adr22s3/
adr22s4/errev/envfns. Completed s4-schema and s4-observations were removed
following remote reachability/process checks, as was s4-query-publication after
[PR #242](https://github.com/vihren-dev/sqlite-verifier/pull/242). Derived subject and publication
workspaces were removed after #243; gate logs are retained under S4 build/.
Completed s4-run/table-premises, s7-proof-cost and both S6 prototype workspaces
were archived and removed after their pushes. Protected s4chk remains.
Published fk-preservation/update-preservation/update-coverage were archived and
removed after remapping diagnostic artifacts. Original fk-atoms was removed
after comparing its five late copied commits with published #248: all code and
review records are retained, with later documentation corrections. Its exact
late patch and acceptance logs remain under S4's archived FK publication logs.
The clean, remotely retained fk-publication workspace was also archived and
removed after #247 CI passed; no active process depended on it.
Completed CTE/CTE-implementation/integration workspaces were archived and removed
after #248. Their six accepted Nix out-links have independent roots under
`cte-publication/build/accepted-cte-artifacts`. Evidence and views remain active.

## Specified work and remaining scope

- [S5](20261024-surface-s5.task.md) is assigned to `s4_part1` in
  `s5-counterexamples` on published S4/S7. Plausible compatibility passed;
  certification and sampling are checked; inference is in progress.
- [Query sources](20261024-query-sources.task.md) is active as above; the
  [table rebuild task](20261024-table-rebuild.task.md) now has clean follow-up
  review `20261024T142117Z-79fd6a8b` and waits for its final view/CTE design.
- [S6 prototype](20261024-surface-s6-foundations.task.md) is DONE, published in PR #246.
  [Execution contracts](20261024-s6-execution-contracts.task.md)
  have clean review `20261024T144839Z-5684010b`.
  [Assertions](20261024-s6-assertions.task.md) and [migration patterns](20261024-s6-migration-patterns.task.md) have clean reviews
  at `33693f10`/`56b9f410`; [automation](20261024-s6-automation.task.md) is clean at `8b118fbc`.
  [Initial/current query context](20261024-s6-before-context.task.md) has clean
  review `20261024T143052Z-5feffb18` and waits for query-source/view integration.
- [Editor](20261024-surface-editor.task.md) is reviewed, unassigned.
- [SQL doc blocks](20261024-sql-doc-blocks.task.md) has clean follow-up review
  `20261024T140400Z-04f1c91e`, unassigned; it accompanies S7.
- [S7 files/freshness](20261024-surface-s7-files.task.md) has clean follow-up
  review `20261024T140930Z-09c30b41`, unassigned.
- [S7 proof-cost prototype](20261024-s7-proof-cost-prototype.task.md) is DONE
  and published as PR #245 at `0569149b`, above completed S4 PR #244 `70705018`.
  Production will use the accepted named-body contract, including native mutual declarations.
- [Guide rebuild wording](20261024-guide-sql-rebuilds.task.md) is DONE, published
  with reviewed S4 explanatory prose in private product PR #8, head `1ae76380`.
- [S8 simulation](20261024-surface-s8.task.md) is reviewed clean at `03ac78a0`:
  both full-state and explicit scoped relations; unassigned pending prerequisites.
- [Integrated guide acceptance](20261024-adr17-guide-acceptance.task.md) has
  clean review `20261024T145218Z-e244461b`; it awaits every required implementation.

Read-only S7/editor audits remain in the modularity research notes. Reserve shared
surface helpers before editor/doc/file tasks run concurrently. Production proof
costs need the prototype contract. ADR17 needs all required behavior and acceptance.
