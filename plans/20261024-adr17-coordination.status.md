# ADR 0017 coordination status

Created 2026-10-24. Status: OPEN. ADR 0017 is not complete.
This record coordinates the task/status files; it adds no implementation scope.

## Standing owner instructions

Continue until ADR 0017 is complete. Specify each task before delegating its
implementation to a subagent. Parallel tasks need separate jj workspaces,
disjoint edit surfaces and enough VM resources. Integrate useful modularity
improvements. Push completed task PRs without another permission request.
Clean completed workspaces after the code is pushed, retaining any workspace
needed for an active review. `direnv allow` is authorized. Ask for owner judgment
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
3 versus 4; retain that full-state refutation. No owner question is pending.

## Resolved findings

The FK regression uses `p(a,b,PRIMARY KEY(a,a))` and child `(x,y)` referencing
`p(a,b)`. Native rejects `(99,NULL)` against parent `(1,2)` under enforcement;
it reports a pragma violation if the row was stored with enforcement off.
The old model exempts the row because it reads unused `y`. The revised FK task
and ADR22 require selected `x` twice, as pinned native `fkLookupParent` does.
The FK workspace retains its split-API work. The accepted correction is now
assigned to `text_build_boundaries`; no FK acceptance result is claimed yet.

The INSERT SELECT streaming/materialization counterexample and accepted scope
are now in ADR19 D4. The formatting counterexample is reflected in ADR17 D6:
SQLite can preserve expression spelling in column names. These accepted changes
remove the prior planning blocks; they are not implementation-completion claims.

## Active implementation and ownership

- `s4_part1` owns `sqlite-verifier-s4`. Part 1 passed full/verdict (805 tests,
  4,838 AGREE / 2,534 MODEL_UNSUPPORTED, all 53 predictions unchanged), then
  rebased cleanly onto #240 at `372e6c8f`. Its pre-rebase full report is
  `/nix/store/japwh8n1f0chh7fz6ig44qn9dxhkm8y5-sqlite-verifier-test-reports`.
  Part 2's reviewed success contract is `00c8707f`; exact default-query bridge
  `fd0f0c1e` is also reviewed. GROUP/index follow-up `82f70442`, mixed-value SUM
  bound `3811b3f4`, uniqueEmail fixture `a003ddcf` and stored range bridge
  `3583de8a` have clean reviews/Nix checks. Metadata law `e3f48d3b` is reviewed
  clean, with Nix model `81v66kv633za3q994jjiiml6lvsaz7q4`. Balance proof and
  part-2 acceptance remain, then part 3's removal of Run.checked.
- `s6_prerequisite_audit` owns `sqlite-verifier-query-sources`, based on S4 part 1.
  Source execution `93767a4d`/`15a252a8` and metadata `649a3021`/`bc79e3e7`
  have clean reviews and Nix model checks. Translation/resolution `c64d8b50`
  is reviewed clean; Nix model is `wnxni6bvnfd3cisq5nndg95qspgbyh94` and
  predictions `xar2y93h71ffx1ccrjvy906936hk4ahj`. Separate draft-v53 evidence
  `873a1473` is reviewed clean; verdict `6h8hi4b2c0z3fkxjamwix6508l30dz9i`
  passes, including 38 new agreements and 4 explicit unsupported cases. Full
  acceptance is correcting stale right-join mutant targets. CTEs/views follow.
- `text_build_boundaries` owns `sqlite-verifier-s6-foundations` and resumed FK
  work. The S6 prototype consumes reviewed S4 `00c8707f` without rebasing.
  Implementation `e9a0354d` and refactor `6c26ac21` have resolved/clean reviews;
  56 focused Nix surface tests pass at
  `/nix/store/1rzb9hwr5s7yccpwjx2xiwbzja3bcd99-sqlite-verifier-test-surface-1`.
  Its 28 audited declarations use only ordinary logical axioms. Design
  refinement `a3cffcb5` and decision record `c838d5cc` have clean reviews.
  DONE at `eb0a16a9`, clean completion review: full 813 at
  `vg3sz4iz4q58vrci7ddrxn9bmv6p7pbi`, Nix 67, scheduled 47, verdict and all 53
  predictions unchanged. It awaits S4-based publication and does not implement
  production S6. Root copied its reviewed task/status; source workspace stays.
- The FK workspace is `sqlite-verifier-fk-atoms`. Revised selected action scope
  is carried in `1a10a3c8`, follow-up `01a02bef` reviewed clean. Split-API and
  action implementation remain uncommitted; focused checks are active. FK owns
  atom/check/frame modules, Database exports and reserved manifests, plus
  ForeignKeyPlan, TriggerClosure and ParentKeys (query-source confirmed).
  S4 supplied exact pragma query laws. Lookup/scan consistency clarification
  `98e1e8f1` is reviewed; baseline predictions are `4k77z378vnagzwx5448yqz0686d58cld`.
  No shared ancestor may be rebased while descendants are active.
  Corpus v53 is reserved for query-sources, v54 for FK; each uses a separate
  judge/evidence workspace and protected PR after measured model comparisons.

S4 owns `sqlite-verifier-product-s4-guide`, originally based on `17666ac9`.
Its reviewed explanatory prose and rebuild wording are published in PR #8;
UniqueEmail proof `efb4e6ee` is reviewed, awaiting installed-consumer Nix evidence
before PR8 update; balance remains open. The product default workspace contains
unpublished S2/S3 guide changes; final acceptance must reconcile these selectively.

The reviewed one-line surface helper fileset fix `b9008683` was carried into
S6. Its initial missing-helper Nix failure is resolved. At most two heavy checks
run: query-source/S4 share slot 1 by explicit handoff; FK now owns slot 2.
No agent opens a herdr tab before the owner's Monday deadline.

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
- Private product PR #8, `docs/guide-success-and-inputs`, head `1ae76380`, base
  #7: reviewed S4 explanatory prose and DONE rebuild wording. Native 3.51.0
  confirms the metadata counterexample; all fenced SQL bodies are unchanged.

All three herdr review tabs and waits are closed by owner request:
`w1:t3T`/78895, `w1:t3V`/78368 and `w1:t3W`/56689. Each returned
`closed_without_review`; no approval is inferred. Their clean, pushed workspaces
text-build-boundaries, prediction-source-filter and profile-publication were
forgotten/removed after confirming no active process and remote reachability.
The earlier completed profile-guide and unused empty editor workspace were
also removed. Prior pushed cleanup removed adr19s2/adr19s3/adr22s2/adr22s3/
adr22s4/errev/envfns. Protected s4chk and unrelated workspaces remain. S4's
completed schema/observation workspaces await publication before removal.

## Specified work and remaining scope

- [S5](20261024-surface-s5.task.md) is reviewed and waits for final S4 run/success
  interfaces. Plausible v4.34.0 needs a compatibility build under Lean 4.34.1.
- [Query sources](20261024-query-sources.task.md) is active as above; the
  [table rebuild task](20261024-table-rebuild.task.md) now has clean follow-up
  review `20261024T142117Z-79fd6a8b` and waits for its final view/CTE design.
- [S6 prototype](20261024-surface-s6-foundations.task.md) is DONE, awaiting push.
  [Execution contracts](20261024-s6-execution-contracts.task.md)
  have clean review `20261024T144839Z-5684010b`.
  [Assertions](20261024-s6-assertions.task.md) and
  [migration patterns](20261024-s6-migration-patterns.task.md) have clean reviews
  at `33693f10`/`56b9f410`; [automation](20261024-s6-automation.task.md) is in review.
  [Initial/current query context](20261024-s6-before-context.task.md) has clean
  review `20261024T143052Z-5feffb18` and waits for query-source/view integration.
- [Editor](20261024-surface-editor.task.md) is reviewed, unassigned.
- [SQL doc blocks](20261024-sql-doc-blocks.task.md) has clean follow-up review
  `20261024T140400Z-04f1c91e`, unassigned; it accompanies S7.
- [S7 files/freshness](20261024-surface-s7-files.task.md) has clean follow-up
  review `20261024T140930Z-09c30b41`, unassigned.
- [S7 proof-cost prototype](20261024-s7-proof-cost-prototype.task.md) has clean
  follow-up review `20261024T141307Z-82085ddd`, unassigned. Production costs still
  need its measured collector contract. This facet is required, not deferred.
- [Guide rebuild wording](20261024-guide-sql-rebuilds.task.md) is DONE, published
  with reviewed S4 explanatory prose in private product PR #8, head `1ae76380`.
- [S8 simulation](20261024-surface-s8.task.md) is reviewed clean at `03ac78a0`:
  both full-state and explicit scoped relations; unassigned pending prerequisites.
- [Integrated guide acceptance](20261024-adr17-guide-acceptance.task.md) has
  clean review `20261024T145218Z-e244461b`; it awaits every required implementation.

Read-only S7/editor audits remain in the research-notes directory of the Lean
model modularity investigation. Shared surface helper ownership must be reserved
before editor/doc/file tasks run concurrently. Production proof costs still
need the measured prototype contract. ADR17 is not complete until all required
behavior and acceptance pass.
