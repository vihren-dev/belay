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
`direnv allow` is authorized. Ask for owner judgment
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
3 versus 4; retain that full-state refutation. No specification question is pending.

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
  clean, with Nix model `81v66kv633za3q994jjiiml6lvsaz7q4`. Balance `2175f989`
  is reviewed; all 62 surface tests passed at `vjvlvym2mp4lqjighnsc7q1qijbq1c2w`.
  Part-2 full/verdict remains. Part 3 starts in `sqlite-verifier-s4-run`.
  Named-source extension `656ab790`/`1dee994a` is reviewed and checked in Nix.
- `s6_prerequisite_audit` completed derived-source part 1 at subject `16bd87a3`;
  separate evidence head is `5d69e3fa`. Combined `c8db1a54` passed full 854 at
  `m64rgzasy2aqvp6d421pk5yh0v4654b9` and verdict `6nazink0rsrzhv7458rs3vgfs63c48dg`.
  Predictions `q4qrigjpa82cg89ggzkvinbnvmgi7pq6` match the earlier measured
  54 files. Existing corpora gain 29 agreements; draft v53 has 38 agreements
  and 4 restrictions. No disagreement/harness error. Subject excludes judge changes.
  CTE/view work resumes in `sqlite-verifier-query-sources-cte`, with use-site
  outer bindings preserved. Its combined integration must compile the balance fixtures.
- `text_build_boundaries` owns `sqlite-verifier-s6-foundations` and resumed FK
  work. The S6 prototype consumes reviewed S4 `00c8707f` without rebasing.
  Implementation `e9a0354d`/`6c26ac21` is reviewed; 56 focused Nix tests pass at
  `/nix/store/1rzb9hwr5s7yccpwjx2xiwbzja3bcd99-sqlite-verifier-test-surface-1`.
  Its 28 audited declarations use only ordinary logical axioms; design
  `a3cffcb5` and decision record `c838d5cc` have clean reviews.
  DONE at `eb0a16a9`, clean completion review: full 813 at
  `vg3sz4iz4q58vrci7ddrxn9bmv6p7pbi`, Nix 67, scheduled 47, verdict and all 53
  predictions unchanged. It awaits S4-based publication and does not implement
  production S6. Root copied its reviewed task/status; source workspace stays.
- The FK workspace is `sqlite-verifier-fk-atoms`. Revised selected action scope
  is carried in `1a10a3c8`, follow-up `01a02bef` reviewed clean. Split-API and
  action implementation `89267008` passed 35 Nix native cases and four mutants.
  Complete review coverage found documentation corrections; the first full gate
  found a duplicate catalog lemma. Reviewed `3df8e641` reuses the existing law;
  its full/verdict rerun remains pending. FK owns atom/check/frame modules and exports,
  ForeignKeyPlan, TriggerClosure and ParentKeys (query-source confirmed).
  S4 supplied exact pragma laws. Baseline predictions: `4k77z378vnagzwx5448yqz0686d58cld`.
  Part-2 schema/run and global row-counter laws use `sqlite-verifier-fk-preservation`.
  No shared ancestor may be rebased while descendants are active.
  Corpus v53 is reserved for query-sources, v54 for FK; each uses a separate
  judge/evidence workspace and protected PR after measured model comparisons.

S4 retains `sqlite-verifier-product-s4-guide` for its final installed-artifact check.
Both email copies and the full balance proof compile against Nix surface
`qz96vr9hh9vghmw4hihvvl2lwh4dmdxf`, with only ordinary logical axioms; PR #8 is updated.
Final acceptance must selectively reconcile unpublished S2/S3 product-default changes.

The reviewed one-line surface helper fileset fix `b9008683` was carried into
S6. Its initial missing-helper Nix failure is resolved. At most two heavy checks
run: query carry `79230` owns slot 1; FK rerun `36195` owns slot 2, then S4.
Root S4 query publication `975f31eb` passed full 808, Nix 70, scheduled 47,
verdict 4,838/2,534 and 53 unchanged predictions; its branch is pushed.
Derived publication merge `359eb0c7` has a clean review; gates remain pending.
Automatic approval rejected S4 PR creation and direnv allow in
`query-sources-cte-implementation`; explicit owner approval is requested for both.

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
- Private product PR #8, `docs/guide-success-and-inputs`, head `d3aeb407`, base
  #7: reviewed email/balance proofs, success prose and DONE rebuild wording.
  Native metadata and installed-consumer checks are recorded in its private status.

Herdr waits `w1:t3T`/78895, `w1:t3V`/78368 and `w1:t3W`/56689 returned
`closed_without_review`; no approval is inferred. Clean, pushed workspaces
text-build-boundaries, prediction-source-filter and profile-publication were removed
after confirming no active process and remote reachability. Earlier cleanup removed
profile-guide, the unused editor workspace, adr19s2/adr19s3/adr22s2/adr22s3/
adr22s4/errev/envfns. Completed s4-schema and s4-observations were removed
following remote reachability/process checks. Protected s4chk remains.

## Specified work and remaining scope

- [S5](20261024-surface-s5.task.md) is reviewed and waits for final S4 run/success
  interfaces. Plausible v4.34.0 needs a compatibility build under Lean 4.34.1.
- [Query sources](20261024-query-sources.task.md) is active as above; the
  [table rebuild task](20261024-table-rebuild.task.md) now has clean follow-up
  review `20261024T142117Z-79fd6a8b` and waits for its final view/CTE design.
- [S6 prototype](20261024-surface-s6-foundations.task.md) is DONE, awaiting push.
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
- [S7 proof-cost prototype](20261024-s7-proof-cost-prototype.task.md) has clean
  reviews at `82085ddd`/`cca27596`, unassigned. Production costs still need its
  measured collector contract. This facet is required, not deferred.
- [Guide rebuild wording](20261024-guide-sql-rebuilds.task.md) is DONE, published
  with reviewed S4 explanatory prose in private product PR #8, head `1ae76380`.
- [S8 simulation](20261024-surface-s8.task.md) is reviewed clean at `03ac78a0`:
  both full-state and explicit scoped relations; unassigned pending prerequisites.
- [Integrated guide acceptance](20261024-adr17-guide-acceptance.task.md) has
  clean review `20261024T145218Z-e244461b`; it awaits every required implementation.

Read-only S7/editor audits remain in the modularity research notes. Reserve shared
surface helpers before editor/doc/file tasks run concurrently. Production proof
costs need the prototype contract. ADR17 needs all required behavior and acceptance.
