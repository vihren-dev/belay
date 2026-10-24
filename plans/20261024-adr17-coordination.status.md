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
One later decision is pending: use an explicit fresh-run helper for the guide's
fresh database/complete-environment claims, proved equivalent to standard
Std.Do triples with precise entry assumptions. Ordinary triples still quantify
over arbitrary contexts. Only dependent public-assertion work is paused.

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
  bound `3811b3f4` and uniqueEmail fixture `a003ddcf` have clean reviews. SUM's
  Nix model result is `4060h7wh955i0wrrh291i5l9b0fsncm2`. S4 still
  needs guide proofs/part-2 acceptance and part 3's removal of Run.checked.
- `s6_prerequisite_audit` owns `sqlite-verifier-query-sources`, based on S4 part 1.
  Source execution `93767a4d`/`15a252a8` and metadata `649a3021`/`bc79e3e7`
  have clean reviews and Nix model checks; latest model result is
  `24qvzhb6dpmsh27pzgqyjwr921dkkqbp`. Derived-source translation/resolution
  remains active. CTEs and views follow. Baseline predictions are
  `/nix/store/qwfgz46d1pyd10xiypmka4kixvx38k2b-sqlite-verifier-predictions`;
  baseline verdict `srv5lc3gnn1s9wzfjy1ilrzsb2ws0881` passes existing claims.
- `text_build_boundaries` owns `sqlite-verifier-s6-foundations` and resumed FK
  work. The S6 prototype consumes reviewed S4 `00c8707f` without rebasing.
  Implementation `e9a0354d` and refactor `6c26ac21` have resolved/clean reviews;
  56 focused Nix surface tests pass at
  `/nix/store/1rzb9hwr5s7yccpwjx2xiwbzja3bcd99-sqlite-verifier-test-surface-1`.
  Its 28 audited declarations use only ordinary logical axioms. Design
  refinement `a3cffcb5` and decision record `c838d5cc` have clean reviews.
  Full suite passed at `vg3sz4iz4q58vrci7ddrxn9bmv6p7pbi`; final gates continue.
  The prototype
  does not implement production S6. Its exact equivalence recommendation and
  the separate guide-effect correction are now accepted by the owner.
- The FK workspace is `sqlite-verifier-fk-atoms`. Root carried the revised task
  and ADR22 in reviewed `8526ed1f`, with status-only findings fixed in `0ca148ce`.
  The existing split-API source work remains uncommitted. FK owns atom/check/frame
  modules, surface Database exports and reserved barrel/lake/test entries.
  S4 identified the reviewed query-output dependency closure for the exact
  pragma law. Root's lookup/scan consistency clarification `98e1e8f1` has a
  clean review. The #239 prediction baseline is `4k77z378vnagzwx5448yqz0686d58cld`.
  No shared ancestor may be rebased while descendants are active.
  Corpus v53 is reserved for query-sources, v54 for FK; each uses a separate
  judge/evidence workspace and protected PR after measured model comparisons.

S4 owns `sqlite-verifier-product-s4-guide`, based on published `17666ac9`:
uniqueEmail/balance/holds_where, Level2 semantics and the separately reviewed
[rebuild wording correction](20261024-guide-sql-rebuilds.task.md). Preserve the
published defaults/header corrections. The product default workspace still
contains earlier unpublished S2/S3 guide changes; the final guide audit must
account for them without publishing unrelated ancestors.

The reviewed one-line surface helper fileset fix `b9008683` was carried into
S6. Its initial missing-helper Nix failure is resolved. At most two heavy checks
run: query-source slot 1 and S4/S6/FK sharing slot 2 by explicit handoff.
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
- [S6 prototype](20261024-surface-s6-foundations.task.md) is implemented and
  validating. [Execution contracts](20261024-s6-execution-contracts.task.md)
  specify the independent production primitives; follow-up review
  `20261024T144839Z-5684010b` is clean. Public
  assertions, patterns and automation still need their production task.
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
- [Guide rebuild wording](20261024-guide-sql-rebuilds.task.md) has clean review
  `20261024T142048Z-e614f5b6` and is assigned to S4's guide owner.
- [Integrated guide acceptance](20261024-adr17-guide-acceptance.task.md) has
  clean review `20261024T145218Z-e244461b`; it awaits every required implementation.

Read-only S7/editor audits remain in the research-notes directory of the Lean
model modularity investigation. Shared surface helper ownership must be reserved
before editor/doc/file tasks run concurrently. Full S6, production proof costs,
S8 simulation and the full guide acceptance audit still need tasks. ADR17 is
not complete until their required behavior and acceptance pass.
