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
- S7 optionally measures named theorem and proof-valued definition bodies,
  including ordinary and native mutual declarations. Report other coverage
  explicitly and compare compatible counts with a user-set CI growth bound.
  The corrected guide is published; production coverage remains open.

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
- S5 part 1 is accepted and published in PR #249 at `f808a41a`, including the
  cold-manifest and proof-cost fixture corrections. Its integrated full report
  passes 936 tests; verdict and all 53 prediction files are unchanged from #248.
  Detailed evidence remains in `20261024-surface-s5-part1.evidence.md` and the
  implementation status. The completed workspace has been retired.
  `s4_part1` has frozen shared-search source `efa0d465` in `s5-search`.
  Seventeen focused Nix checks pass at `dwk93ll3d8jxi6vhfd3gck1qxp892h3a`;
  two changed budget/search fixtures pass at `vmfzzp6s6mz5z42rhv9rbzwsz5c9mk8j`.
  Native SQLite replays all nine reported cases. Independent review awaits the
  reviewer login refresh. Integration `3a632d10` combines unchanged search
  source with complete S6 contracts and native artifacts. Its 18 focused Nix
  checks pass at `wvqkfh98cjbga852p7jgm0axwr1rf0gw`.
  The mechanical merge with stored-view source `694d0790` is frozen at
  `6228f90a` in `s5-view-integration`. Its incremental shared sampler and
  formatter retain empty storage and explicit replay refusal for views.
  All 26 focused Nix checks pass at `lscw12hldqbsah8n7i9bl71c6f5ilywd`;
  all 53 prediction files and 7,372 cases retain the exact accepted view output
  `lnz7y254m8cvgkz2fv9zw4cqcq3898i5`. Independent review remains pending;
  no frontend feature scope advanced in this integration.
  Commands, searched tactics, automatic defaults and editor actions remain open.
  The read-only frontend audit identified saved environments for anonymous
  examples and preservation of the native cancellation context as requirements
  of the existing implementation scope.
- `s6_prerequisite_audit` completed derived-source part 1, published in #243.
  Separate evidence head `5d69e3fa` retains draft v53's 38 agreements and
  four restrictions. Combined acceptance is recorded in its task status.
  CTE part 2 is DONE in PR #248, head `e3d6aa38`, above #247. Full 923,
  final focused 36 and verdict 4,869/2,503 passed. All prior predictions are
  unchanged; two become agreeing and 69 retain unsupported with changed reasons.
  All changes are classified; publication reviews are resolved. Views remain
  OPEN. Origin-metadata source `86e15af9` passed 17 Nix fixtures and unchanged
  53-file predictions (`30578`, exit 0). Normalization `858e0a2b`, with
  review/status head `c0e288b5`, fixes both origin review findings and has clean
  review. Its 17 Nix fixtures passed at `yy0xf2n1yrg9assy7y31bfda0v6ign9q`;
  all 53 prediction files/7,372 cases remain identical. The next isolated
  catalog/source workspace joins this head with published #248 and carries
  only the checked exact `CatalogValidDrop` lookup law/caller from `135b8338`.
  The merge `63bcea9d` has clean review. Catalog/source implementation now owns
  slot 2 for build/proof closure. An admitted view must expand correctly or
  return an explicit interim model restriction, never fabricated missing-table
  or empty-pragma outcomes. The FK owner has reserved the mechanical view cases
  in parent lookup, planning and row updates to this unit; mapping/action formulas
  are unchanged. Exact parent-link framing also tracks view positions when no
  physical parent exists, without constraining view bodies.
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
and resolved review. CREATE/plain-DROP `135b8338` passed 13 Nix fixtures/238
axiom audits (`19966`, exit 0). Review has zero musts and three small fixes
that accompany the next enforced-DROP/ADD proof unit. Enforced DROP
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
are green for #242 through #248. At #248 head `e3d6aa38`, CI `40129182805`
and Verdict `40129182818` both completed successfully.
Both repair workspaces are removed; their logs/report XML are archived under S4 build/.
S7 prototype PR #245 `0569149b` is DONE: full 872/Nix 70/scheduled 47; accepted scope reviewed.
## Published work and cleanup

- Public [PR #240](https://github.com/vihren-dev/sqlite-verifier/pull/240),
  text-build boundaries `2f86e45a`, and [PR #241](https://github.com/vihren-dev/sqlite-verifier/pull/241),
  prediction-source filter `529ff779`, are DONE in stack 231. Both passed full
  792/scheduled 47; Nix 67 and 70 respectively. Verdict 4,838/2,534 and all
  53 predictions/7,372 cases stayed identical. Their task statuses retain results.
  #241's protected judge source change still requires owner merge approval.
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
after #248. The clean, remotely retained cte-publication workspace is now
retired too, after host-process and owner dependency checks. Its six accepted
outputs have independent roots under `s4/build/accepted-cte-artifacts`; its
logs are in `s4/build/agent-logs/cte-publication`. Evidence and views remain active.

## Specified work and remaining scope

- [S5](20261024-surface-s5.task.md) is assigned to `s4_part1`; part 1 used
  `s5-counterexamples` on published S4/S7 and shared search now uses `s5-search`. Part 1 is accepted at
  `77dc166d`: final Nix report `lwi3qm7nqb4j4n3r03q0172prbm3mx7g` contains
  877 tests with zero failures, errors or skips, verdict passes at
  `1w3s86b8201bc72c1r51rc66rnb1iknr`, and all 53 frozen prediction files are
  unchanged. The root independently counted the report totals.
  [PR #249](https://github.com/vihren-dev/sqlite-verifier/pull/249) publishes
  part 1 at `f808a41a` on #248, in stack 231. The integrated Nix report
  `khn3naiwa85vk1iaf4yk73f6d57f2j28` passes 936 tests; source checks pass 521.
  Verdict `afn513ampmbdfjr467cm90dydkyirkd1` passes, and all 53 files/7,372
  predictions reuse the exact #248 output. Source reviews are clean. Shared
  checking and automatic diagnostics remain open in the separate search workspace.
- [Query sources](20261024-query-sources.task.md) is active as above; the
  [table rebuild task](20261024-table-rebuild.task.md) now has clean follow-up
  review `20261024T142117Z-79fd6a8b` and waits for its final view/CTE design.
- [S6 prototype](20261024-surface-s6-foundations.task.md) is DONE, published in PR #246.
  [Execution contracts](20261024-s6-execution-contracts.task.md)
  were refreshed at `7e855ae9` with clean review and assigned to
  `text_build_boundaries` on published #248 in a separate S6 workspace.
  First production unit `e5d737bd`, accepted head `7711598f`, provides exact
  branches, branch validity/composition, the modeled-execution transformer and
  standard-triple soundness. Independent review has no findings. Its two
  Nix test groups passed at `9mh19n9lvn425dfn9s9hdbbjcwcdf732`, with 32 new
  and 28 retained prototype axiom reports using only standard logical axioms.
  The success/fresh-run unit is accepted at `e804ddde`, source `1c09bf9f`,
  with clean review `20261024T212855Z-1c09bf9f`. Its two Nix surface groups pass
  at `gm2y6fiagq0jcngxjxq089kbfcfrvhi7`: 54 production and 28 prototype axiom
  reports use only standard logical axioms. Combined acceptance with S5 and the native
  artifact fix is running in `s6-native-publication` from source `8a6ed72a`,
  clean review `20261024T215807Z-8a6ed72a`, review record `0efc3042`.
  Full Nix report `vkv6a2w0acxkfy3bagcw89aqk5rkhgbz` passes 937 tests with no
  failures, errors or skips; source checks pass 521. Verdict
  `fdyxvw89hvk8i7sa232c6is81sczb24d` passes with 4,869 AGREE and 2,503
  UNSUPPORTED results. All 53 prediction files and 7,372 cases are byte-equal
  to the published baseline. Task-end Nix checks pass 71; scheduled report
  `j37adzg25s32slqy03advda9hfd02dwx` passes 47 with no failures, errors or skips.
  The complete sequential part-one/native acceptance gate exited successfully.
  Strong equivalence and composition source `51387d8e` is accepted at
  `52cd08bf`, with clean review `20261024T222747Z-51387d8e`. Its two focused
  Nix groups pass at `f0yg6digr0wiv60gjvihv6jb5x93a05s`; 101 production and
  28 retained prototype axiom reports use only standard logical axioms.
  Complete execution-contract integration `5bc323f0` joins these accepted
  sources in `s6-complete-publication`. Its independent review and final
  acceptance remain pending. Publish one complete execution-contract PR.
  The same worker now owns the reviewed [native artifact reuse task](20261024-model-native-artifacts.task.md)
  in an isolated workspace. The existing surface gate rebuilt 589 unchanged
  model C objects despite a cached model derivation. Task `e2a49629` has clean
  independent review. Native source `ebe1c3e9`, frozen head `a4c91d52`, has
  clean follow-up review. Nix package replay passes three checks at
  `2g962nijmc1fl3s99hl6d9j2yp7l1058`; installed surface checks pass 81 at
  `ypfqx5qns8bl8c16yjw36syqb5d80gwh`. A real surface-only source edit
  rebuilt zero model C objects, while the old output fails the new replay
  check as expected. Combined native-artifact acceptance is complete. S6 source
  work is frozen for final integration; FK proof work continues in isolated probes.
  [Assertions](20261024-s6-assertions.task.md) and [migration patterns](20261024-s6-migration-patterns.task.md) have clean reviews
  at `33693f10`/`56b9f410`; [automation](20261024-s6-automation.task.md) is clean at `8b118fbc`.
  Migration-pattern public primitives are now assigned to `s6_prerequisite_audit`
  in isolated `s6-migration-patterns` on `5bc323f0`. The first unit reserves
  new execution-view/pattern modules; rebuild/FK examples remain later work.
  Its descriptor/projection source is frozen at `504b819b`. Both focused Nix
  groups pass at `3f2nwr14gs5wz0j4q1vhp3ix3xa50ayh`, with 128 axiom reports
  using only standard logical axioms. Independent review remains pending;
  comparisons, migration patterns, examples and full acceptance remain open.
  [Initial/current query context](20261024-s6-before-context.task.md) has clean
  review `20261024T143052Z-5feffb18` and waits for query-source/view integration.
- [Editor](20261024-surface-editor.task.md) has clean final task review
  `20261024T132927Z-4be46bc9`. Its first acceptance part is assigned to
  `text_build_boundaries` in isolated `surface-editor` on `3a632d10`, with
  source/parameter information checked through the native server. Shared
  helper ownership remains with that worker; frozen S7/doc sources stay at rest.
- [SQL doc blocks](20261024-sql-doc-blocks.task.md) has clean follow-up review
  `20261024T140400Z-04f1c91e`, assigned to `text_build_boundaries` in isolated
  `sql-doc-blocks` on `5bc323f0`. Its new modules can proceed independently
  of the S7 package-root decision; shared helper ownership remains with the
  same worker. The first checked commit will wait for independent review.
  Its observation/checker unit is frozen at `3bb4171e`, with 12 focused Nix
  checks passing at `hf7dvfi8gzkgl71g1v930im6i4xk2dmn`. Public registration,
  headers, bindings, expected errors and source mapping remain open. The native
  registration fixture is a probe, not completion of the public SQL handler.
- [S7 files/freshness](20261024-surface-s7-files.task.md) has clean follow-up
  review `20261024T140930Z-09c30b41`, assigned to `text_build_boundaries` in
  `s7-files` on `5bc323f0`. Shared parameter/source helpers are reserved;
  S5 retains Check*, Sampling* and ReplayScript ownership. The first checked
  source commit requires independent review after the login refresh.
  Twenty focused checks pass, and the corrected real-consumer case passes at
  `hs6b8p1fzvl2cm9hm758f16qrbc7pygk`. The source is at rest. Two valid nested
  Lake projects can share a package ID and source file, while Lean omits the
  package root. The owner has been asked to choose a relative root override,
  Lake-supplied root metadata, or an unambiguous-layout restriction. No choice
  has been implemented before the answer.
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

The completed `s5-counterexamples` workspace was retired after PR #249's push,
clean-state/remote checks and the search owner's independent-cache audit. Its
complete build evidence is archived in `s4/build/agent-logs/s5-part1-implementation`;
12 outputs are rooted under `s4/build/accepted-s5-artifacts`. The active search
and old sampling-draft workspaces remain available.

The modularity report's retired-workspace citations now use published source
files or exact archived source copies. Historical research claims are unchanged.
Keep its cited S4 build logs available when eventually retiring that workspace.

View catalog foundation `59dc5215` and anchor repair `a890097f` are accepted
at `d1b28daf`, with clean final review `20261024T215844Z-a890097f`.
All five affected targeted Nix mutation checks pass. Stored-view expansion is
frozen at `694d0790` in `query-sources-view-integration`. Eight focused Nix
checks pass at `cj5vhkv8xxk9iqz7q4yal2yi7hk1c0ry`; all 53 prediction files
and 7,372 cases remain unchanged. Independent review, remaining view behavior
and full acceptance remain open. PR #249 Verdict CI
and Linux main check passed. CI run `40136011925` failed in Linux general
mutants: query, fromless and JSON-function groups reported failure before the
overall timeout. Function and table mutant jobs passed. PR #248's nominally
successful general-mutant job skipped execution after selecting infrastructure
scope, so it is not a passing mutant baseline.

The original `fromless_star_accepted` mutant survives its unchanged native
target in a focused Nix reproduction (derivation
`6hlzam2x2342xbc0awm5m2x9x8z0w38r`, 82.17 seconds). Earlier `starIssue`
validation prevents the target from reaching the mutated `resolveResultColumn`
guard. Both guards serve existing APIs or error precedence. A diagnostic with
one logical fault applied at both sites passes at
`b1cb35nhbg9vdwh0dpdhy9bjzlvr0p4k`: the unchanged native baseline agrees and
the same target kills the two-site mutant. No production resolver or harness
change has been made. Focused Nix runs of the unchanged query and JSON groups
pass: all 16 query mutants are killed at `hvx19aq81d4n444lp9qgyngd1hg337gj`
(160.60 seconds), and all 14 JSON mutants at `bw6qs4f727q8qi1hfhldgghxbfgyi7w2`
(194.09 seconds). The hosted failures have no retained traceback; their exact
cause remains unconfirmed. These local results do not establish hosted timing.
The original CI logs are retained under `s4/build/agent-logs/ci24{8,9}-mutants-linux.log`.

Enforced FK DROP source is frozen at `dd60f94c`, after the focused Nix output
`s5r4vk09sydz5wk93ypa0dzl8g9fwcr6` passed 18 fixtures with 293 standard-axiom
reports. It covers NULL/action outcomes, carried FAIL states and separate row
and schema frames. Required independent review remains pending the same login
refresh; this is not a task-completion or publication claim.

The frozen S6 part-one and native-cache build evidence has been copied, with
byte/symlink verification, into `s4/build/agent-logs/s6-execution-part1` and
`s4/build/agent-logs/model-native-artifacts`. Seven existing Nix outputs are
rooted under `s4/build/accepted-s6-native-artifacts`. Five additional outputs
preserve focused equivalence, combined full tests, verdict, predictions and API
reference evidence. A thirteenth root retains the successful scheduled report;
five combined acceptance logs and summaries are hash-verified under
`s4/build/agent-logs/s6-native-integration-acceptance`. Both implementation
workspaces remain until combined acceptance and publication. The equivalence
workspace dependency audit found only direct store symlinks and no references
to either implementation workspace.

The complete integration review failed twice because the Claude CLI OAuth
token expired, not because of source findings. Both failure records are retained
in `c19670b0`. On 2026-10-25 the credential metadata showed a refresh, and the
retry succeeded: review `20261025T001053Z-5bc323f0` has no findings for the empty
merge of the previously reviewed parents. Reviewer access is restored for the
pending source units above. Complete S6 full/verdict/prediction and task-end
checks are running as root session `24501` in `s6-complete-publication`, using
slot 1. Shared S5 search review of `efa0d465` found zero musts and one policy-list
should; the correction and its acceptance are recorded below.

On 2026-10-25 the editor compatibility check exposed an S5 import regression:
the global `ToExpr Output` instance in `CheckReplayData` changes the existing
guide's `#eval` rendering. The `s4_part1` worker corrected the instance scope in
an isolated workspace based on `6228f90a`, keeping the guide expectations and
checked replay intact. Seven focused Nix checks pass at
`pncn74lcx9si588ivscx36cn3micnf05`; source `b5f15c67` has a clean review.
The separate policy-list correction passes three focused search checks at
`82xlqm0788nqy2hfwz6ymzgc8j0jhcxw`; source `ac077b90` has a clean review.
Both corrections and their records are frozen at `bf3fa71f`.

The editor's real Lean-server fixtures now pass in Nix at
`8d538sd8bf49gx9qqnrd8rimpcaxbs27`: both LF and CRLF cases, with zero failures,
errors or skips. The tested source is `44b4286c`; its production files are
unchanged from `a075cb27`. The retry adds the pinned timezone-data path to the
surface test derivation after the server watchdog failed to find UTC. The
editor source is at rest with no reserved build slot. Compatibility, independent
review and part acceptance remain open. The editor worker will integrate the
checked S5 correction through a new merge, then run the combined focused checks.

The read-only table-rebuild readiness audit is complete in the workspace's
modularity research notes, with 28 bounded pinned-native probes. Index choice
can change partial writes and error precedence even with total `ORDER BY`;
the transfer optimization can also preserve source rowids. The owner has been
asked to choose possible executions (coordinator recommendation), a proved
plan-independent restriction, or exact pinned planning. No production or task
contract has changed before that answer. The read-only audit has no live process.

Reviews recovered on 2026-10-25: stored-view source `694d0790`, search/view
integration `6228f90a`, and search/execution integration `3a632d10` have no
findings. Their retained review records are at `7e458081`, `bc55cdc1` and
`c71360eb`. Enforced-DROP source `dd60f94c` has no source findings; its two
status corrections and review records are at `ffe4d749`. SQL-doc source
`3bb4171e` has one diagnostic-text should; its approved correction is prepared
and awaits a build slot. None of these results completes its enclosing task.

The migration descriptor review is complete at `48bc5237`. Its next comparison
and pattern unit is assigned under the unchanged reviewed task and owns slot 2.
The new production leaves compiled; focused fixtures and Nix acceptance remain
pending. Editor integration and the doc-message correction are next in the queue.

The next S5 unit is assigned to `s4_part1` under the existing reviewed S5 task:
`#sql_check`, searched `sql_refute`, and certified result display, with explicit
input primitives and bounded resource controls. Use a new workspace on
`bf3fa71f`; preserve the old `s5-commands` draft until intentionally reused.
Reuse the shared checker and keep explicit refutation available. Command and
tactic fixtures must establish all three outcomes and original-claim replay;
measure command cost before choosing the default budget. Automatic theorem
checks and editor actions remain the later part. This unit has no build slot yet.


PR #250 is published on #249 as `tasks/s6-execution-contracts` at `9ac05c46`.
The checked source is `5bc323f0`; the completion record `70f5fc28` has a clean
independent review. The execution-contract and native-artifact tasks are DONE.
This completes those tasks, not S6 or ADR17. Complete Nix acceptance has 937
passing full checks, 71 Nix checks and 47 scheduled checks. The verdict is
4,869 AGREE and 2,503 MODEL_UNSUPPORTED; all 53 prediction files and 7,372
cases are unchanged. The existing PR #249 general-mutant CI failure remains
open and is not claimed fixed by #250.

Fifteen complete acceptance logs, summaries and the PR body are hash-verified
under `s4/build/agent-logs/s6-complete-integration-acceptance`. Two additional
roots under `s4/build/accepted-s6-native-artifacts` retain the complete full and
surface reports. Existing roots retain the shared verdict, predictions,
scheduled checks, API documentation and native-artifact measurements. Completed
implementation workspaces are being audited for retirement after publication.

The second migration-pattern unit is checked at `2ed8463e`: three focused Nix
groups with 160 standard-axiom reports pass at `4ngn8pikwbsql2fqflbvmgc7gz6crxm9`.
Review of `838aa29e` has no source findings; its status provenance correction
is recorded. The worker continues the approved composition and frame laws
under the same task, without a reserved heavy slot.

The editor integration at `495d7693` passes 23 focused Nix checks at
`pfqbwzf1dvcfbdjzhl2fyavl3fwca3dv`. Independent source review found only two
missing module overview comments. Their correction passes both real-server
checks at `bzy1b1fwjxlk3m36r0kbirncv3j7jrq6`; final review is pending. Slot 1
remains reserved for that worker and the queued SQL-doc message correction.
The S5 command/tactic frontend worker now owns slot 2 for its first build and
measured command checks. Neither enclosing task is complete.


The four published S6/native workspaces have been retired: `s6-execution`,
`s6-equivalence`, `model-native-artifacts` and `s6-native-publication`. Each had
an empty working copy and a parent contained in published `9ac05c46`. All
three active workers confirmed no process or dependency on those paths; the
filesystem audit found no external symlinks. The editor worker also checked
298 surface ELF libraries. An additional 132 logs/probes are hash-verified in
`s4/build/agent-logs/retired-s6-workspaces`, with a cleanup record.

Editor source and reviews are frozen at `8ca6d7ae`; full part acceptance is
still queued. SQL-doc diagnostic correction is checked and reviewed at
`8a83a65b`, with two passing focused Nix tests at `8arqjd5l5jlnvg5v148gimnk0gbijzrp`.
Both tasks remain OPEN. The worker is assigned the reviewed fromless mutant
repair at `plans/20261025-fromless-mutant-repair.task.md`, independently on
published #250. Slot 1 is now available to the migration law worker's focused
gate; mutant repair follows. S5 frontends retain slot 2.


The migration composition/frame boundary is checked and reviewed at `6da0f67b`
(implementation `c398676a`). Its focused Nix check passes three groups and
201 standard-only axiom reports at `x6cp3k3a7vlx9z8k0jrhdzcllm4bls22`. The
worker continues the remaining public law and notation unit under the existing
task; universal model-dependent examples remain deferred. It has no heavy slot.

The fromless mutant repair now owns slot 1 for the bounded harness and relevant
mutation checks. S5 frontends retain slot 2 for their 14 selected Nix checks.
The copied proof script has also been checked with a user binder named kernel;
this local diagnostic is not Nix acceptance. PR #250 hosted Verdict is green,
and its Linux API-reference build passed. Other CI jobs remain running.


At 2026-10-25 00:58 UTC, PR #250 hosted Linux main, table-mutant,
function-mutant and Verdict jobs have passed. The general-mutant job remains
running; the confirmed fromless fault is addressed separately below.

The fromless repair source `e4265048` is independently reviewed with no
unresolved findings; review/status head is `0ee899e6`. Its 12 focused Nix
harness cases pass at `zv6n9rjksjqnzpqwiays4igjxzrcimmx`, and 52 focused
mutation/inventory checks pass at `n02c574s3rvy5vzz0bkja5avrigcha4a`. Every
existing fromless and representative parameter fault is killed. Full task
acceptance is running as agent session `83904` in slot 1; publication waits
for that sequence. Protected production and evidence trees remain unchanged.

S5 frontends passed 14 focused Nix checks at
`l8igz2np850nzkkgp0apq1bv19fawwhw`; the environment-only follow-up passes at
`mhiwy40jrnpdscjl2b8y9hs0mvzlnar4`. Source `aca8d84d` review found only missing
observable coverage for nondefault search options. That follow-up is running
as `9352` in slot 2. Default command budget is 100,000 Lean units; expensive
targeted cases use explicit 500,000 units. Automatic checking remains later
work and has no responsiveness claim from these command measurements.

The next migration unit has public pattern syntax, quiet descriptors,
explanations and application-composition conveniences. Its source is frozen
at `4c68ae69` after two failed bounded dev-build attempts. The remaining
corrections are untested; it has no reserved slot or live process. Both slots
currently serve the acceptance work above. No semantic specification error was
found. Stored-view completion and universal model-dependent examples remain open.


S5's nondefault-option follow-up is checked at `7e6f194c`: the Nix check at
`q5flkif5f52xdjilcg2a6wf932jhp3ww` passes its selected case. It covers seed,
random sample count, maximum rows, shrink attempts and a size-sensitive custom
Plausible generator. The default SQL sampler is size-independent. Independent
review `20261025T010407Z-7e6f194c` has no findings. Recorded source boundary
`c13c9e20` is frozen while part 2 full/verdict/prediction acceptance runs as
agent-owned session `41484`, in slot 2. Automatic checking has not started.

The fromless repair retains slot 1 for full acceptance session `83904`.
Migration source `4c68ae69` remains frozen and queued for the next available
bounded build slot. Editor part 2 readiness identifies reuse of the existing
real-server harness and a narrow shared resolution-observation boundary;
no editor observer implementation is assigned yet. PR #250's general-mutant
job remains running; its other Linux and Verdict successes are unchanged.


S5 part 2 gate `41484` stopped before Nix full/verdict: its source diagnostics
had 470 passes and two stale mutation-anchor failures inherited from view
integration. They are `fromless_star_accepted` and `outer_row_dropped`. The
command source remains `c13c9e20`; part 2 is not accepted. The worker merges
reviewed repair `0ee899e6` without rewriting ancestors, then updates the two
star predicates to `namesVisible` and the correlated-row anchor to
`outer.take query.outer`. Replacements, targets and guard obligations remain
unchanged. Protected production/evidence trees match `c13c9e20`. Local harness
checks pass, but focused Nix acceptance and independent review are pending.
The repair workspace on published #250 remains frozen and separate.

Slot 2 now serves migration syntax/law validation. Preflight found and corrected
an explanation path that could continue after a failed query-admission proof;
the command disables error-to-sorry recovery while elaborating and synthesizing
its claim. Fixtures also establish an inhabited composition domain and
behaviorally distinguish the default SQL guard from the complete comparison
environment. Explanations print the written claim and plain segment descriptions
instead of model AST records. These changes stay within the existing task.
Focused Nix acceptance and independent review are pending; the slot returns to
S5's targeted mutation checks after that focused gate. No part is marked DONE.

After S5 part 2 acceptance, the worker can merge reviewed editor `8ca6d7ae`
(common ancestor `bf3fa71f`) and reuse its real-server harness for automatic
checking. The editor's own required part 1 full/verdict gate remains queued;
focused harness reuse does not discharge that separate acceptance obligation.


PR #251 is published on #250 as `tasks/fromless-mutant-repair`, head
`fe169099`, and is in stack 231. The repair task is DONE. Reviewed source
`e4265048` passed 949 full Nix tests, 71 Nix checks and 47 scheduled checks.
Verdict is unchanged at 4,869 AGREE / 2,503 MODEL_UNSUPPORTED; all 53 files and
7,372 predictions are identical. Completion review `20261025T012631Z-52e98fd1`
has no findings. Hosted CI for the new PR is separate acceptance still pending.

Hosted #250 general-mutant job 121029975402 (run 40146867734) is now failed.
Its log reports query, fromless and JSON-function group failures, followed by
outer timeout exit 124 before the final pytest failure details. No general-mutant
report artifact was produced. The raw log is retained under
`research_notes/Lean model modularity investigation/ci249-mutants/ci250-mutants.log`.
The new repair addresses only the confirmed fromless fault; query/JSON causes
remain unconfirmed. Linux main/API, table/function mutant and Verdict jobs pass.

Completed publication workspaces `s5-publication` and `s6-complete-publication`
are retired after empty-source/published-parent and dependency checks. Their
28 evidence files and 14 store roots are retained under the S4 workspace's
`build/agent-logs/retired-publication-workspaces` and
`build/accepted-publication-evidence`. All active agents confirmed independence;
2,400 shared libraries had no dependency on the removed paths. The published
fromless workspace is also retired: 29 evidence files and eight store roots
are under `build/agent-logs/fromless-mutant-repair-acceptance` and
`build/accepted-fromless-mutant-repair`; 2,287 libraries were checked. Cleanup
records and hash manifests are retained. No store garbage collection ran.

S5's three mechanical view-anchor corrections passed 12 Nix harness checks and
52 named mutation/inventory checks, including all four fromless and four
subquery faults. Integration `d280c408` review is clean; recorded head `1fb9c741`
is frozen in post-review full/verdict/prediction retry `96340`, slot 2. Its
source prerequisites now pass, including both formerly stale guards. Editor
integration still waits for part 2 acceptance.

Migration public meanings/laws/notation source `162849ad`, recorded head
`317cdb1a`, has clean review and 10 focused Nix checks with 225 permitted-axiom
reports. Part 1 full/verdict `18258` now owns slot 1 in the frozen original
workspace. Separate `s6-migration-examples`, based on `317cdb1a`, prepares the
complete counter refutation and universal normalized-field proofs under the
existing task. Those examples need proof closure, not missing SQL execution
features. Complete rebuild/cascade/affinity examples still need the pending
query-copy/rename/FK work. The example source is not yet compiled or accepted.

The former repair worker resumes the existing query-sources task in
`query-sources-view-integration`, starting with published #251 and the same
three checked anchor spellings. It owns remaining view DDL, pragma metadata,
write errors and statement/catalog preservation. It has no heavy slot while
S5 and migration full acceptance run. The migration worker's separately reserved
normalization proof leaves and registration entries remain disjoint.

Migration part 1 full/verdict gate `18258` passed: 946 full Nix tests and
4,869 AGREE / 2,503 MODEL_UNSUPPORTED. Evidence head is `467cdde5`.
The example workspace carries that status-only descendant and now uses slot 1
for bounded counter development/focused Nix gate `45610`, source `402cf053`.
Its fixture compares complete public runs, proves an inhabited migration domain,
and checks both retained-trigger scripts against pinned native SQLite. Acceptance
is still pending. S5 gate `96340` remains live in slot 2; its model suite passed
all 251 tests, with package, sample and surface groups remaining at this update.

View integration `c3e4346f`, recorded as `05c4d214`, has clean review and exact
Nix derivation reuse for the 12 harness and 52 mutation/inventory checks. No view
production edits followed it. That worker now owns the immediately reviewed
`20261025-mutant-failure-diagnostics` task in an isolated workspace on published
`fe169099`; carried task/review head is `a2f68a27`. It can edit and review while
both heavy slots are occupied. The task keeps passing coverage and all limits,
and exposes an already reported failure before later groups consume the budget.

PR #251 hosted mutation jobs are skipped by the existing change filter, despite
their successful job status. This is not hosted mutation acceptance. The new
diagnostics task requires the existing manual CI trigger after publication so
the actual mutation commands execute. No change to CI routing is planned.

The complete expansion counterexample is now checked and reviewed: source
`5600ba9e`, evidence head `b967224a`, review `20261025T014239Z-5600ba9e`
with no findings. Nix report `i2w0ml50phaipdzksffjd79sy4csszh2` contains one
passing native/kernel fixture and no errors or skips. Seven kernel facts use
only permitted axioms; both execution orders give equal complete databases and
application outputs, with total-change counters 3 and 4. This establishes the
concrete full-commutation refutation, not the remaining universal examples.

The migration worker is preparing the separate normalization row/query lemmas:
NULL/TEXT storage and comparison laws for every Value, the exact appended-cell
update under structural premises, and old-versus-normalized query equality for
arbitrary admitted rows and parameters. The complete expansion's successful
effects and all branches still need to establish those premises. It has no
heavy slot while the following two acceptance gates run.

Diagnostics source `e148e0e4` has clean review `20261025T014300Z-e148e0e4`.
Frozen evidence head `10aa47c3` runs full/verdict/prediction/Nix/scheduled-checks
in slot 1, owned handle `11589`. All eleven ordinary suite commands are
byte-identical; each mutant command gains only `--exitfirst`. Source inventories,
limits and protected trees are unchanged. S5 `96340` remains live in slot 2,
now in its surface suite. PR #251's hosted Verdict passed; its Linux API build
remains in progress. Hosted mutant jobs for that PR were skipped as noted above.

S5 gate `96340` ended with exit 124 at the unchanged 1500-second full-suite
limit. No test reported a failure; surface reached 89%, after the frozen,
harness, model, sample and package groups passed. The original log is retained.
One sequential cached retry, `20553`, now owns slot 2 at the same frozen
`1fb9c741`, with unchanged source and limits and separate `*-cached.log` files.

At the owner's request, the three still-pending decisions were restated together:
extend FK execution for non-NULL ADD COLUMN defaults; keep automatic SQL-file
root discovery with an explicit relative override; and represent plan-dependent
INSERT SELECT outcomes. These are the recommendations, not accepted decisions.
Affected work remains paused pending the owner's answers; independent tasks
continue. The accepted named proof-body cost contract is not an open question.
