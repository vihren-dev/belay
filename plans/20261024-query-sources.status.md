# Status: queries as sources

Created 2026-10-24. Status: DONE (2026-10-25). Parts 1, 2 and 3 DONE.
Task: [task file](20261024-query-sources.task.md).
Specs: ADR 0019 D5/slice 4 and D3 metadata exception; ADR 0017 S6.
The [part-1 record](20261024-query-sources-part1.status.md) retains its complete
implementation, review, prediction and acceptance history.

## Accepted scope and dependencies

On 2026-10-24 the owner selected ordinary nonrecursive CTEs only. Actual recursion
remains excluded without the RECURSIVE keyword, and that keyword remains excluded
for nonrecursive definitions too. Materialization hints remain excluded.

Part 2 continues the reviewed task in an isolated workspace on subject
`16bd87a396510fdf8e42cc0d1cf83b274d857b75`. Part-1 publication is coordinated
separately. No CTE or view implementation is part of that checkpoint.

The source agent owns query syntax, source resolution, codecs, translation and
required existing query-proof adjustments. FK owns ParentKeys, ForeignKeyPlan,
TriggerClosure and ForeignKey proof/API files. View catalog cases and their FK
preservation closure require coordination before integration. S4 owns its new
success/program modules. Full maintained SuccessBalance fixtures will be checked
at a combined integration boundary after resolver changes.

## Checked part-1 boundary

Final combined acceptance boundary: `c8db1a54ff74c7c7f033aee61c041e9bc5668ac8`.
Subject-only final status head: `16bd87a396510fdf8e42cc0d1cf83b274d857b75`.
Separate evidence/status head: `5d69e3fa8025ef51b7be11a7d41f6464bb942b51`.

- Post-review full gate: 854 Nix-selected tests passed, at
  `/nix/store/m64rgzasy2aqvp6d421pk5yh0v4654b9-sqlite-verifier-test-reports`.
- Final verdict passed at
  `/nix/store/6nazink0rsrzhv7458rs3vgfs63c48dg-sqlite-verifier-verdict`.
- Combined predictions:
  `/nix/store/q4qrigjpa82cg89ggzkvinbnvmgi7pq6-sqlite-verifier-predictions`.
  All 54 files match the earlier checked combined predictions byte-for-byte.
- The subject prediction baseline before CTE changes is
  `/nix/store/xar2y93h71ffx1ccrjvy906936hk4ahj-sqlite-verifier-predictions`:
  53 corpus files, without the unpublished v53 evidence.
- Measured gains: v4 has 675 agreements; v5 has 2,973. Draft v53 has 38 agreements
  and four model restrictions. Every prior agreement and claim survives.
  The separate evidence report classifies all 76 changed historical records.

Corpus v53 is now complete with CTE and view evidence (178 cases; see the last section).
Frozen corpus, claims and lock changes stay in their separate owner-approved judge
PR. Task-end Nix and scheduled checks remain required after all three parts.

## Part 2 progress

- 2026-10-24: carried S4's reviewed generalizations of `resolveSources_table` and
  `resolveSources_tableInfo` from `656ab790ecaf3a00a36f710f728d5913b2c7fd64`.
  Their defaulted callback and prefix parameters follow the existing hypotheses.
  Existing callers remain valid; copied source queries can supply their own
  expansion callback and diagnostic prefix.
- Two maintained consumer examples from S4 review boundary `1dee994a` now live
  in `tests/surface/ClaimsDerived.lean`, without its unrelated SUM fixture.
  The focused Nix surface check selects `derived_sources` from the normal suite
  and passed at
  `/nix/store/9zkv499mbvg2cwcs5jnn351rv253zfsd-sqlite-verifier-test-query-source-callback-carry-1`.
  It compiles the consumer against this source's built model, text and surface
  packages. The carry changes proof statements and consumers only.
- Carry review `20261024T164800Z-0559f47b` found no must issue and one should
  issue: the retained part-1 history needed an explicit historical label. Its
  header now states Part 1 DONE and links to this active task status.
- Part 1 was published separately as PR #243, source
  `1f5eea9e0c3ecd8a5fb62940b3976708909fdb29`, above PR #242. This implementation
  workspace remains on the checked carry and does not rewrite that published
  ancestry.
- Ordinary WITH now has indexed syntax metadata, JSON/Lean codecs and text
  translation. Each used definition becomes an ordinary derived query at its
  use site. Lexical WITH lookup follows the written definition scope; column
  lookup follows the use site's permitted enclosing scope. Explicit column
  lists replace output names while retaining each resolved column's metadata.
- Recursive UNION arms use preparation-only name placeholders, then ordinary
  resolution checks their column counts and names. Prepared recursion ends in
  `recursive-common-table` before evaluation. Circular references, repeated
  recursive references and recursive aggregates retain SQL preparation errors.
  Unused definitions do not enter the executable query list.
- SELECT and supported VALUES INSERT, UPDATE and DELETE share the expansion.
  Trigger expression queries also use it. The existing `keyReady` restriction
  on nested writes with subqueries remains: the public fixture distinguishes
  successful preparation from the runtime stop.
- Existing query-resolution and catalog/schema-link proofs cover the new
  syntax field and wrapper. The specific no-WITH resolution lemmas state that
  premise explicitly. No alternate evaluator or catalog object was added.
- Authored input definitions cover 43 CTE cases, with parser/span fixtures,
  kernel context and public quotation examples, and two targeted scope and
  recursion mutants. Frozen v53 evidence remains separate and unpublished.
- Focused Nix acceptance passed: 32 model/parser/native differential tests at
  `/nix/store/m35i7is1gmyiwy76c5lskzbpr810xhmr-sqlite-verifier-test-common-tables-model-1`,
  17 public surface fixtures at
  `/nix/store/fx2h7dkcm5z3q88q61sv37r9dwgvxrr5-sqlite-verifier-test-common-tables-surface-1`,
  and all 60 restriction examples at
  `/nix/store/nc6ks1rv3jyzvyjcyp9pw5527m0ismh6-sqlite-verifier-test-common-tables-restrictions-1`.
  These use the existing registered suites with focused selections.
- Both targeted mutants were killed in Nix: removing lexical parent lookup and
  removing recursion registration each changed the selected native verdict.
  Report:
  `/nix/store/zdn3s51b8gyns4r7z3bdqq77v7gyfdnf-sqlite-verifier-test-common-tables-mutants-1`.
  The following source edits only clarified the WITH behavior in the public
  write and trigger entrypoint docstrings; executable definitions are unchanged.
- Implementation commit `1a1848b12f9af98a6db77dce8dd5e72acb68d868` passed
  independent Claude review `20261024T190005Z-1a1848b1` with no findings.
- Part 2 acceptance below uses a combined CTE, reviewed S4 and FK boundary,
  including the maintained full S4 success fixtures and resolver adjustments.
  S4's physical-table premise correction remains a separate reviewed change.

## Combined part-2 acceptance

The integration workspace joins CTE review carry
`80b4cb5e86725b7168a3894b4e804a030b34b473`, S4 source
`24ca8b4c9635ee14f3235001dc86d7315ac514ac`, and FK review carry
`9350aa3147e92cf27fe59c00750fd638440494ba`. It contains no view behavior.

- The model manifest retains every new parent entry and the FK removal of
  the replaced `ForeignKeysHold` module. The resulting manifest has 379 entries.
- Five maintained S4 fixtures account for the no-WITH expansion branch and
  the explicit ordinary-query premise. Their public success formulas retain
  the separately accepted physical-table premises.
- ADR 0019 D4 carries the exact streaming/materialization section of reviewed
  owner-decision commit `1c6eeb5ee995118c4635d48f3f969ee64a2ed8b2`. This is
  specification synchronization; this checkpoint adds no INSERT SELECT support.
- Published part-1 acceptance history from the FK parent is retained in the
  linked part-1 record, alongside the newer active CTE progress above.
- The focused Nix integration check passed all 19 selected fixtures at
  `/nix/store/11yz0c3ypy7q42fjfb0896ag2y7whzg9-sqlite-verifier-test-common-tables-integration-1`.
  It includes the complete unique-email and balance success proofs, all selected
  query-claim consumers and the translation checks. The S4 physical-table
  premises and the existing axiom restrictions are unchanged.
- The accepted derived-source predictions at
  `/nix/store/2kpi159rivfybjqkv2cw7vxh31qpdlbq-sqlite-verifier-predictions` and the
  S4 predictions at
  `/nix/store/ifmznfzpqyd12dxjhr3yp404ljb0dgxy-sqlite-verifier-predictions`
  were byte-identical: 53 files and 7,372 cases. The accepted S4 copy is the
  comparison baseline below; the historical derived store path later disappeared.
- Combined source `4e8d9b296d63c7acbe302ebd1c54385d203b2b3d` passed independent
  Claude review `20261024T192443Z-4e8d9b29` with no findings. No view behavior
  is part of this boundary.
- The first combined full-gate attempt ended with exit 124 at the configured
  1,500-second aggregate Nix suite limit. Session `65827` reached 40% of the
  72-test public surface suite without a reported test failure. The preceding
  Nix model suite passed all 251 tests in 1,041.50 seconds at
  `/nix/store/sbkyci4g6afx2lrry8sdvpv9ywzgmmkp-sqlite-verifier-test-model-1`.
  That attempt's full report was incomplete; verdict and comparison did not run.
  It is not acceptance. The retry below retained the source and all timeouts.
  The attempt log is
  `/tmp/query-source-cte-integration-full.log`.
- The cached retry, session `44795`, exited 0 on the unchanged reviewed source.
  Its post-review Nix full report passed all 923 tests, with no failures, errors
  or skips:
  `/nix/store/6ccraalbxszhkp504g0q4d1fi49160bs-sqlite-verifier-test-reports`.
- The final verdict passed: 4,869 AGREE and 2,503 MODEL_UNSUPPORTED, at
  `/nix/store/afn513ampmbdfjr467cm90dydkyirkd1-sqlite-verifier-verdict`.
  All prior claimed agreements survive. Corpus v4 has 676 agreements; v5 has
  2,974. Each gains the same trigger-creation case under its execution profile.
- Accepted predictions:
  `/nix/store/wbpwn1x38fyn3l0g00wg5m011n6ajwq4-sqlite-verifier-predictions`.
  Compared with the accepted S4 baseline above: 53 files, 7,372 cases, 50 files
  byte-identical. All 4,895 previously predicted records are unchanged. Of 71
  changed records, 69 remain unsupported with only their reason changed, and
  two become agreeing predictions. The [complete classification](20261024-query-sources-cte-predictions.status.md)
  records each changed case and the baseline-equivalence evidence.
- Part 2 is DONE at this checkpoint. Views remain OPEN. Corpus v53 remains
  unpublished and mutable; no frozen corpus, claim or judge-lock file changed.
  Task-end Nix and scheduled checks remain required after the view part.

## Publication above the FK prerequisite

The publication workspace joins reviewed CTE boundary `58300b39` and published
FK prerequisite `b1130903` (PR #247). It retains both prototypes from PRs #245
and #246. All files under `packages/` are byte-identical to the CTE boundary,
including its precise SimpleQuerySteps and StatementCalm documentation.
The model manifest resolves to the same 379 entries. The test inputs retain
the proof-cost helper and register both prototype suites. The earlier FK
review record remains in the append-only review history.

The static ownership, surface-layer and documentation checks passed 16 tests.
The final publication integration passed all 36 selected Nix cases, with 44
deselected, in 194.19 seconds:
`/nix/store/2zlr1pgsarrvmq8b0apzx8pbh0mhvffj-sqlite-verifier-test-cte-publication-1`.
This checks the CTE/query consumers, both S4 guide proofs, all nine FK fixtures,
and the S6/proof-cost prototypes. Independent integration review
`20261024T200939Z-57bf72e2` found no findings. The completed full gate and verdict
are recorded under "Combined part-2 acceptance" above; the
[classification record](20261024-query-sources-cte-predictions.status.md) lists
every prediction change. This publication adds no view behavior.

Acceptance-documentation review `20261024T201724Z-ed535519` found zero musts
and two status-wording shoulds. The classification record names the retained
S4 log archive and artifact roots after retirement of the publication workspace.

## Part 3 progress

The [view record](20261024-query-sources-views.status.md) holds the part-3 history. Part 3 is DONE.

Task-end acceptance on the integration `431cdd16` (the v53 evidence line above the checked SQL doc blocks;
parents `e32ae362` and `3d0ab903`), all through Nix:

- `just test-full` exit 0: `/nix/store/q3dn28cw4b8bn44zfz6sl1zia94vpndz-sqlite-verifier-test-reports`.
  The first run stopped at the 1500 s build limit without a failed test (log
  `build/agent-logs/v53int-test-full-timeout1.log`); the rerun passed.
- `just verdict` exit 0: `/nix/store/gz1wg4l0969wpihb402jjayih440m13x-sqlite-verifier-verdict`.
- `just test-nix`: 71 passed, 1,802 deselected.
- `just test-scheduled-checks`: `/nix/store/j4lq1v2g0x3gns40acg8xsbzfgfy6lzx-sqlite-verifier-scheduled-check-reports`.
- The integration review `20261025T142047Z-431cdd16` had one should finding (the corpus-format document),
  fixed with the prediction classification below.

[The part-3 prediction classification](../reports/20261025-query-sources-part3/README.md) compares the view
predictions `bi8dvn7z` against the accepted CTE baseline `wbpwn1x3`: 48 of 53 files are identical, 402 records
change (97 unsupported to predicted: 93 AGREE and 4 declared out of scope; 305 only change their reason or
restriction), and every previously predicted record is unchanged. The final v53 predictions differ from `bi8dvn7z`
only in `corpus-v53.jsonl`.

Accepted restrictions at completion: see the [task file](20261024-query-sources.task.md). The corpus, claim and lock
changes (judge commits `2ffa2b19` and `f7cfc95b`) need owner approval in the separate judge PR before merge.

## Judge evidence for CTEs and views (corpus v53)

The evidence workspace joins the draft v53 line (`5d69e3fa`) with the published view head
(`6a0bc6be`, PR #255) by merge `18dcbaac`; it has two text conflicts (the module list of
`build-support/tests.nix` and this status file) and no rebase. Corpus v54 is reserved by the FK work and
is not used. Judge commits need owner approval: `2ffa2b19` (recorder, `judge/catalog.py`,
`judge/records.py`, lock) and `f7cfc95b` (v53 corpus, claim, lock). The refactor and test commits between
them follow reviews of these two.

Recorder gaps closed (judge-side code, with tests):

- A `CREATE VIEW` over a missing table, a cycle or `new.a` succeeds natively and fails only when the view is read.
  The recorder keeps such a view as an `unreadable` entry with SQLite's primary code and message. Only SQL errors
  count as evidence; a timeout or I/O failure is raised. `judge.catalog` compares the primary code. The model
  predicts the same code (`ViewObservationIssue.failureCode`); a body that fails at run time stays unsupported.
- `judge.records.subject_input` forwards `setupClockUnixMilliseconds`; the model uses it for the first observation.
  Without it a view with a clock function stays unsupported.

Corpus v53 now has 178 authored cases: 42 derived-source, 52 ordinary CTE (nine new: shadowing in compounds,
IN subqueries, UPDATE and INSERT targets; an output alias; and four documented refusals of MATERIALIZED,
NOT MATERIALIZED and the RECURSIVE keyword) and 84 view cases. The view cases cover CREATE and DROP VIEW with
IF EXISTS and IF NOT EXISTS, name collisions, column lists, nested views, metadata through views, joins,
aggregates, compounds, subqueries, CTEs, late binding, cycles, broken views, `table_info`, writes and their
errors, and transactions. The claim forbids DISAGREE and HARNESS_ERROR and requires 158 agreements. The other
20 cases are MODEL_UNSUPPORTED with a documented reason: recursion (5), RECURSIVE and hints (4), uncertain
membership and fallible bodies (6), a written-table subquery (2), PRAGMA `table_xinfo` and `table_list` (2),
and INSTEAD OF triggers (1).

Nix evidence for the final source (`90399012`):

- Full tests: 1,020 tests, no failure, `/nix/store/99wphi628c4l897r12q6wis9qclcw6y3-sqlite-verifier-test-reports`.
  The first run failed one test: the frontend refuses the four new CTE refusal cases before the model, so the
  kernel boundary check has no case for them. The test now asserts that refusal; the failed log is kept in
  `build/agent-logs/failed1/`.
- Verdict `/nix/store/11ha0p1bg9g6bkvf72mxcpqhdva1z271-sqlite-verifier-verdict`: no DISAGREE, no HARNESS_ERROR.
  v53: AGREE 158, MODEL_UNSUPPORTED 20.
- Predictions `/nix/store/cdglbidddydm09iw1i5hc7bdl2m51b0f-sqlite-verifier-predictions` against the baseline
  `/nix/store/da3k2rw7vk2f8mqa7j3nzrs4wnwxmd0g-sqlite-verifier-predictions` (merge `18dcbaac`): the 53 other
  files are byte-identical, and the 42 old v53 predictions are unchanged. Only v53 grows from 42 to 178 cases.
- `just test-nix`: 71 passed, 1,590 deselected.
- `just test-scheduled-checks`: 48 passed,
  `/nix/store/c2yyckm3kdcrmm5aklgd5si3zwmszx6b-sqlite-verifier-scheduled-check-reports`.

Reviews: `20261025T104917Z-2ffa2b19` (one must, one should, fixed), `20261025T105508Z-9fc379e3` (one must, fixed),
`20261025T105615Z-cf8b7f97` (clean), `20261025T105903Z-f7cfc95b` (two shoulds, fixed),
`20261025T110006Z-115c5e8e` (clean), `20261025T112338Z-90399012` (clean). The merge `18dcbaac` has no review.
The stale reason "as the model has no views" of INSTEAD OF triggers
(`packages/belay-sqlite-text/Belay/Sqlite/Translation/Triggers.lean`) is not changed here, because it would
change existing predictions.

