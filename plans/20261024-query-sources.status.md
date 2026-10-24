# Status: queries as sources

Created 2026-10-24. Status: OPEN. Parts 1 and 2 DONE; views remain.
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

Corpus v53 remains unpublished and mutable until CTE/view evidence is complete.
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
and two status-wording shoulds. The raw comparison is retained under the
publication's build logs, and this section now points to the completed evidence.

## Part 3 progress

The [view record](20261024-query-sources-views.status.md) tracks the remaining part.
