# Status: queries as sources

Created 2026-10-24. Status: OPEN. Part 1 DONE; CTEs and views remain.
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
- Independent review, frozen prediction classification
  and post-review full/verdict gates remain pending for this part. The full S4
  success fixture closure is reserved for the combined integration boundary;
  its physical-table premise correction is a separate reviewed change.
