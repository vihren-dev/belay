# Proof refactor acceptance repair status

Date: 2026-10-28. Status: IN PROGRESS.
Audience: the implementation team.
Task: [restore acceptance checks](20261028-proof-refactor-ci.task.md).
Source baseline: PR 295, `e8f46dae`; production `3e2212ed`.

## Native replay diagnosis and repair

The model producer already supplies all required native artifacts. Pinned
Lake 4.34.1 expands wildcard module selections through unsorted directory
enumeration (`Lean.Util.Path.forEachModuleInDir`). Its library builder collects
native objects in that order, and the order contributes to the saved link trace.
Thus relocation between filesystems can invalidate the shared facet while each
module and native object remains current. The direct and installed local replay
orders agree; the hosted failure is the acceptance case for relocation.

The producer manifest now uses explicit names for the four former wildcard
selections. It retains all 874 modules of the `Belay.Sqlite.Model` library.
The package's other four modules are `Codec`, `Codec.Resolution`,
`Codec.SyntaxJson` and `Codec.StatementExamples`, each under `Belay.Sqlite.Model`:
878 package modules in total. Both library declarations remain.
No source, object, output trace or installed-package permission is rewritten.
The existing package replay test checks the configuration that avoids this
failure, then requires the real immutable native facets to replay. Retire the
configuration guard when the pinned Lake sorts wildcard expansion.

The installed fixture and its seven consumer test files are unchanged. The
focused Nix invocations select existing tests from `packages`, `surface` and
`surfaceS6`; their source inputs, runtime, environment and deadlines stay intact.
No test owner or permanent runner was added.

## Resolver measurements

The existing resolver test is parametrized by each mutant's edited source file.
The parameter set and each selected table come from the same unchanged `MUTANTS`
mapping. Equality with exactly one file assigns every mutant to one group, with
neither omissions nor duplication. Each measurement retains all 16 authored
cases, the original 2,000-column-case exclusion, unchanged-model agreement, and
the assertion that every mutant changes a verdict. No timeout or harness code
changes.

| Edited file | Mutants |
| --- | --- |
| `Identifier.lean` | `non_ascii_fold` |
| `Resolution/AddColumn.lean` | `constant_column_limit`, `no_too_many_columns`, `no_duplicate_column`, `no_such_table` |
| `Resolution/Definitions.lean` | `desc_rowid_alias`, `table_index_same_name`, `no_table_exists` |
| `Resolution/ResolveStatement.lean` | `rollback_keeps_catalog` |
| `Resolution/TypeAffinity.lean` | `affinity_order` |
| `SqlAdvance.lean` | `commit_without_transaction` |

## Acceptance

The new Nix model output is
`/nix/store/mfdl4l49m8lv5phl38hmyxfsgdb9gm86-belay-sqlite-model-0.1.0`.
It contains 878 Lean module artifacts and 878 native objects. Current Nix checks:

| Existing owner and selection | Result | Report under `/nix/store/` |
| --- | --- | --- |
| `packages`, all native replay checks | 3 passed, no compiled targets | `lc9hq9b2mrs3yxjh97z0pzvmgk53xlds-sqlite-verifier-test-packages-1/junit.xml` |
| `surface`, SQL files, roots, records, Lake inputs and proof-cost reports | 24 passed | `fzpdbv90f2mmf3j0pw3hh6rhs6l7w69g-sqlite-verifier-test-surface-ci-repair-1/junit.xml` |
| `surfaceS6`, SQL checker and checker-root tests | 6 passed | `p5gl3ssaaxy7gavx9vr388glwma5a6x6-sqlite-verifier-test-surfaceS6-ci-repair-1/junit.xml` |
| `mutants`, resolver file only | 6 passed; all 11 mutants killed | `ib7rp3hpzj5gils5sjaqbpnv54ax09z9-sqlite-verifier-test-mutants-ci-repair-1/junit.xml` |

These runs used `max-jobs = 1`, `cores = 3` and the hardened Nix sandbox.
The selected consumer runs use an untracked expression in
`build/ci-repair/selected.nix` that changes only the existing owner's pytest file
selection. Logs are `/tmp/proof-refactor-ci-{packages-final,consumers,resolver}.log`.
The resolver measurements took 149.913, 111.811, 104.206, 86.370, 144.235 and
86.315 seconds in the table's order, with the unchanged 300-second test limit.
The selected resolver run took 682.963 seconds in total. These measured local
Nix times do not establish hosted headroom; the hosted Linux rerun remains
required. Other development builds shared this host during the run.

Native repair `15a4bd15` received independent Claude review
`20261028T114602Z-15a4bd15`: zero must findings and one should finding. The
finding requested the model-library versus codec module-count distinction
above; it is fixed. Resolver repair `33611eda` received independent Claude review
`20261028T115235Z-33611eda`: zero must and zero should findings. Whole acceptance
remains with the coordinator. The Linux hosted result is pending and is separate
from local Nix checks. PR 295's earlier API-reference and verdict successes do
not establish acceptance of this repair.

The coordinator's first combined snapshot `5540e15f` includes this repair,
ADR 0025 foundations and API, and ADR 0026 source agreement and primitive
ownership. Its first `just test-full` invocation reached the final S6 suite,
then the unchanged 2,700-second suite-build deadline expired with exit 124.
Every completed individual test passed, but the invocation did not complete
acceptance. The log is `/tmp/proof-refactor-batch1-test-full.log`.
After confirming the old build had stopped and resource checks passed, the
coordinator retried the same snapshot and limits, reusing completed Nix
derivations. The retry log is
`/tmp/proof-refactor-batch1-test-full-retry.log`; it completed with exit 0.
The aggregate report is
`/nix/store/qvp6k3y3m1f1dr452kjvf3ap8namj9hg-sqlite-verifier-test-reports`:
15 suites and 1,444 test cases, with no failures, errors or skips. Host source
checks recorded 513 tests and 49 subtests without failures. Public documentation
checked 752 modules and 5,960 authored declarations with no missing, ordinary
or unclassified declarations. The remaining gates then completed:

| First-batch gate | Result | Evidence |
| --- | --- | --- |
| `just verdict` | 56 corpora; 5,653 AGREE, 2,109 MODEL_UNSUPPORTED, no other outcome | `/nix/store/4bw2n219874pnc0wmw64937990k127np-sqlite-verifier-verdict` |
| `just test-nix` | 71 passed, including the development loop | `/tmp/proof-refactor-batch1-test-nix.log`; frozen workspace `build/acceptance-batch1/nix.xml` |
| `just test-scheduled-checks` | 50 writers checks passed; no mutant suite selected | `/nix/store/vrghz0ikwd6p6593yvkmbvbjqzsqapsi-sqlite-verifier-scheduled-check-reports` |

The Nix configuration check used independent writable copies of this snapshot's
exact Nix package caches, with all normal shell variables and tests retained.
The seed record is `/tmp/proof-refactor-batch1-cache-seed.json`; all 7,285 tracked
files retained their original hashes. Generated API-reference output is an
additional required final gate; public documentation alone does not supply it.
Later expression, context, query, resolver and profile changes still require
their own final combined acceptance.

The coordinator froze all reviewed ADR 0025/0026 implementations at
`53a346e1899f7221c67faa3c6df379862e16edb8`. Final combined checks are running
in the same isolated acceptance workspace; the earlier snapshot's reports do
not establish their outcome. Temporary migration witnesses remain in place.

On 2026-10-28 the coordinator pushed reviewed repair `16ab6ad7` to
`plans/proof-boundaries`, updating PR 295 and its description. GitHub confirmed
head `16ab6ad7c4109de6d34ba7c1d5eeb1ae0c463266`. At that publication
checkpoint, hosted acceptance was pending and the PR was open. It contained
the report/specifications and CI repairs. The production proof refactors remained
on the local integration branch for separate publication after final acceptance
and witness retirement. The later merge is recorded below.

At the 14:33 UTC checkpoint on 2026-10-28, hosted run `40702241903` had passed
Verdict at head `16ab6ad7`. In CI run `40702241901`, the Linux API-reference step
and function-mutant job had also passed. The Linux checks and other mutant jobs
were still running, so the whole hosted result was then pending.

## Hosted follow-up, 2026-10-28

The repair was pushed as PR 295 head `16ab6ad7`. Hosted Verdict run
`40702241903` passed. CI run `40702241901` passed the API-reference build,
function-mutant job and all six resolver-mutant groups. Two later measurements
failed: query-resolution mutant `no_such_column` could not compile the imported
`Resolution/OperandArms` proof, and the grouped join measurement exceeded its
300-second limit (337.49 seconds including cleanup). These are failures, not
detected mutants. The Linux check job was still running at this checkpoint.

Logs are retained at `/tmp/ci295-122864838415.log` (query) and
`/tmp/ci295-122864838065.log` (joins). Read-only diagnosis found the operand
equation imports on the classifier's path through `Resolution/QueryExprs` at
both production `3e2212ed` and repair `16ab6ad7`. The task now covers that import
boundary and bounded join measurements with unchanged semantics, mutant edits,
target mappings and deadlines. The worker assignment follows specification
review. The already-running integrated proof acceptance remains frozen.

The join measurement combines 22 mutants and 20 distinct target cases from
the existing join, USING, right-join and merged-name tables (6, 6, 4 and 6
mutants). At timeout all four workers were compiling classifier dependencies.
Source inspection supports separate measurements of those tables with the
same target mappings. Hosted timings remain to be established. The extended
task's documentation-link diagnostic passed; independent review follows.

Claude reviewed scope amendment `7b651616` with zero must and zero should
findings (`reviews/20261028T144207Z-7b651616/review.json`). The worker is assigned
the import-boundary repair and join grouping in this isolated CI workspace.
Local diagnostics may run with bounded parallelism; Nix acceptance waits for
the coordinator's currently occupied build slot. No final acceptance is claimed.

## Operand equation imports and join measurements

`Resolution/QueryExprs` now imports `OperandProjection`, the executable owner.
The equation modules remain unchanged. Their actual proof consumers import them:
`SingleSourceNameLaws` and `TableInfoLaws` import `OperandArms`;
`ExprResolutionLaws` and `ResolveReadsBelow` import `OperandArmsMore`.
All declaration bodies, theorem formulas, attributes and proof bodies are unchanged.
The classifier's source import closure contains 290 project modules instead of
292; the two excluded modules are the operand equations. This count establishes
the import boundary, not a build-time improvement.

The existing join test now has four parameters, one for each existing authored
case module and mutant table. The join, USING, right-join and merged-name tables
contain 6, 6, 4 and 6 mutants. They retain all 22 mutant identities and their
20 distinct target cases. Each measurement still records its targets natively,
requires unchanged-model agreement, and rejects every surviving mutant. Mutant
edits, target mappings, the measurement harness and all deadlines are unchanged.

Claude reviewed implementation `7da59def` with zero must and zero should findings
(`reviews/20261028T145306Z-7da59def/review.json`). The ignored expression
`build/ci-repair/operand-joins.nix` selects the existing query-resolution test from
`mutants` and the four join parameters from `tableMutants`. It preserves each
owner's inputs, runtime, environment and deadlines.

## Scoped Nix acceptance of the hosted follow-up

Both scoped Nix invocations completed with exit 0 against frozen source
`f298895c38574c55ce09d9952ada5ad3b1cbfa2b`. They ran sequentially with
`max-jobs = 1`, `cores = 3` and the hardened sandbox. The test deadline remains
300 seconds, the suite deadline 2,700 seconds, and the outer build deadline
3,000 seconds. JUnit reports contain no failures, errors or skips.

| Existing measurement | Mutants detected | JUnit test time, seconds |
| --- | --- | --- |
| Query resolution | 6 | 105.755 |
| Joins | 6 | 103.005 |
| USING | 6 | 137.376 |
| Right joins | 4 | 92.686 |
| Merged names | 6 | 141.775 |

The query report is
`/nix/store/nqvfmakynapyis9sgf068wbgcc8ai6hd-sqlite-verifier-test-mutants-operand-joins-1/junit.xml`:
one test, 105.947 seconds for the suite. The join report is
`/nix/store/mgy88i300bxja0dnw243khaf4g13n31z-sqlite-verifier-test-tableMutants-operand-joins-1/junit.xml`:
four tests, 475.032 seconds for the suite. Invocation logs are
`/tmp/proof-refactor-ci-query-resolution-nix.log` and
`/tmp/proof-refactor-ci-joins-nix.log`.

The query selection retains `no_such_column`, `no_such_table`,
`no_misuse_of_aggregate`, `no_aggregate_in_group_by`,
`no_order_by_out_of_range` and `no_group_by_out_of_range`. The join parameters
select each unchanged table once: `join_mutants`, `using_mutants`,
`right_mutants` and `merged_mutants`. The complete mutant/target mappings in
those five source files remain identical to `16ab6ad7`. Every selected target
agrees with the unchanged model, and every mutant builds and changes a verdict.

PR 295 was merged at `16ab6ad7`; these reviewed changes are a separate CI repair
for publication against main. Checked documentation and combined full acceptance
of the changed imports will run with the final post-retirement implementation.
Those gates and the subsequent hosted Linux result remain pending. These scoped
Nix timings do not establish hosted headroom or a build-speed improvement.

## Combined integration checkpoint

The coordinator integrated repair `7da59def` and its review record `f298895c`
with the reviewed proof refactors. Production sources merged without conflicts.
This status file preserves both the combined acceptance record and the hosted
repair record. The final acceptance workspace remains frozen at `53a346e1`.

At this checkpoint, GitHub completed the Linux check job in run `40702241901`
successfully, including its API-reference build. The two mutant-job failures
above occurred on that earlier head. The new import and join repairs have since
passed their selected Nix checks, as recorded above. Their hosted validation
and final combined acceptance remain pending.

The first final `just test-full` invocation reached S6, then expired at the
unchanged 2,700-second suite-build deadline (exit 124). Completed individual
tests passed. The unchanged snapshot is retrying with the same limits, reusing
completed Nix results. Its log is
`/tmp/proof-refactor-final-test-full-retry.log`. Integration of the later import
repair does not change the frozen acceptance source or establish acceptance of
this repair. The later scoped Nix results above accept the selected mutant
measurements; final combined package and documentation acceptance remains pending.

PR 295 was merged at 15:00 UTC on 2026-10-28. Fetched main `2c5fff35`
has the same tree as `16ab6ad7`; it adds the merge commit only. The remaining
CI repair was published as draft PR 296, as recorded below. The production proof
refactors remain a separate publication. The coordinator did not merge PR 295.

Independent review of integration `5bdeebf4` found one must and one should:
the earlier publication checkpoint needed an explicit historical label after
the PR merge, and a following heading needed a blank line. Both are corrected
here. These record corrections change no source, contract or test.
Claude reviewed correction `0f00220c` with zero must and zero should findings
(`reviews/20261028T151046Z-0f00220c/review.json`). Both integration findings are
recorded as fixed.

## Final mathematical-contract acceptance

Frozen revision `53a346e1899f7221c67faa3c6df379862e16edb8` passed the full Nix
suite and native verdict on 2026-10-28. All 7,345 tracked files retained their
original hashes. This revision contains every final ADR 0025/0026 contract and
the complete temporary formula witnesses. It predates the later operand-import
repair and witness retirement.

| Check | Result | Evidence |
| --- | --- | --- |
| `just test-full` | 15 Nix suites, 1,463 cases; no failures, errors or skips | `/nix/store/hhr97zwf0557py4k2iyxnrgzx222ri7n-sqlite-verifier-test-reports` |
| Source checks | 513 tests and 49 subtests passed | `/tmp/proof-refactor-final-test-full-retry.log` |
| Public documentation | 5,962 authored declarations across 756 modules; no missing, ordinary or unclassified declarations | `/nix/store/0809qly33djc1bffrai0vpd3xsvkjz4w-sqlite-verifier-public-documentation-1/public-doc-inventory.json` |
| `just verdict` | 56 corpora; 5,653 AGREE and 2,109 MODEL_UNSUPPORTED, no other outcome | `/nix/store/hi2lacnzjyzr6xxabqcslyfv8mnvar62-sqlite-verifier-verdict` |

The initial full invocation expired at the aggregate limit after 3,183.640
seconds of whole-command time. The same-source retry passed in 790.075 seconds;
S6 passed all 66 cases in 666.161 seconds. Verdict passed in 98.577 seconds.
Logs are `/tmp/proof-refactor-final-test-full.log`,
`/tmp/proof-refactor-final-test-full-retry.log` and
`/tmp/proof-refactor-final-verdict.log`.

This acceptance releases the redundant witnesses under ADR 0025 D4 and ADR 0026.
The retirement worker preserves the three identified unique premise and semantic
checks. End-of-task Nix configuration, scheduled writers, API reference, matched
dependency report and affected resolver mutants will run on the later combined
source. Its import and fixture changes also require their affected acceptance.
The accepted historical witness revision remains replayable. No final publication
or completion claim is made by this intermediate acceptance record.

## Witness retirement integration

Reviewed cleanup `e3ae5e92` is integrated at `9335618d`. It retires 26 temporary
fixtures and their registrations, while retaining the independently quantified
schema-link and subquery-depth checks and the append fault/subtype check. Its
package and test sources match the worker's reviewed source exactly. Claude's
integration review `20261028T152451Z-9335618d` found zero must and zero should
findings. The separate comparison-proof placement correction remains in progress.
Final combined Nix acceptance and publication are pending.

## Follow-up publication checkpoint

At 15:31 UTC on 2026-10-28, the coordinator pushed CI-only head `46e5a773` to
`fix/proof-refactor-ci` and opened draft PR
[296](https://github.com/vihren-dev/sqlite-verifier/pull/296) against main
`2c5fff35`. This starts hosted validation while combined proof acceptance is
prepared. The draft does not claim completed combined or hosted acceptance.
The production proof refactors remain local and will be published separately.
No PR merge was performed by the coordinator.

Reviewed documentation correction `7741beb5` is also integrated. It removes
stale temporary-fixture descriptions from two test module docstrings and changes
no test AST body, Lean source or coverage. Its independent review found no
must or should findings.

Review `20261028T153628Z-14445be0` found zero must and two should findings.
Both historical-checkpoint phrases are corrected to refer to the subsequent
Nix acceptance and draft PR publication. Both findings are recorded as fixed.

PR 296's normal pull-request scope runs full tests and the API reference, but
intentionally skips mutation suites. Their successful job labels therefore do
not establish hosted mutation acceptance. The existing manual workflow's full
scope is required to obtain the Linux mutation results on the final source.

## Final delivered-source acceptance

The coordinator freezes code and test source at
`23a3427b4d3cb071d81dae248ff870ccaa55de0c`. This includes the accepted mathematical
contracts, retired fixtures, CI import/join repairs and corrected comparison
proof ownership. The source differs from the earlier witness snapshot and
requires the final combined checks. The latest integration review has zero
must and zero should findings.

Remaining gates are full tests and verdict, Nix configuration/development-loop
checks, scheduled writers, checked API reference, a matched theorem-dependency
report, the six resolver-mutant groups and the existing comparison-mutant
measurement. The final source count uses the fixed goal baseline and counter.
The implementation will be published as a draft while these checks run, with
the existing manual CI workflow supplying hosted mutation results. Draft
publication does not mark the implementation tasks complete.

## Draft implementation publication and final source count

The coordinator pushed publication head
`9eb179dea63084ce30e69406b5cf462f894c4e33` to `tasks/proof-refactor` and opened
draft PR [297](https://github.com/vihren-dev/sqlite-verifier/pull/297), stacked
on CI repair PR 296. The publication commit adds only the freeze and review
record to final code/test source `23a3427b`. Both PRs remain drafts while their
remaining acceptance runs proceed.

A fresh standalone Nix count of `23a3427b` uses the fixed baseline's exact
scc 3.7.0 executable and 31 historical exclusions. It counts 87,018 maintained
Lean code lines: 70,876 in packages, 15,919 in tests and 223 elsewhere. Compared
with the fixed 88,030-line baseline, packages decrease by 1,323 lines and tests
increase by 311, for a net reduction of 1,012 lines. The derivation retains the
revision, file hashes, counter hash and totals at
`/nix/store/3136rk4i9jjkxf40fmm4lfdndyjw7qaf-lean-simplification-final-20261028`.
This count establishes source size only; the final capability audit remains
pending. The long-term 45,000-line objective remains open.

The final full Nix acceptance run is in progress in its frozen workspace.
Its public-documentation producer has passed for all 5,962 authored declarations
across 757 modules, with no missing, ordinary or unclassified declarations:
`/nix/store/3w2lzcyr2w0gf65chzmqyvlb3j70f3sh-sqlite-verifier-public-documentation-1/public-doc-inventory.json`.

Hosted PR 296 run `40716887931` passed its Linux API-reference step and is running
its checks; Verdict run `40716887801` passed. PR 297 run `40720732197` is building
its reference and Verdict run `40720732192` is in progress at this checkpoint.
Both PR runs skip the actual mutation-suite steps, so their green mutation job
labels supply no mutation acceptance.

Dispatching the existing full CI workflow on `tasks/proof-refactor` failed with
HTTP 403, `Resource not accessible by integration`. The coordinator asked the
owner to start that workflow or provide Actions write access. No workflow,
permission or test scope was changed to bypass this restriction. Local final
acceptance continues independently; hosted mutation acceptance remains pending.

## Completed worker workspace cleanup

The coordinator removed the nine original implementation workspaces after
checking that each working copy was empty and its parent was an ancestor of
published `tasks/proof-refactor@origin` at `9eb179de`:

- `adr25-api`, `adr25-foundations` and `adr25-preservation-context`.
- `adr26-execution-profiles`, `adr26-expression-congruence` and `adr26-primitives`.
- `adr26-query-outputs`, `adr26-resolver-certificate` and `adr26-source-agreement`.

No live process used those directories. The active acceptance workspace uses
independent package caches and immutable Nix inputs; its worker confirmed that
cleanup does not affect the run. The coordinator, acceptance, CI-repair,
retirement, comparison-correction and user review workspaces remain. Cleanup
changes no tracked source or acceptance result.
