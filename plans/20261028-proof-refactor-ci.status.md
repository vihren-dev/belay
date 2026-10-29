# Proof refactor acceptance repair status

Date: 2026-10-28. Status: IN PROGRESS.
Audience: the implementation team.
Task: [restore acceptance checks](20261028-proof-refactor-ci.task.md).
Source baseline: PR 295, `e8f46dae`; production `3e2212ed`.

## Current acceptance state

All local ADR25/26 acceptance items have passed at frozen source `23a3427b`;
the checked API reference passed in the source-identical hosted build. The
fixed capability audit retains all 30 groups, including every essential group.
The nine implementation tasks have completed their substantive acceptance.
Their reviewed completion records are integrated here; publication of this
change fulfills their recorded DONE condition.

Full workflow `40742662857` now supplies the requested hosted execution at
published head `bbd2eeac`. Linux's main checks and table-mutant suite pass;
the resolver and query-resolution measurements also pass before the general
suite reaches its aggregate limit. macOS exposes two individual mutant
timeouts and a default-fixture subprocess timeout. This CI task remains
IN PROGRESS to repair those measured workload failures without weakening
coverage or limits. The task now states the required follow-up behavior for
both hosted platforms. No local result substitutes for hosted timing headroom.
The later sections record final results; earlier sections are historical
checkpoints.

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

## Hosted CI-repair test acceptance

PR 296's [Linux check](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40716887931/job/122916892875)
passed. The runner checked merge `0b6da25affdc8496c857442bee0758726b49ed69`,
containing repair head `46e5a7738c6c131eda4cde89d019a7b86d5729db` and main
`2c5fff35d8356850529b79b0ba6ab06e2432a55e`. Routing selected `test` for its ten
changed paths. The actual `just test-full` phase exited 0 in 1,867.414 seconds.
The API-reference step also passed.

The 15 Nix suite reports contain 1,435 tests with no failures, errors or skips.
Twelve suites ran fresh. The corpora, documentation and parser-library suites
reused matching Nix results. Fresh acceptance includes:

- Native package replay: three tests in 1.240 seconds. The model check replays
  its native `:shared` facets and rejects any `Built` output.
- Surface S6: 65 tests in 841.359 seconds, including all six formerly failing
  SQL checker/root cases with their no-rebuild assertions.
- Surface: 378 tests in 928.767 seconds, including all six proof-cost report
  cases and the installed SQL-file consumers.

The separate host source report has two expected skips: its optional installed
reviewer-CLI checks, because Codex and Claude are not installed on that runner.
These are outside the 15 Nix suite totals above.

The downloaded [case-report artifact](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40716887931/artifacts/12833170585)
matches GitHub's SHA256
`23be1db9595241cba42ecb512f2ccb6285d913d19d218b7a2dc9141c2619d01c`.
Its parsed summary is `/tmp/pr296-case-reports-summary.json`; the complete job
log is `/tmp/ci296-122916892875.log`. This result establishes the hosted installed
consumer repair. Scope `test` did not run scheduled checks or mutation suites;
hosted resolver/query/join mutant acceptance and the final combined gates remain
pending.

## Hosted final-source test acceptance

PR 297's [Linux check](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40720732197/job/122930600377)
passed at merge `9c3da650eab70f605912e253570c7fd413863a7f`, containing publication
head `9eb179dea63084ce30e69406b5cf462f894c4e33` and base `46e5a773`.
The tested merge has no file differences from the publication head. That head
adds only records to final source `23a3427b`, including its comparison-import
correction. Routing selected `infrastructure` for 319 changed paths. The actual
`just test-full test-nix` phase exited 0 in 1,542.633 seconds; the API-reference
step also passed.

All 15 Nix suite reports passed: 1,440 tests, with no failures, errors or skips.
Twelve suites ran fresh; corpora, documentation and parserLibrary reused matching
Nix results. The model passed 241 tests, surface 380 and surfaceS6 66. The
remaining twelve suites account for 753 tests.

Separate host reports contain 560 source-check passes and two optional reviewer
CLI skips, plus 70 Nix-infrastructure passes and one development-shell skip.
The latter needs `BELAY_PARSER_LIBRARY` and `LEAN_CC`, which the hosted runtime
does not supply. The local final pipeline runs the development-loop check in
the configured shell; hosted evidence does not replace that requirement.

The downloaded [case-report artifact](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40720732197/artifacts/12832988203)
matches GitHub's SHA256
`4d9223cc6e8b0d8c240028253f2fe9880cd79c4d50fc59130064f1b8c3c96bdb`.
The parsed evidence is `/tmp/pr297-case-reports-summary.json`; the complete log
is `/tmp/pr297-122930600377.log`. Scheduled writers and actual hosted mutant
execution remain outside this result. The mutation steps were skipped.

The first local final-source aggregate test invocation reached its unchanged
2,700-second deadline during surfaceS6, with no individual test failure.
Its completed Nix suite outputs remain valid. A serial retry uses the same
source, configuration and limits, reusing those outputs; no timeout is counted
as a pass. The remaining final gates continue after that retry.

The coordinator also removed the completed CI-repair, fixture-retirement and
comparison-correction workspaces. Each had an empty working copy, all commits
were ancestors of published `tasks/proof-refactor@origin`, and no live process
used the directory. The acceptance worker confirmed that its inputs and caches
do not depend on those paths. This brings completed worker cleanup to twelve
workspaces. The coordinator and active acceptance workspaces remain, as do the
owner's other workspaces. The audit is
`/tmp/adr25-26-remaining-workspace-cleanup-audit.json`.

## Final-source tests, conformance and dependency inspection

The unchanged local full-test retry exited 0 in 752.403 seconds. Its aggregate
Nix output is
`/nix/store/6wkw19ik1ldb4zh09g7glinyl1pdksfw-sqlite-verifier-test-reports`:
15 suites, 1,440 tests, no failures, errors or skips. The final source checks
also passed all 562 cases without skips. The retry reused completed derivations;
the surfaceS6 suite ran fresh and passed all 66 cases in 628.517 seconds.

Final-source `just verdict` exited 0 in 97.982 seconds. Across 56 corpora it
reported 5,653 agreements and 2,109 explicitly unsupported cases, with no other
outcomes. Its immutable result is
`/nix/store/mq2zhrhhdmbr27fnnxjnd64nkx8iywmj-sqlite-verifier-verdict`.

The matched theorem-dependency report completed in 16.232 seconds at
`/nix/store/vi1d8p2dwnyg6fjb6gm6isjan4s7sygz-sqlite-verifier-theorem-dependencies`.
Inspection checked all 1,169 selected and loaded modules, the final-source
hashes, manifest and compiled-artifact hashes, and the 13 Plausible source/artifact
pairs in their separate immutable dependency output. All 155 targeted replaced
names are absent: 84 ADR25 endpoints, 45 query endpoints, 14 origin helpers,
three resolver dispatch proofs and nine relation wrappers. All 64 inspected
body-reference routes reach the intended shared facts; the four prohibited
reverse routes and specified executable/lower-owner imports are absent.

The compiled project import closures, including each root, contain 77 modules
for Values, 154 for Script, 159 for ValueDisplay, 290 for Classify and 240 for
Resolve. These are dependency observations, not proof-strength or speed claims.
The accepted formula witnesses at `53a346e` supply the separate migration
evidence. The one-time inspection result is
`/tmp/adr25-26-final-dependency-inspection.json`; no permanent graph gate was added.

Configured development-loop checks, scheduled writers, local API reference,
affected resolver/comparison mutations and the scoped proof-cost sample remain
in the serial acceptance pipeline. Hosted mutation execution still requires
the pending full workflow dispatch. Task completion records remain pending.

## Final development-loop and scheduled-writer checks

`just test-nix` exited 0 in 94.726 seconds in the configured development shell.
All 71 cases passed without failures, errors or skips. The development-loop
case took 30.529 seconds. It used independent writable copies of the exact
current Nix package caches, with no shared inodes or symlinks to those caches;
the source outputs remained immutable. The provenance is
`build/final-23a/cache-setup.json` in the acceptance workspace. All 7,337 tracked
source hashes remained unchanged. The result closes the development-shell
coverage gap in the hosted infrastructure run.

`just test-scheduled-checks` exited 0 in 455.663 seconds. All 50 corpus-writer
checks passed without failures, errors or skips. The immutable suite report is
`/nix/store/r444x3c1521gin6g1bqmrx2if8rlfnwy-sqlite-verifier-test-writers-1/junit.xml`;
the aggregate is
`/nix/store/b1970pfwpg9ks801732i7x6wrbixxjb4-sqlite-verifier-scheduled-check-reports`.
Its JUnit suite time is 453.324 seconds. These are writer checks, not mutation
measurements. Local API-reference generation, affected resolver/comparison
mutations and the proof-cost sample are the remaining local gates.

## Final affected mutations and API-reference acceptance

The existing resolver owner passed all six measurements covering all eleven
resolver/control mutants. Each mutant compiled and changed an authored verdict;
no compilation failure or timeout counted as detection. The unchanged
300-second test deadline and all original mutant/target mappings were retained.
The Nix invocation exited 0 in 511.442 seconds, with no failures, errors or skips.
Its report is
`/nix/store/ph0mnmjkvijlfwijmyk0vbllmmbnfi1j-sqlite-verifier-test-mutants-ci-repair-1/junit.xml`.

| Resolver group | Seconds |
| --- | ---: |
| Identifier | 112.903 |
| AddColumn | 90.558 |
| Definitions | 86.520 |
| ResolveStatement | 62.799 |
| TypeAffinity | 91.779 |
| SqlAdvance | 64.229 |

The existing comparison measurement passed all three mutants after the
comparison-law import correction. Its one JUnit case took 132.360 seconds;
the Nix invocation exited 0 in 134.852 seconds, with no failures, errors or skips.
The report is
`/nix/store/zv8w1pxdwyc5l7ciwnd2l0d0pqvgsdv5-sqlite-verifier-test-mutants-comparison-boundary-1/junit.xml`.
These local Nix measurements do not establish hosted timing headroom.

API-reference acceptance uses the verified hosted PR 297 build recorded above.
Its actual command ran `just reference` through the existing Nix target and
produced
`/nix/store/f6sy1s39hx680v9dhm88569ppbnmvhlg-sqlite-verifier-api-reference-9c3da650eab7`.
The hosted and local runs use the identical documentation-base derivation
`/nix/store/9nvhc7iackzzzibgk1iy9pl78qqhgv7l-sqlite-verifier-api-reference-base-2.drv`.
The tested merge has the same files as publication head `9eb179de`, whose code
matches frozen source `23a3427b`. Only the final source-link revision stamp
differs from the redundant local rendering.

The coordinator cancelled that duplicate local rendering with a targeted
SIGINT after confirming the hosted evidence. The local command exited 1 after
415.177 seconds and is recorded as cancelled, not passed. The required checked
API result is the successful hosted Nix build. No required mutation check,
deadline or source scope was changed. The scoped proof-cost sample is the last
local acceptance item still running.

## Final proof costs, source integrity and capability audit

The one-time Nix proof-cost sample exited 0 in 52.907 seconds. It covers nine
owner modules and 50 definition-body profiler nodes, using pinned Lean 4.34.1,
one thread, warmups and repeated control/profile measurements. Its sources,
artifact/compiler hashes, raw logs and measurements are retained at
`/nix/store/8mzc56z463p8pzcf95ccbzxij6c14a9k-sqlite-verifier-adr26-final-proof-cost-sample`.
This is a current-state body-elaboration sample, not exhaustive proof coverage
or a before/after speed comparison. Two repeated body measurements differed by
two or four internal heartbeats; raw samples retain that variation.

The final Nix producer log records build phases of 233 seconds for the model,
31 seconds for text, 64 seconds for the surface and 63 seconds for checked
public documentation. These phases rebuilt changed outputs with cached
prerequisites; they are not clean-build times or evidence of a speedup.

All 7,337 tracked files in the acceptance workspace still match the frozen
source manifest. The final fixed-baseline capability audit retains S01–S17
and M01–M13: 30/30 groups, none unknown or lost. Essential groups S01–S04 and
S06 remain intact. This combines unchanged executable definitions, the
accepted original-formula witnesses, final source and compiled-reference
inspection, and each group's existing Nix acceptance owners. Test counts alone
do not establish retention. No capability loss was requested or approved.

Before workspace cleanup, the coordinator copied the final summaries, source
manifest and host XML reports to `build/final-23a` in the coordinator workspace.
Thirteen existing Nix outputs, including the dependency report, source counts
and pre-retirement contract results, have indirect roots under that directory.
The final summary is `build/final-23a/acceptance-summary.json`; the host source
and development-loop XML reports are under `build/final-23a/host-results`.
Retaining this evidence built no new derivations and changed no tracked source.

All local acceptance work is terminal. The completion records from `54580b0b`
are integrated without conflicts with the final acceptance evidence. Their
single task/goal decision is `0cd4cbf5`; three independent Claude reviews have
zero must and zero should findings. The bounded supplemental reviews checked
the governing ADR/task completion requirements and cited Nix artifacts.
No executable source, proof, test or acceptance configuration changed during
this closing integration. The remaining acceptance item is the externally
blocked hosted mutation run.

The independent review of integration `a8636c41` also has zero must and zero
should findings (`20261028T174514Z-a8636c41`). The closing changes consist only
of task, status, goal-ledger and review records; final code remains `23a3427b`.

## Full hosted follow-up, 2026-10-28

Manual run `40742662857` tested `bbd2eeacf082f1f9ed820e3096499d8fb44cd63f`.
The previous dispatch blocker is superseded by this actual run. Linux check
`123008079942` and table-mutant job `123008080011` pass. General-mutant job
`123008080055` finishes 21 of 63 tests, including all six resolver groups,
comparison and query resolution, before its Nix builder exits 124 at the
2,700-second suite limit. It produces no successful suite/JUnit artifact.

macOS check `123008079877` reports one failed model case out of 241:
`test_oversized_hex_default_prepare_error[False-3.46.0]` exceeds its 15-second
Lean subprocess deadline. The neighboring sign/version cases pass. Table
job `123008079969` times out the combined write measurement at 300 seconds;
general-mutant job `123008080251` times out arithmetic at 300 seconds.
These reports show timeouts, not a surviving mutant or proof/import failure.

The coordinator retained the Linux general-mutant log under
`build/final-23a/logs/hosted-40742662857-mutants-linux.log`. The repair is split
between mutant scheduling/grouping and the independent default-fixture import
boundary. Neither work surface may change production semantics or deadlines.

Independent review of follow-up specification `af674848` has zero must and
one should finding: an import requirement prescribed implementation order.
The requirement now states the resulting dependency boundary instead.
The corrected specification at `bcad4b11` passed independent review with zero
must and zero should findings.

The successful Linux table suite has 13 cases, no failures, errors or skips,
and takes 2,118.007 seconds. Its four join measurements take 162.928 seconds
(joins), 190.770 (USING), 123.980 (right joins) and 206.199 (merged columns).
All 22 mutant identities and 20 target cases are unchanged from the accepted
repair. Artifact `12843142974` has SHA256
`95b86120c43f8dbe3d7215c50f5d5f3d4d8fa3cd148791fba354b234a187ea4d`.
Query resolution logs PASS approximately 104.378 seconds after the previous
case finishes; this is a timestamp interval, not an individual JUnit timing.

The Linux main check actually runs `just test-full test-nix test-scheduled-checks`
and exits zero in 1,772.995 seconds. Its 15 full Nix suites pass all 1,440 cases;
scheduled writers pass all 50. Host reports retain only the two optional
reviewer-CLI skips and one development-shell skip already covered by configured
local acceptance. Artifact `12842678651` has SHA256
`74186f840e445fcda76be361cf2eb587a4a61d32a2b497a60a2b8a1a4b22b5b6`.

The coordinator retained the verified ZIP/XML, exact mutant/target membership,
source comparisons, summaries and three macOS job logs under `build/final-23a`.
`audit/hosted-40742662857-retained-evidence.json` records the copied file hashes.
The default-fixture and mutant-workload workers were assigned the reviewed
follow-up in separate workspaces; both slices are recorded below. Only one
worker ran focused Nix acceptance at a time. The user confirmed that the exited
herdr review remains unfinished.

## Oversized-hex default fixture import boundary

The assigned default-fixture slice changes only the generated Lean source in
`test_oversized_hex_default_prepare_error`: it imports `Lean` for its JSON list
of strings, instead of the model's `Codec` module. The explicit default,
INSERT-cell and error-message imports remain. All four SQLite-version/sign
cases still compare the native prepare phase and exact message. The neighboring
value-serialization fixture still imports `Codec`. The shared 15-second
compiler deadline and forbidden-axiom checks are unchanged.

Focused Nix acceptance uses the existing `model` owner, selecting the complete
`tests/column_default_value_test.py` file through an ignored
`build/default-fixture/selected.nix` expression. The override changes only the
pytest file selection and diagnostic derivation name. Runtime, source inputs,
environment, 300-second test limit and 1,200-second suite limit are unchanged.
The invocation uses `max-jobs = 1`, `cores = 3` and a 2,700-second outer limit:
`nix-build build/default-fixture/selected.nix --out-link build/default-fixture/result
--option sandbox true --option sandbox-fallback false
--extra-experimental-features 'nix-command flakes'`.

The Nix invocation exited 0 in 10.846 seconds and built only the selected test
output, reusing existing package/runtime outputs. All six cases passed without
failures, errors or skips in 8.576 seconds. The four oversized-hex cases took
0.872, 0.850, 0.860 and 0.913 seconds in version/sign collection order; the two
neighboring value cases took 2.729 and 2.273 seconds. The immutable report is
`/nix/store/vw59wlyk072bcdghrcw95y0vasvjqwd9-sqlite-verifier-test-model-default-fixture-1/junit.xml`.
The invocation log is `/tmp/proof-refactor-default-fixture-nix.log`.
These Linux measurements do not establish hosted macOS headroom. Independent
review is recorded below; the overall CI task remains IN PROGRESS until its hosted
gates pass.

Independent Claude review `20261028T201736Z-745e944e` of implementation
`745e944e8b2af517c79b98ae341fe364a74f8d3f` completed with zero must and zero
should findings. The fixture change is ready for integration. Hosted acceptance
of the full model suite on both platforms remains pending.

## Hosted mutant workload partition, 2026-10-28

The follow-up retains the existing mutant edits, guards, target mappings, native
records and base-model agreement. Arithmetic is now two three-mutant
measurements, selected by its existing real-arithmetic guards. Writes use the
three existing tables as separate measurements: write (five), row-write
(seven) and DELETE (five). The existing `measure_set` executable body is unchanged.

The former general owner is now seven static owners. `mutants` retains resolver,
core query/key/conflict and rebuild tests. `valueMutants` owns the extracted
number/FROMless/JSON/date tests. Query features, query sources, INSERT queries,
rename and column drop each use their existing file in a separate owner.
The table and function owners remain. The existing Nix inventory generates
the shared suite definition, and the CI matrix names all nine mutant owners.
The existing ownership check verifies that every mutant test file belongs to
exactly one scheduled mutant owner. Nix command evaluation verifies all nine
file lists and unchanged 2,700/300-second limits. An inventory-only change
now selects the infrastructure checks.

The partition bounds work without changing the 300-second test, 2,700-second
suite, subprocess or 75-minute job deadlines. Hosted run `40742662857` measured
macOS resolver and core comparison/evaluation/resolution work at about
1,216 seconds. The remaining tail was not measured there. The query-feature
and other extracted owners therefore remain candidates for hosted validation;
test counts alone do not establish timing headroom.

Focused arithmetic Nix acceptance passed both groups: integer-and-CAST in
123.720 seconds and real arithmetic in 125.208 seconds, with no failure,
error or skip. The selected run took 249.106 seconds. Its immutable report is
`/nix/store/4ldcn9xzfbljwq2myyl3v7mkmp5g7a8w-sqlite-verifier-test-hosted-arithmetic-groups-1/junit.xml`.
The captured source differs from the final tree only in the helper's module
docstring; its executable AST and all other captured source files match.
Focused write Nix acceptance passed all three groups: write in 81.556 seconds,
row-write in 125.465 seconds and DELETE in 74.895 seconds, with no failure,
error or skip. The selected run took 282.154 seconds. Its immutable report is
`/nix/store/a5zzn7bs3l61hrc2plhj6mw2n675ibhw-sqlite-verifier-test-hosted-write-groups-1/junit.xml`.
Its captured source matches the final inputs. Both focused runs selected the
existing test by name through its actual owner, with normal dependencies,
`--max-jobs 1 --cores 3` and all existing limits. These are local Nix timings;
new hosted Linux/macOS results remain required.

The changed static checks are `test_test_ownership`, `test_ci_scope`,
`test_ci_workflow`, `test_recipe_limits` and the bounded-command check in
`test_nix_test_targets`; doc links and the existing affected mutant-guard
checks also apply. The full combined acceptance runs once through the
coordinator. The CI task remains IN PROGRESS until all scheduled mutant
suites and the model suite succeed on both hosted platforms.

The source partition audit of `3ba90a61` against `db1c11b1` confirms all six
arithmetic mutants retain the same five target definitions, and all 17 write
mutants retain the same 16 target definitions. Edit tuples, targets, guards,
authored-module unions and native-recorder sources are unchanged; the groups
have no duplicate or missing mutant. Fourteen moved/retained query functions
have identical executable ASTs. Only the arithmetic grouping changes there.
The five focused Nix measurements above supply the execution evidence.

Independent Claude review of `3ba90a61` has zero must and zero should findings
(`20261028T203525Z-3ba90a61`). Combined coordinator acceptance and subsequent
hosted validation remain pending; this task stays IN PROGRESS.

## Combined follow-up review, 2026-10-28

The coordinator integrated both reviewed slices at `cfcde78c`. The only merge
conflict was in appended status records; both records were retained. All
production files under `packages/` remain identical to the accepted ADR25/26
source `23a3427b`. Independent Claude review `20261028T203808Z-cfcde78c` has
zero must and one should finding: the assignment paragraph used present tense
after both workers had finished. The paragraph now uses past tense.

This status and review record freezes the combined source for one acceptance
run in the existing default-import workspace. That run will use independent
writable copies of the four immutable package caches recorded in
`build/final-23a/cache-setup.json`, with one Nix worker slot. The required checks
are `just test-full`, `just verdict`, `just test-nix` and
`just test-scheduled-checks`. Their results and hosted validation remain pending.

## Combined follow-up acceptance, 2026-10-28

All four assigned gates passed once at frozen source
`d61d7990fa29a60b1625eea9d24087acf0516d70` in the reused default-import workspace.
Each command ran through `direnv exec .` with `max-jobs = 1`, `cores = 3` and
`LEAN_NUM_THREADS=2`. All existing recipe, suite and test limits remained in
force. The run used independent writable copies of the four accepted immutable
package caches; each copy had no symlinks or shared inodes with its source.

`just test-full` exited zero on its first invocation in 2,105.477 seconds.
All 15 Nix suites passed 1,440 cases, with no failures, errors or skips.
The configured source checks passed 563 cases in 118.098 seconds, with no skips.
The combined report is
`/nix/store/s8p03pilyrr2f14lc56klb7z6n5fpi40-sqlite-verifier-test-reports`.
Four suites ran again: model (241 cases, 353.675 seconds), surface (380,
666.238), surfaceChecks (22, 338.691) and surfaceS6 (66, 619.910). The other
eleven suites reused matching immutable results. The surface report inputs
include the build-support definitions; their captured sources differ only in
`build-support/tests.nix`. Package producers and checked documentation reused
their accepted outputs.

`just verdict` exited zero in 1.400 seconds and reused
`/nix/store/mq2zhrhhdmbr27fnnxjnd64nkx8iywmj-sqlite-verifier-verdict`.
Its 56 corpora retain 5,653 agreements and 2,109 explicitly unsupported cases,
with no other outcomes. `just test-nix` exited zero in 95.247 seconds: all 71
cases passed without failures, errors or skips. The development-loop check ran
normally in 30.010 seconds. The checks include rendered Nix commands, source
identities, test ownership and infrastructure routing.

`just test-scheduled-checks` exited zero in 1.267 seconds and reused
`/nix/store/b1970pfwpg9ks801732i7x6wrbixxjb4-sqlite-verifier-scheduled-check-reports`.
Its writers report retains all 50 passing cases, with no failures, errors or
skips. No whole mutant suite, API reference or dependency report was rebuilt
for this local acceptance.

All 7,352 tracked files retained their original hashes throughout the run.
The source manifest SHA256 is
`900757ee2755eb73fbaa3edf80351c46a5abaa58b5031cdc5a2f1b50a3fd0f4f`.
The coordinator retained 23 verified evidence files under `build/final-d61d`,
including `acceptance-summary.json`, exact commands and terminal results,
logs, both host XML reports and cache/source provenance. Five indirect Nix
roots retain the named outputs. No new implementation change followed the
frozen acceptance source.

The CI task remains IN PROGRESS. Fresh hosted checks must execute and pass all
nine scheduled mutant owners and the model suite on both Linux and macOS.
The owner's earlier herdr review remains unfinished.

## Value workload exposed by the next hosted run, 2026-10-28

Run `40771508608` tests publication head `c9fa3f73` through merge
`72df4baee5e635a47ba29711d909f9c885ef15bf`. Its value-mutant job `123109628916`
passes four cases, then the eight-mutant JSON reading/extraction case reaches
the unchanged 300-second test limit. Its log reports 304.45 seconds including
unwind and 1,138.48 seconds for the failed suite. Worker traces show classifier
builds and execution still active. No named mutant compilation error or
surviving-mutant result is reported. The remaining three cases do not execute
because the existing command stops after its first failure.

Both arithmetic groups pass (209.35 and 215.16 seconds). The other-number group
passes in 278.68 seconds, leaving 21.32 seconds of test headroom. This is new
hosted evidence for the same finite-workload repair. The existing task now
covers bounded JSON/other-number measurements and separates numeric/FROMless
from JSON/date/clock ownership. Exact edits, target mappings, guards, native
observations and all existing deadlines remain required. The three unexecuted
tail measurements need focused evidence before the follow-up is accepted.

Read-only designs identify existing semantic boundaries: the three summation
mutants versus four scalar/text/coalesce mutants, and four JSON value/rendering
mutants versus four lookup/error mutants. The unexecuted JSON-function table
has six mutants; JSON-each/clock and date/modifier each contain ten across their
existing tables. These designs do not establish timing headroom. An isolated
worker will implement the reviewed follow-up through the current harness.

The current Linux API reference and hosted verdict have passed. Eight mutant
owners pass fresh execution, including all twelve core measurements in 1,949.09
seconds. The value owner is the only failed mutant job. Main checks remain
active. Their final evidence will be retained before another push. Manual
dispatch for `c9fa3f73` returned HTTP 403; the next manual run must use the next
repaired publication head. The owner review remains unfinished and this task
remains IN PROGRESS.

## Independent review blocked by credentials, 2026-10-28

The value-workload specification is committed as `3933edbd`. Its required
independent Claude review fails twice with HTTP 401: the OAuth access token
has expired. The review records `20261028T220604Z-3933edbd` and
`20261028T220709Z-3933edbd` contain no valid review result. The second attempt
follows the repository's one-retry rule for reviewer failures.

The owner has been asked to restore Claude Code authentication or authorize
another independent reviewer for this repair. No implementation workspace or
build has started for the value follow-up. Existing hosted main checks can
continue independently; all nine mutant jobs are terminal and their logs,
artifact identities and hashes are retained under
`build/final-d61d/hosted-mutants-40771508608/`.

## Review access restored, 2026-10-29

At the owner's request, the previously blocked review of `3933edbd` was retried.
Claude authenticated and completed the review successfully, with zero must or
should findings. Record: `20261029T071121Z-3933edbd`. The reviewer checked the
plan against the current test file; hosted timing evidence remains in the
retained CI logs. The authentication blocker is cleared. Value-workload
implementation has not started.

The previous main Linux job `123109629015` also completed successfully. Its
verified reports contain 1,440 passing Nix tests across fifteen suites, with
1,340 fresh executions and 100 cached results, and no failures or skips. The
model's four oversized-hex cases all pass. The source checks have two
missing-CLI skips, and the hosted infrastructure checks skip the development
loop because its shell configuration is incomplete; the earlier local full
acceptance includes that check. Checked API documentation and all fifty
scheduled writer tests pass. Full logs, artifact metadata, verified ZIP files
and parsed totals are retained in
`build/final-d61d/hosted-checks-40771508608/`.

The workflow still fails on the value-mutant timeout. macOS remains untested
by this PR run, and the owner review remains unfinished. The CI task remains
IN PROGRESS.

## Value measurements and separate ownership, 2026-10-29

The seven other-number mutants are split into summation (three), text parsing
(two), and coalesce (two). The eight JSON reading/extraction mutants are
split into values/rendering (four) and lookup/errors (four), using their
existing source/guard metadata. Exact mutations, guards, target dictionaries
and authored-case suppliers remain unchanged. Numeric/FROMless measurements
stay in `valueMutants`; `tests/conformance_json_date_mutants_test.py`
belongs to `jsonDateMutants`. The inventories and CI matrix now name ten mutant
owners. No build-support, production, conformance or shared-helper code changes.

The three original tail measurements passed focused Nix in 166.404 seconds
(JSON functions), 151.477 seconds (JSON-each/clock) and 224.013 seconds
(date functions/modifiers), with a total of 542.074 seconds. The diagnostic
report is `/nix/store/xgs7a6yw42iamq3y5rnvwmbk8h9v4bvy-sqlite-verifier-test-value-followup-tail-1/junit.xml`.
These costs leave limited margin given the slower hosted arithmetic samples.
That comparison is calibration, not a hosted acceptance result. The final
partitions use existing boundaries: JSON Functions/Valid (three each),
JSON-each/clock (six/four), and date functions/modifiers (five each).

The refreshed one-time audit retains all 41 mutants across the five changed
families, their exact target/guard maps and selected authored definitions,
without duplicate or missing entries. Arithmetic, FROMless and the number-table
helper retain identical executable bodies and inputs. Their whole-file
Nix source identity changes with the extraction; earlier arithmetic/FROMless
results are unchanged-body evidence, not cache hits for this new source.
The final owners have six numeric and eight JSON/date/clock measurements.
The sums of their individual 300-second budgets are 1,800 and 2,400 seconds,
respectively, within the existing 2,700-second suite limit.

The first number partition passed in 105.23 seconds for summation and 157.90
seconds for scalar/text. Its report is
`/nix/store/q2a0s23mn6w1l8j0q7z7av18n8vwvzab-sqlite-verifier-test-value-followup-numbers-1/junit.xml`.
The scalar/text cost motivated its final two-way split. This is diagnostic
evidence from the preceding test-file source; all three final parameters
were measured again against the final selector and file.

Final focused Nix results cover all eleven resulting measurements and all
41 affected mutants. Each report has zero failures, errors or skips:

- Other numbers (3/2/2 mutants): 106.812, 144.332, 115.772 seconds; suite 367.095 seconds.
  Report: `/nix/store/d48ynbgyf4j072js7a2b122vb3ss2563-sqlite-verifier-test-value-followup-numbers-1/junit.xml`.
- JSON reading (4/4): 138.650, 132.455 seconds; suite 271.286 seconds.
  Report: `/nix/store/w16wjjhha092y80qscliqhkcnmch11n1-sqlite-verifier-test-value-followup-json-1/junit.xml`.
- JSON functions/validation (3/3): 128.830, 126.586 seconds; suite 255.609 seconds.
  Report: `/nix/store/6wli4f01hwhkyxgymcgwxskqbzvjsl62-sqlite-verifier-test-value-followup-functions-1/junit.xml`.
- JSON-each/clock (6/4): 125.193, 124.010 seconds; suite 249.392 seconds.
  Report: `/nix/store/716c4irhpqg1hpv54sr21qh4n5wlijn1-sqlite-verifier-test-value-followup-each-clock-1/junit.xml`.
- Date functions/modifiers (5/5): 145.756, 146.114 seconds; suite 292.036 seconds.
  Report: `/nix/store/9yn2kkha02gh6lzzx24yyy5bcy2lsnc3-sqlite-verifier-test-value-followup-dates-1/junit.xml`.

The final number source is
`/nix/store/xgqgxwg0anh79dxyfl8zwf3yh1i7yjn8-source`;
the shared JSON/date/clock source is
`/nix/store/iigyqn8g9giz0d9x3l3w27dg12wcski2-source`.
Every file in these filtered source snapshots matches the final workspace.
The temporary working files `/tmp/value-followup-acceptance.json` and
`/tmp/value-followup-partition-audit.json` are not durable records. The
partition results and immutable Nix report paths are summarized above.

The temporary selectors derive from the
existing scheduled owners and run with `--max-jobs 1 --cores 3` and
`LEAN_NUM_THREADS=2`. They keep native/runtime dependencies, harness and
all existing test, compiler, suite and subprocess limits. The resource cap
is an explicit difference from normal hosted execution; these results do
not claim exact CI-owner cache reuse or establish hosted timing headroom.

The attempted workspace-local `build-dir` override was rejected by the Nix
daemon as a restricted setting. The first run used default temporary storage;
subsequent commands omit the ignored option. The normal resource guards passed
at run boundaries, and all focused runs completed using default temporary storage.
No global configuration, permissions or unrelated temporary files changed.

The affected existing checks are `test_test_ownership.py`,
`test_ci_workflow.py`, `test_nix_test_targets.py`, `test_test_reports.py` and
`docs_test.py`. They cover ownership, the matrix, bounded Nix commands,
two-platform flake targets, report links and documentation. No permanent
partition gate or new measurement framework was added. The coordinator
runs combined acceptance after integration. All hosted mutant owners and the
model suite must still pass on both platforms; this CI task stays IN PROGRESS.

Independent Claude review of `4ee25f4f` found zero must and two should
findings (`20261029T075742Z-4ee25f4f`). Both are fixed: the owner count now
explicitly describes the changed state, and the scratch evidence paths are
identified as temporary. The substantive audit summary and immutable report
paths remain in this status. Production code and measured inputs are unchanged.

## Combined value-repair acceptance, 2026-10-29

All four acceptance commands ran once and passed at frozen source
`b621785b28577f71e3fc88c1147654be7380db41`, with the existing limits.
`just test-full` completed in 125.392 seconds and reused all fifteen exact Nix
suite outputs in
`/nix/store/s8p03pilyrr2f14lc56klb7z6n5fpi40-sqlite-verifier-test-reports`:
1,440 passing cases, with no failures, errors or skips. The accompanying host
source checks reran and produced 563 passing JUnit cases. These host results
are supplementary checks, not additional Nix acceptance cases.

`just verdict` completed in 1.388 seconds and reused the accepted verdict
output named above: 56 corpora, 5,653 agreements and 2,109 explicitly
unsupported cases, with no other outcomes. `just test-nix` completed in
94.195 seconds: all 71 infrastructure cases passed, including the development
loop in 29.686 seconds, with no failures, errors or skips.
`just test-scheduled-checks` completed in 1.271 seconds and reused the accepted
scheduled-check output named above, with all fifty writer cases passing.

The source retained all 7,359 tracked hashes. The source-manifest SHA256 is
`ffeea8585b94a3ba9afc30d0a7f9dc5e32e94d65fe65bac1b9efa7473d8ca495`.
Package, toolchain and Nix sources remain identical to the accepted proof
refactor for the reused outputs. Development-loop caches are independent
writable copies of immutable package outputs. No package producer, API
reference, dependency report or whole mutant suite was rebuilt.

The coordinator retained and hash-verified 21 evidence files under
`build/final-b621/`, including exact commands and terminal results, logs,
host XML, cache provenance and before/after source manifests. Five indirect
Nix roots retain the named outputs. The focused mutant evidence is retained
separately under `build/value-followup-20261029/`: twenty verified files and
seven rooted Nix outputs, including the superseded diagnostic measurements.
The eleven final focused measurements retain the explicit two-thread resource
difference from hosted execution documented above.

The reviewed repair is ready for publication. This task remains IN PROGRESS
until all ten scheduled mutant owners and the model suite execute and pass
on both Linux and macOS at the repaired publication head. PR runs skip actual
macOS execution, so a successful manual or scheduled run is still required.
Both stacked PRs remain drafts, and the owner's herdr review remains unfinished.
