# SELECT automation specification checkpoint

Created 2026-10-28. Status: DONE (2026-11-07): the owner accepted ADR 27 and asked for its
implementation.
Audience: team. Task: [required outcome](20261028-select-automation-spec.task.md).
The owner explicitly requested number ADR 27 for this work. The
[ADR](../docs/adr-0027-compositional-select-proofs.md) and the
[acceptance contract](../docs/select-automation-acceptance.md) are accepted (owner,
2026-11-07); gaps in earlier ADR numbers do not change that request.

## Current state

- Baseline: main `187ea510` (PR 297, ADR 0025 and ADR 0026), Lean 4.34.1.
  The experiments and Nix reports below were made on the earlier main
  `3e2212ed`; see "Integration of main after PR 297".
- Source inspection found existing SQL weakest preconditions, `mvcgen`
  integration, `sql_run`, `sql_auto`, and expression simplification. The SELECT
  rule leaves model-coverage and universal selected-output obligations.
- Earlier consumer probes are exploratory only. They are not Nix acceptance
  evidence for this task. The consumer NOT NULL theorem uses a general table
  projection rule; broader execution adapters remain absent there.
- The disk-space gate blocked work at 8.37 GiB free. A fresh resource check now
  passes. No cleanup was performed by this task.
- Development shell initialization passed: Lake reports Lean 4.34.1.
- Four retained SELECT experiment tests passed in the complete Nix `surfaceS6`
  suite: 69 tests, no failures, errors or skips, 699.816 seconds.
  Report: `/nix/store/kqiwv5v55hh5g0zg1pr70b4rby9zv8hx-sqlite-verifier-test-surfaceS6-1/junit.xml`.
  These are feasibility checks, not acceptance of the proposed automation.
- Planning commit `1783df21` received independent review with no must findings.
  Its two should findings concern the owner-selected ADR number and the
  owner-local location of earlier consumer probes; both are clarified here.

## Installed checker fix (2026-10-29)

The experiment run exposed six failures in the existing SQL-file checker tests.
Both Nix environments set `MACOSX_DEPLOYMENT_TARGET=14.0`, but
`tests/sql_file_support.py::toolchain_environment` discarded it. Lake then used
`99.0`, invalidated the executable trace and tried to rebuild the checker in
the read-only Nix store.

The owner authorized a small fix with no unnecessary new tests. The helper now
preserves the deployment target when present. No test cases or Nix
configuration were added.

Focused Nix validation passed for all seven caller test modules. A temporary
`PYTEST_ADDOPTS` override selected existing tests, with the declared sources,
runtime, sandbox and timeouts unchanged:

- `surface`: 24 passed, 354 deselected, in `surface_sql_files_test.py`,
  `surface_sql_file_root_test.py`, `surface_sql_records_test.py`,
  `surface_sql_lake_inputs_test.py` and `surface_proof_cost_report_test.py`.
  Report: `/nix/store/k4bhqv5cxr63nl9z8p14cdy7vyvy2dpm-sqlite-verifier-test-surface-1/junit.xml`.
- `surfaceS6`: six passed, 59 deselected, in `surface_sql_check_test.py` and
  `surface_sql_check_roots_test.py`.
  Report: `/nix/store/s5ypavrppr9ch6njrrf74n8aar93rbz4-sqlite-verifier-test-surfaceS6-1/junit.xml`.

Fix status: DONE in commit `8a2b159a`. Independent Claude review
`20261029T074907Z-8a2b159a` returned no findings.

## Work remaining

The owner selected Lean-only specification artifacts after PIDE startup found
no compatible HOL heap. The unchecked Isabelle files were removed; no Isabelle
build or PDF is required. The Lean fixtures and written semantic review cover
are the target-specific formal specification artifacts for this task.

The checked fixtures are integrated from the isolated `select-experiments`
workspace into primary commit `2dab0fe0`. They use the existing surface test
harness and the Nix runtime at
`/nix/store/jh9zgilri7ckdrssni872wjrjsbadx7h-sqlite-verifier-test-surface`.
The Nix suite's declared Python includes pytest-timeout. No dependency was
installed or test timeout removed.

The experiment baseline is the pinned Lean 4.34.1 runtime and unchanged model
source `3e2212ed`. Each module has a 60-second process limit; each test has a
180-second limit. The schema and execution fixtures set recursion depth 8192.
They inherit Lean's finite heartbeat default and disable background SQL checking.
The four successful checks establish:

- `SelectAutomationCore`: universal collection cardinality and WHERE properties,
  with concrete duplicate, empty aggregate and alternative-result boundaries.
- `SelectAutomationSchema`: a universal NOT NULL projection theorem with explicit
  resolution, presence and calmness premises. Empty and populated instances
  discharge every premise. Existing `sql_auto [db.notNull]` fails first.
- `SelectAutomationSources`: nested-source certainty, ordering, NULL extension
  in joins and fault boundaries on concrete evaluator inputs.
- `SelectAutomationExecution`: branch-universal success, the raw output wrapper,
  SQL/preparation errors, continuing context, vacuity and unsupported stops.

The harness checked 23 named axiom reports (7 + 3 + 5 + 8), allowing only
`propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
Nix test times were 1.778, 3.845, 3.515 and 2.298 seconds respectively; these
include harness and elaboration work and are not tactic-cost measurements.

Source review found that a `Run` observation is not equivalent to arbitrary
branch-universal programs, that `.may` faults require readiness checks, and
that three subquery certainty conditions are distinct. The ADR now specifies
these boundaries explicitly. A 22-case automatic acceptance matrix and
constructor-level semantic coverage are proposed, not claimed as implemented.

The source map identifies existing constructors, laws and semantic traps. The
review cover links the checked Lean statements to whole execution and evaluator
views. Review finding 1 was rejected with a clarification that model windows
mean LIMIT/OFFSET, not SQL OVER. Finding 2 was fixed by removing numeric rule
priorities and explaining the shared registry's imported-library purpose.

Integrated revision `2dab0fe0` received independent Claude review
`20261029T080752Z-2dab0fe0` with no findings. The conformance verdict passed:
`/nix/store/ycpq2vi5qagfavihhv7pr4p4m0piq0wj-sqlite-verifier-verdict`, with
5,653 agreements, 2,109 unsupported observations and no other result classes.
The Nix documentation check covered all 6,065 authored declarations:
`/nix/store/qf8fll0jxlnls4v1djqznhg3z6ry2hk4-sqlite-verifier-public-documentation-1`.

`just test-nix` completed its host process checks. This records the required
workflow check, not additional proof or conformance acceptance evidence.
An initial `just test-full` run stopped because the host sandbox denied `ps`
to the existing process-cleanup test. The owner approved the unsandboxed rerun;
its source checks passed. The Nix run then passed feature coverage, locked
corpora and frozen evidence before it was stopped at the resource gate:

- Feature coverage: `/nix/store/0rdmc0nw1v5h7z4mah41wr3vxqzzj8bx-sqlite-verifier-test-coverageFeatures-1/junit.xml`.
- Locked corpora: `/nix/store/ryzyg15qhyybj50frshpz35zc902rwiv-sqlite-verifier-test-corpora-1/junit.xml`.
- Frozen evidence: `/nix/store/897f3fb9n76gj3yim5hsw585lzk4dk7i-sqlite-verifier-test-frozen-1/junit.xml`.

Free space fell below the required 10 GiB. The full-check process was stopped;
after its temporary files were released, 8.22 GiB remained. No failing assertion
caused this stop. Targeted cleanup approval was requested for the packaged runtime,
Rust build cache and four local Lake build directories listed in the owner question.
On the next owner resume, the gate passed with 17.24 GiB free. The requested
cleanup is no longer needed, and this task did not delete those artifacts.
The resumed `just test-full` passed its host source checks and reached the final
`surfaceChecks` suite. It then exceeded the existing 2700-second Nix recipe
deadline (exit 124), with no assertion failure observed. The surface suite had
reported 376 passes and two Linux-only skips. The parser-library suite had one
Linux-only sanitizer skip. The aggregate full-check result remains incomplete.

After temporary files were released, the resource gate passed again. A retry
found that several completed, unrooted Nix outputs had disappeared, including
the surface and corpora reports, so it started rebuilding them. The cause of
their removal is not established; those deleted reports are not retained
acceptance evidence. The protected SELECT experiment report remains available.
The owner asked about faster development-test commands. The retry was stopped
before another complete rebuild; no resource policy or timeout was changed.

The task-created experiment workspace was confirmed empty after integration and
removed. Five diagnostic files were preserved in `build/deployment-target-research`;
`build/select-automation-tests` retains the successful Nix report as a GC root.
No other workspace or cache was removed by this task. Existing `dev-build`
and `dev-verdict` recipes give
incremental local feedback; `test-cases` selects tests on an existing runtime.
Surface fixtures cannot yet use the local checkout directly: they expect a
runtime-local Lean executable and co-located native libraries, while Lake
keeps dependency libraries in their package directories. There is no `dev-test`
recipe. A local adapter must also retain the configured pytest timeout support.

On 2026-10-29 the owner selected focused Nix evidence and deferred the full
suite for this specification-only task. The task's validation requirement now
records that exception; the incomplete full run is not reported as passing.
`just test-scheduled-checks` passed: 50 writer tests, no failures, errors or skips,
36.011 seconds. Report:
`/nix/store/93f486vgr58hk2q5cd7axa1gmrprh5g1-sqlite-verifier-test-writers-1/junit.xml`.
The normal `build/nix-tests-scheduled` root retains that report. No mutant suite
ran. The task-only validation amendment passed the three documentation-link
process checks; these are not additional Nix proof evidence.
Amendment `88749d42` received independent Claude review
`20261029T100954Z-88749d42` with no findings.
Remaining: owner review of the complete cover. No production automation is
implemented here. No full or scheduled check is running.

## Retirement instructions (2026-10-29)

The owner found that the specification was purely additive: it named what to
reuse but not what to remove. The owner decided on 2026-10-29: keep `Holds`,
`Empty` and `Fails` as abbreviations over the D2 predicates; retire the ADR 0026
D1 characterizations; retire the per-family resolution-shape laws where the ADR
0026 D3 certificate replaces them; stage automatic closure with a core set.
Review `20261029T112539Z-23586cde` found two must findings: the general
source-output equation was both required and retained, and the D3 certificate
assumes resolution, so it cannot replace a resolution-shape law. Both fixed:
the equation is retained with `QueryOutputFacts`, and resolution-shape laws are
retained unless every consumer is retired. This reverses the third owner
decision on technical grounds.

Applied: ADR 0027 gains "Scope and supersession", the D2 claim-vocabulary
paragraph, the D3 staging paragraph and a completion rule that includes an
empty required column of the new
[retirement inventory](../docs/select-automation-retirement.md). The acceptance
contract makes retirement per family and applies the ADR 0025 D4 test lifetime
to migration witnesses. The task file records the owner decisions. Checks:
`tests/docs_test.py` and `just review`. No Lean source changes.

## GitHub review

The owner moved the remaining review to [PR 299](https://github.com/vihren-dev/belay/pull/299).
Merge `cdd3e645` integrates main `2c5fff35`, preserving the SELECT experiment
registration and main's `theoremDependencies` suite. It passed 11 focused
ownership, documentation-link and Lean-category process checks and independent
review `20261029T122617Z-cdd3e645` with no findings.
The owner's remote updates through `d702bea8` are retained, including the
claim abbreviations, staged automatic closure and retirement inventory.
The ADR's link to ADR 0026 now resolves locally after the main merge.
The Nix reports above describe pre-merge revisions; current-head CI supplies
integration validation. The full local suite remains deferred.
The combined remote-update merge passed all three documentation-link checks.
Review `20261029T123759Z-df2246bb` found no must findings and two wording
findings. Both are corrected: the ADR and inventory distinguish PR 297's
not-yet-integrated output-fact owners from this branch's current definitions.
The retirement requirements and the owner's staging decisions are unchanged.
Correction `a5d0b0b1` passed documentation-link checks and independent review
`20261029T124036Z-a5d0b0b1` with no findings.

## Integration of main after PR 297 (2026-10-29)

PR 297 merged ADR 0025 and ADR 0026 into main `187ea510`. The branch already
carried owner merge commits, so a rebase onto main produced conflicts in ten
commits; the operation was restored and main was integrated by a merge commit
instead. The merge had no conflicts.

Specification reconciliation in the same merge commit:

- ADR 0027: the intro and the supersession section name the D1 owners as they
  exist on main (`resolvedStepOutput_selectOne`, the per-family output files,
  the surface `Script.outputOn_<form>` equations); `QueryOutputFacts` stays as
  the D5 execution bridge. The interim "not in this branch" wording is removed.
- Retirement inventory: `FilteredDuplicateKeyEmpty.lean` (deleted by PR 297)
  is dropped; `SelectOneOutput` and `QueryOutputFacts` are named with their
  current content; line counts are from `187ea510`; the measurement section
  links the Lean simplification goal, which main now has.
- Source map: the execution row points to `QueryOutputFacts.lean` and
  `SelectOneOutput.lean` instead of `QueryStatementOutput.lean`.
- Task file: baseline updated.

Experiments: every identifier that the four `tests/surface/SelectAutomation*`
fixtures use was checked to exist on main `187ea510` (for example
`Query.simple_isSimple`, `Query.Simple.results_eq`,
`resolvedStepOutput_simpleTable_rows`, `Script.outputOn_query`,
`Script.query_outputs`, `Sql.check_stopped`). The fixtures were not changed.
After the owner freed disk space (the 10 GiB gate had refused the shell at
9.94 GiB free), `just dev-build` passed as a diagnostic, and a sandboxed
`nix-build` of `tests.surfaceS6` with `PYTEST_ADDOPTS="-k select_"` ran the
four fixtures on the merged source: 4 passed, 66 deselected, in 7.82 seconds,
axiom counts 7, 8, 3 and 5 unchanged. Report:
`/nix/store/kgdc6q9vcgyp1r4vrnk80fyiwfgnagi1-sqlite-verifier-test-surfaceS6-1/junit.xml`.
`tests/docs_test.py` passed (3 tests). Review `20261029T145241Z-546b0915` of
the merge found no must findings and one should finding: the surface-form
table said every file proves a complete-output equation, but
`UniqueLookupQuery.lean` has only a `Holds` claim and `SampleQueryHints.lean`
has hint functions. Fixed in the next commit.

## Rebase onto main `84c0d779` (2026-11-06)

The branch was rebased with `jj rebase --simplify-parents` onto main
`84c0d779` (210 commits after the earlier base `de0e0462`: ADR 0028 to ADR
0031, the leaf rename of #27 and the CI fixes). The two merges of main became
ordinary commits; the owner's merge of the remote ADR revisions stays a merge.
Two conflicts were resolved in the commits that caused them:

- `tests/sql_file_support.py` (`8a2b159a`): main no longer passes
  `BELAY_PARSER_LIBRARY` to Lake (ADR 0023). The helper keeps only the
  toolchain path and the deployment target, when the caller sets one.
- `tests/nix_suites.json` (`2dab0fe0`): the SELECT experiment test is
  registered at the end of main's current `surfaceS6` list.

The PR's other changes (the five documents, the task files, the four fixtures,
the review records) are unchanged. `just dev-build` passed on the rebased tree
as a diagnostic. Focused Nix evidence: a sandboxed
`nix-build` of `tests.surfaceS6` with `PYTEST_ADDOPTS="-k select_"` ran the
four fixtures on the rebased tree: 4 passed, 66 deselected, in 7.798 seconds,
no failures, errors or skips. Report:
`/nix/store/h16mncz9ffj1rq9bnbaim5z4srbygyml-sqlite-verifier-test-surfaceS6-1/junit.xml`,
rooted at `build/select-automation-tests`. The macOS deployment-target fix is
checked by the `Check (aarch64-darwin)` job of the pull request.

### Reconciliation gaps against main `84c0d779`

The specification documents described main `187ea510`. The gaps below were
found on 2026-11-06; the next section records how each was applied.

1. **ADR 0030 D4, D5 (grouping).** A grouping term is now any expression that
   `WHERE` resolves, with its collation; only a subquery (`group-by-term`) and
   an alias inside an expression (`alias-in-expression`) stay restricted. The
   row of a group is `Query.groupRow`: the row of the deciding `min`/`max`
   call (`Query.deciding`), else the first row; the result columns of
   `Query.firstRowColumns` read the first row. The source map's constructor
   inventory (`Query` fields), its "Conditions that rules must preserve"
   (`group.headD []` under `groupContext`) and its restriction examples
   ("unsupported GROUP BY expressions"), the acceptance's unsupported-form
   list, A07 to A10 and the ADR's D4 group paragraph must say this. The group
   value is one modeled result, not an alternative of `possibleResults`;
   where SQLite's plan decides the row (issue #309) the rules state the
   model's row. `Query.aggregateOf` now sets the deciding call, and the
   duplicate-key laws cover expression keys only under `key.Calm`.
2. **ADR 0031 (the checker).** `#sql_check` builds a compiled screen from the
   claim (D2) and needs a `Decidable` premise and conclusion at the screened
   inputs; a claim without a screen gets explicit witnesses and `unknown`
   (owner decision 2). B10 and ADR 0027 D7 must say what this means for the
   new claim shapes (`Run.returnsResult`, `returnsRows`, `sql_select` goals):
   they are screened when their predicate is decidable, otherwise `unknown`
   is the required answer. The resource list of the acceptance must add the
   time limit of compiled work (`sql.checkTimeLimit`, outside heartbeats) and
   the candidate count (`sql.checkCandidates`); `sql.checkBudget` 100000 and
   `sql.checkRecursionLimit` 4000 are unchanged. The domain premise
   `Database.HasCatalog` (D7) is the name for the "fixed catalog equality" of
   ADR 0027 D4 and the motivating theorem of A01.
3. **Baselines and counts.** The ADR intro, the source map, the retirement
   inventory and the task file name `187ea510`. On `84c0d779` the per-family
   law group is 638 lines (was 620) and the resolution-shape group 1,678 (was
   1,647); every other count is unchanged, and every cited file and
   declaration still exists.
4. **New fixtures.** `ClaimsGroupValues.lean`, `ClaimsExpressionGrouping.lean`
   and `ClaimsConditionalCreation.lean` test model semantics through
   execution and use no per-form law; the inventory's fixture table should
   list the two grouping fixtures as retained.
5. **Links and process.** The retirement inventory and this file link PR 297
   and PR 299 at `vihren-dev/sqlite-verifier`; the repository is
   `vihren-dev/belay`. The review checklist has R20 (expensive tests reuse
   Nix results); the acceptance already puts the A and B fixtures into the
   existing Nix surface suites, and the implementation task file should say
   so.

### Reconciliation applied (2026-11-06)

The owner asked to update the ADR and to be asked about decisions. All five
gaps are applied to the six documents (`docs_test.py`: 4 passed):

1. The ADR's intent paragraph, D4 and the source map state the grouping of
   ADR 0030: a grouping term is any `WHERE`-resolvable expression with its
   collation, a key that can fail is a fault obligation, and a grouped scalar
   column, `HAVING` and a sort key read `Query.groupRow` (the deciding
   `min`/`max` call, else the first row; `firstRowColumns` read the first
   row). The source map's inventory lists `Query.deciding` and
   `Query.firstRowColumns`, links `GroupRow.lean`, and the restriction
   examples name a subquery or an alias inside a grouping term. A07, A09 and
   A10 and the coverage inventory of the acceptance say the same.
2. ADR D7 and B10 say that the checker screens a convenience claim whose
   predicate is decidable (ADR 0031 D2; `Run.returnsResult Q` and
   `returnsRows P` get `Decidable` instances when `Q` or `P` has one) and
   answers `unknown` with the reason otherwise; the proof search runs no
   compiled code. The performance section names `sql.checkTimeLimit` and
   `sql.checkCandidates` as the checker's controls. D4 and the motivating
   theorem name `Database.HasCatalog` (ADR 0031 D7).
3. All baselines name main `84c0d779`; the law group is 638 lines and the
   resolution-shape group 1,678.
4. The retirement inventory lists the three ADR 0030 fixtures as retained and
   adds `GroupRow` and `GroupAssociation` to the definitions that are not
   replaced.
5. PR links point at `vihren-dev/belay`; the acceptance and the task file say
   that the A and B fixtures are modules of the existing Nix surface suites
   (R20).

Review `20261106T195415Z-507d25a3` (Codex) found two R19 "must" points,
both fixed in the following `refactor:` commit: D4 and A07 now state the two
exceptions to `Query.groupRow` (a result column in `firstRowColumns` reads the
first row; a sort key that names a result column reads the projected output),
and D7 and B10 say that a claim without a screen keeps the proof route, its
explicit witnesses, the empty database and the databases that it names, and is
`unknown` only when no certificate is found.

Rule stated for the row of a group: the rules name `Query.groupRow` as the
model's one result and make no claim about native SQLite where its plan decides
the row (issue #309). DECIDED (owner, 2026-11-06): keep this wording; the
rules name the model's one row, and they are amended when #309 is decided. The
alternative, rules that abstract over the representative row, was rejected.

## Deep review (2026-11-06)

The owner asked for a deep review of the ADR by Codex (GPT-6-Astra, reasoning
effort ultra, with web search and local experiments); only the review was
kept, at `/home/codex/work/.adr27-deep-review/review.md` outside the
repository. It found eight points, all confirmed against the code and, for the
`HAVING` divergence, against native SQLite 3.51.0:

1. The intro said the alternatives of `possibleResults` vary "only the order
   of rows". They vary the selection at a LIMIT or OFFSET cut and normalize the
   selected tie groups; `Query.results` need not be a member. Fixed in the
   intro.
2. The grouping-term sentence overstated what resolution accepts. Fixed in
   the ADR and the source map (operand rules of WHERE after the grouping
   checks; integer and alias own rules; a subquery refused).
3. D7 and B10 said `unknown` "only when no certificate is found". A certified
   candidate whose replay cannot be produced is also `unknown`, and screening
   needs supported and supplied inputs and an executable closure (ADR 0031
   D1). Fixed in D7 and B10.
4. The source map's output row did not name the group row. Fixed.
5. The retirement inventory omitted `ScalarNoFrom.lean` and claimed a net
   reduction that the baselines do not establish. Fixed: a row for the file
   and a measurement caveat.
6. No evidence showed that phase rules compose. Added the three fixtures
   `tests/surface/SelectAutomationPhaseRules.lean` (nine rules),
   `SelectAutomationPhaseBridge.lean` (the D2 observer, `run_of_faultless`,
   `outputs_of_calm_table`) and `SelectAutomationPhases.lean`
   (`schema_projection_phases`, the grouped `HAVING` proofs and their
   witnesses), registered as `test_select_phase_rules_compose` in
   `tests/surface_select_automation_test.py` with axiom counts 9, 3 and 5.
   The ADR's validation section and the review cover cite them.
7. D2's scalar convenience needed the quiet premise of `ScalarNoFrom` and the
   clause that a statement count permits a `.done` output. Fixed in D2.
8. The `Query.groupRow` limitation reaches `HAVING`, the cardinality of the
   result, nested queries and continuations, and a quantifier over execution
   branches does not cover SQLite's plans. Stated in D4 and in the A10
   contrast of the acceptance; the owner keeps the model's one row until
   issue #309 is decided.

Nix evidence for the fixtures: a sandboxed `nix-build` of `tests.surfaceS6`
with `PYTEST_ADDOPTS="-k select_"` ran the five SELECT automation tests: 5
passed, 66 deselected, no failures, errors or skips. Report:
`/nix/store/yiv0vsp2zqnaqvwwzskpw4larjrcpa6k-sqlite-verifier-test-surfaceS6-1/junit.xml`,
rooted at `build/select-automation-tests`.
`tests/docs_test.py` passed (4 tests) after the document edits.

Review `20261106T214403Z-d4b95e3a` (Codex) of the fixture commit found no
must findings and two should findings (R12): the rules and the proofs fixtures
had 202 and 204 lines. Both fixed in the following `refactor:` commit by
shorter module docstrings and proofs (199 lines each); the chain compiles
unchanged. Nix evidence after the fix: the same focused `surfaceS6` build, 5
passed, 66 deselected. Report:
`/nix/store/dncxsrhgbymmykijlxrfjf3miachlpq7-sqlite-verifier-test-surfaceS6-1/junit.xml`.
Review `20261106T214630Z-66d021e0` (Codex) of the refactor commit found nothing.
Review `20261106T214758Z-f199fe41` (Codex) of the specification commit found
one should finding (R19): the retirement measurement still counted fourteen
surface files after the `ScalarNoFrom.lean` row was added. Fixed in the
following `refactor:` commit: fifteen files, 1,328 physical lines, 905
maintained code lines, 2,553 with the model files (`scc` on main `84c0d779`
plus the 86-line, 61-code-line `ScalarNoFrom.lean`).
Review `20261106T214907Z-50657f9e` (Codex) of that refactor found nothing.

## Rebase onto main `c54d8395` and acceptance (2026-11-07)

PR 299 was rebased onto main `c54d8395` without conflicts. The six new main
commits change only Nix suite plumbing (the model suite split, #353) and leaf
names of the Belay rename (#27); they change no Lean file, so the baselines
and line counts of the documents, measured on `84c0d779`, still hold. Focused
Nix evidence on the rebased tree: the `surfaceS6` build with
`PYTEST_ADDOPTS="-k select_"` ran the five SELECT automation tests: 5 passed,
66 deselected. Report:
`/nix/store/ymjdljjvdjs1x47zpjr088jg2np42zln-sqlite-verifier-test-surfaceS6-1/junit.xml`.

The owner then asked to implement the ADR (2026-11-07). The ADR, the
acceptance contract, the review cover and the retirement inventory now say
ACCEPTED. The implementation has its own task and status files.

## Open design axes

The revised proposal fixes the successful-result bridge domain, entry goal forms,
rule matching and ordering, local/global registration, replay meaning and reuse
of current public budgets. The owner review concerns these proposed interfaces
and the stated automatic coverage, not unresolved implementation prerequisites.
The new procedure's performance and the A01-A22/B01-B11 acceptance results can
only be established during implementation; this specification does not claim them.
