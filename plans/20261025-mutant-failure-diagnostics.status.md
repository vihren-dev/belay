# Mutation failure diagnostics status

Created 2026-10-25. Status: DONE.
Task: [required outcomes](20261025-mutant-failure-diagnostics.task.md).

The published #250 hosted log reports three failed groups before outer timeout
exit 124, without final pytest failure details or a general-mutant report
artifact. The task preserves complete successful-run coverage and all existing
limits while making an already reported failure diagnosable. It does not infer
the cause of the query/JSON failures.

Task review `20261025T013944Z-ef3c7307` found no must findings and one R19 should:
state why scheduled acceptance excludes broad local mutation runs. The task now
cites the owner's restriction and requires an actual hosted manual run, since
the PR change filter skips mutation jobs for this change. The finding is fixed;
clarification review `20261025T014013Z-d7844328` has no findings. The
implementation base is published #251, `fe169099`; the view worker takes
this bounded follow-up in an isolated workspace after task review.

The isolated `mutant-failure-diagnostics` workspace is ready on `fe169099`.
Its four development-shell configuration files match the approved planning
workspace byte for byte; `direnv allow` used the owner's standing authorization.

## Implementation and command inspection

The common Nix suite command appends pytest's `--exitfirst` only for names in
the existing `tests/nix_mutant_suites.json`. A reported failure therefore ends
that suite before later groups consume its budget. The successful path keeps
the same complete test-file inventory and assertions. No runner or plugin is
added; the independent CI matrix's `fail-fast: false` is unchanged.

The existing evaluated-command test checks the conditional flag along with the
complete file list, 300-second per-test limit, 2700-second mutant suite limit,
1200-second ordinary suite limit and report arguments. The focused command,
routing, ownership, scope and limit checks are local diagnostics only;
the Nix acceptance gates follow independent review.

Before/after evaluation of all 14 suite commands is retained under
`build/agent-logs/mutant-diagnostics-{before,after}.json`. The three mutant
commands differ only by `--exitfirst`; all eleven ordinary commands are
byte-identical. Only the three mutant derivations and the surface derivation
change: the surface layer checks read the changed build configuration, although
its command is unchanged. Earlier mutant results are not claimed as acceptance
of the changed command. No broad local mutant suite runs.

`mutant-diagnostics-command-comparison.json` records these equalities and the
unchanged protected trees. Packages, conformance/native/corpus sources, judge,
integrity and oracle inputs match `fe169099`. The judge lock SHA-256 is
`3ed3054ac313591582e038ecad92b04c81fea33d2559a97ba5a847198196831c`.
Post-review full/verdict and task-end Nix/scheduled checks are assigned heavy
slot 1. The task remains OPEN until the required hosted manual run is inspected
after publication; a skipped PR mutant job is not execution evidence.

Source `e148e0e495624c17972997f2348e9a88956cc323` has clean independent review
`20261025T014300Z-e148e0e4` (0 must, 0 should). The sequential bounded gate is
`build/agent-logs/mutant-diagnostics-acceptance.sh`; it compares predictions
against the accepted #251 output
`/nix/store/nvd3jnygzz7i4w29wyfx34zfpwbfvjdm-sqlite-verifier-predictions`.

## Local acceptance and publication handoff

The post-review sequence on evidence revision `10aa47c3` completed with exit 0.
The tested source remains `e148e0e4`; the independent review covers both
`build-support/tests.nix` and `tests/test_nix_test_targets.py`. No package source
changed, so a local package rebuild was not required.

- `timeout 3000 just test-full`: 949 tests passed, with no failures, errors or
  skips, in `/nix/store/nxmw2w3ywpjhzar69ww9f42yffvi5vhl-sqlite-verifier-test-reports`.
- `timeout 2000 just verdict`: passed with 4,869 agreed and 2,503 unsupported
  cases. The output is the unchanged
  `/nix/store/93lqb1sa4smkvfbcsq95hyyijj90b94f-sqlite-verifier-verdict`.
- The prediction build returns the same `nvd3jnyg...` output named above.
  All 53 files and 7,372 cases are byte-identical to the accepted #251 baseline.
- `timeout 600 just test-nix`: all 71 checks passed. The report is
  `build/test-results/nix.xml`.
- `timeout 1500 just test-scheduled-checks`: all 47 writer checks passed in
  `/nix/store/fr5hdf7cri54bqc2ha8f6g5k7h0sd953-sqlite-verifier-scheduled-check-reports`.

The XML totals and exact protected-source comparison are retained in
`build/agent-logs/mutant-diagnostics-acceptance.json`; the command logs share the
`mutant-diagnostics-` prefix. Production packages, all conformance inputs,
judge, integrity and native oracle configuration still match `fe169099`.
The publication body is `build/agent-logs/pr-body.md`.

Status remains OPEN. Root will publish this change above #251 and dispatch the
existing manual CI workflow on that exact published revision. Actual hosted
mutation execution and any exposed failure details must be inspected before
completion. Skipped PR mutation jobs and these ordinary acceptance gates do not
replace that requirement. The unconfirmed query/JSON causes remain separate
investigations.

## Hosted mutation run

The owner started the manual CI run `40156468777` on `296f3a57`. The mutation
commands executed. `functionMutants` and `tableMutants` passed on Linux.
The `mutants` suite failed on both platforms at its second test,
`test_every_query_mutant_changes_a_verdict`, with
`Timeout (>300.0s) from pytest-timeout` (Linux 300 s, macOS 319 s); the first
test passed (228 s and 209 s). `--exitfirst` ended the suite with its pytest
summary and JUnit report, as this task requires. The job logs are retained as
`build/agent-logs/ci252-manual-job-{linux,darwin}.log`. The repair is the
separate task [query mutant time limit](20261025-query-mutant-time-limit.task.md).
This task's required outcomes are met; it is DONE.
