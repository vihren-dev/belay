# Status: keep the general mutant tests within their time limit

Created 2026-10-25. Status: DONE on 2026-10-25.
Task: [task file](20261025-query-mutant-time-limit.task.md).

## Progress

- 2026-10-25: task written from the hosted run `40156468777` of PR #252, which
  showed the query mutant test above its 300 s limit on Linux and macOS.
- 2026-10-25: implementation. The query mutant test is now three tests by model
  file (`Comparison.lean`; `QueryEval.lean` and `QueryResults.lean`; the
  `Resolution` folder), and the JSON mutant test is two tests (JSON reading;
  JSON functions) in `tests/conformance_query_mutants_test.py`. The module
  docstring tells the measured durations and the current layout (one hosted job
  per mutant suite).
- Method: the suite derivation `scheduledTests.<suite>` with its pytest
  selection narrowed by `-k` and a timer around each Lean command, as in
  `research_notes/Lean model modularity investigation/ci249-mutants/`
  (`build/agent-logs/focused-mutants.nix`, `focused-mutants.sh`, logs
  `focused-*.log`), each run in a heavy slot with max-jobs 1 and cores 2.
  Another heavy job shared the eight cores in every run (load average 10 to
  15), so each time is an upper bound of the time alone. The old
  arithmetic test, documented at most 124 s alone, took 191 s in this load: the
  load factor is at least 1.5.
- Local Nix durations (call time of one test): comparison 109.5 s, evaluation
  82.9 s, resolution 72.5 s, JSON 122.8 s, JSON functions 112.5 s. Not changed:
  resolve mutants 137.0 s (hosted: passed at 228 s and 209 s); derived source
  and join padding 51 to 65 s each; the other tests of the `mutants` suite
  between 63 and 211 s, listed in the final report; `tableMutants` 50 to 181 s;
  `functionMutants` 75 to 130 s (both passed on hosted Linux).
- 2026-10-25: review `20261025T044837Z-fd9c46c0` (R12, should): the test file
  grew from 187 to 242 lines. The tests of subqueries, expression forms,
  DISTINCT and HAVING, foreign keys, triggers, possible results, parameters,
  compound SELECT and pragmas moved unchanged to
  `tests/conformance_query_feature_mutants_test.py` (97 lines), listed in the
  `mutants` suite of `tests/nix_suites.json`. The query mutant test file has
  163 lines.
- 2026-10-25: review `20261025T045934Z-ff196a1c` of the refactor commit:
  no findings. Nix results at `ff196a1c`: `just test-full` exit 0 (472 source
  tests passed; Nix reports `/nix/store/nxmw2w3ywpjhzar69ww9f42yffvi5vhl-sqlite-verifier-test-reports`,
  10 suites, 0 failures); `just verdict` exit 0
  (`/nix/store/93lqb1sa4smkvfbcsq95hyyijj90b94f-sqlite-verifier-verdict`);
  `just test-nix` exit 0 (71 passed); `just test-scheduled-checks` exit 0
  (`/nix/store/fr5hdf7cri54bqc2ha8f6g5k7h0sd953-sqlite-verifier-scheduled-check-reports`).
  A first `just test-full` failed once in the source tests:
  `tests/test_model_ownership.py::test_neutral_consumer_uses_structural_facts`
  timed out at its 30 s command limit while the VM load average was 14; the
  log is `build/agent-logs/qm-test-full-attempt1-failed.log`, and the repeat
  passed. The hosted run of the `mutants`, `tableMutants` and `functionMutants`
  jobs is still to do (owner).
- 2026-10-25: hosted validation. The owner started the manual CI run
  `40174999810` on `tasks/query-mutant-time-limit` (PR #253, `8da7184e`).
  All six mutant jobs executed all their tests and passed:
  `mutants` (Linux 08:01–08:47, macOS 08:01–08:51), `tableMutants` and
  `functionMutants` on both platforms. The task is DONE. In the same run the
  macOS `Check` job failed in the `model` suite (not a mutant suite); that
  failure is the task `20261025-macos-model-suite-limit`.
