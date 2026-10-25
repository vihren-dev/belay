# Status: keep the model suite within its time limits on hosted macOS

Created 2026-10-25. Status: DONE (the hosted macOS run is for the owner to check).
Task: [task file](20261025-macos-model-suite-limit.task.md).
Relevant files: `conformance/model_check.py`,
`tests/conformance_query_coverage_test.py`, `tests/nix_suites.json`,
`build-support/tests.nix`.

## Progress

- 2026-10-25: task written from the hosted runs `40156468777` and
  `40174999810`, whose macOS `Check` jobs failed in the `model` suite.
- 2026-10-25: the first implementation attempt stopped at the measurements: one
  case, `jsonb-header-sizes`, takes 50 s alone, so batching cannot meet outcome
  1. The task file now records the measurements. The coordinator decided: step
  1 amend the task (this commit); step 2 split `model` into three suites (the
  rest, the first 28 coverage case modules, the later 17); step 3 make the
  kernel evaluation of the JSONB text encoding cheaper, with byte-identical
  predictions; step 4 the Nix gates.
  Measurement tools: `build/agent-logs/focused-model.nix` and `.sh` (focused Nix
  run with a timer around each Lean process), logs `focused-baseline.log`
  and `focused-jsonb-b1.log`.
- 2026-10-25: step 2, commit `108d6f62`. `model` is now three suites: `model` (206
  tests), `coverageStatements` (28 coverage tests: case modules up to
  `authored_drops`) and `coverageFeatures` (17 tests: from
  `authored_text_functions`). Both coverage suites use
  `tests/coverage_case_support.py`. Registered in `tests/nix_suites.json`,
  `build-support/tests.nix`, `developmentTests` of `build-support/default.nix`,
  `tests/test_nix_test_targets.py`, `tests/test_conformance_frontend.py`,
  `docs/ci.md` and `build-support/README.md`. Focused Nix runs of the three
  suites (`build/agent-logs/focused-split-*.log`; one heavy slot, max-jobs 1,
  cores 2; load average 3 to 12 from other jobs, so each time is an upper
  bound): `coverageStatements` 382.8 s, `coverageFeatures` 298.1 s, `model`
  315.1 s, against 840.3 s for the old `model` suite (46 %, 35 % and 38 %;
  the target was at most 60 %). Store paths:
  `/nix/store/01d5a6l454xxc2x9bm9zvy5g7ahfnq0b-sqlite-verifier-test-focused-coverageStatements-1`,
  `/nix/store/bjangqkl1jx3a3y8xzrgd74nhxv6zc1s-sqlite-verifier-test-focused-coverageFeatures-1`,
  `/nix/store/03596ymca9lnfszvlhgibla5mzz58mja-sqlite-verifier-test-focused-model-1`.
- 2026-10-25: step 3. The kernel evaluation of the JSON text reader was quadratic in
  the length of a string, because the kernel reads an element of an `Array` by walking
  its list (`Array.size` is `List.length`, `Array.get` is `List.get`), and the reader read
  each byte of a string with `byteAt`, and copied the string with `slice`, which read
  each byte again with `byteAt`. `slice` (`Json/Bytes.lean`) now takes the bytes with one
  `List.drop` and `List.take`; `scanString` is now `scanStringFrom` (`Json/ReadScalar.lean`)
  and walks the list of the remaining bytes; `hasHexDigits` uses the new
  `startsWithHexDigits`. The semantics are the same: a position past the end is 0. Local
  kernel time of the proof of `jsonb-header-sizes` (`lean` on `Case1.lean`): 56.6 s before,
  7.7 s after (single-expression `jsonb('"<300 bytes>"')`: `readString` alone 7.5 s to 0.35 s).
  The
  53 prediction files of `integrity/judge.nix -A predictions` are byte-identical: baseline
  (commit `108d6f62`)
  `/nix/store/hkvlvawsx4fk1zvcknmh5gn4m0kkynps-sqlite-verifier-predictions`, with the fix
  `/nix/store/9z2qckqphdmnjfqhjbzpxc3m82shp51g-sqlite-verifier-predictions` (`diff -r`
  empty). No mutant targets `Json/Bytes.lean` or `Json/ReadScalar.lean`.
- 2026-10-25: reviews of the step 3 commits. Review `20261025T103113Z-e97aeb14`: one must
  (`ReadScalar.lean` had 202 lines) and one should (the status cited local runs); both
  fixed in `ad592d69`. Review `20261025T103446Z-ad592d69`: no findings. The prediction
  comparison above was run again on the final sources (`ad592d69`): the output is
  `/nix/store/9z2qckqphdmnjfqhjbzpxc3m82shp51g-sqlite-verifier-predictions`, identical to
  the baseline.
- 2026-10-25: part end, on the merge of `32992b77` and `2b10c963`. Nix results: the focused
  run of `coverageFeatures` after the fix (17 passed, 247.0 s, against 298.1 s before; load
  average 3 to 10 from other jobs; slowest proof process 25.1 s, `authored_numeric_functions`;
  `authored_jsonb` 21.6 s, against 55.8 s before):
  `/nix/store/x0zvin4d7ffm7p659dm9phwjibv1mnh7-sqlite-verifier-test-focused-coverageFeatures-1`.
  `just test-full` passed with no skipped test: `model` 206 tests, `coverageStatements` 28
  and `coverageFeatures` 17 (the three suites ran at the same time with the other suites, so
  their times, 435.6 s, 435.9 s and 410.0 s, are not comparable with the focused runs):
  `/nix/store/7bzsbwqqzrclmqxcl3cgj88mlsshdhgm-sqlite-verifier-test-reports`. `just verdict`
  passed: `/nix/store/942a63aj46vik43gk06lrqgxjjsf6663-sqlite-verifier-verdict`.
- 2026-10-25: task end, on the same tree. `just test-nix` passed (71 passed, 363.7 s). `just
  test-scheduled-checks` passed:
  `/nix/store/4awcmzn3qs6l9245gqpfj9c19sq5grdw-sqlite-verifier-scheduled-check-reports`.
  DONE. The hosted macOS `Check` job of a pull request is the last check; the owner runs it.
- 2026-10-25: integration merge `48f54842` (this limit above the SQL doc blocks): `just test-full` passed at
  `/nix/store/vqmd2nrczb21dgib16c5rf7vkhk5882z-sqlite-verifier-test-reports` (rerun after one stop at the 1500 s build
  limit); `just verdict` passed at `/nix/store/s5vdvv5xshkazwhbccqxiwv26858q94f-sqlite-verifier-verdict`.
