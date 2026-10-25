# Status: keep the model suite within its time limits on hosted macOS

Created 2026-10-25. Status: OPEN.
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
