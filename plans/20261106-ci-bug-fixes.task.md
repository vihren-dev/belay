# Fix the CI bugs #333, #326, #329, #327 and #328

Created 2026-11-06. Status: open.
Audience: implementers and reviewers.
Progress: [status](20261106-ci-bug-fixes.status.md).
Inspected base: `tasks/check-real-schemas` (PR #324), `23194e0d`.

## Present problem

The owner asked for a fix of the open bug issues, in this order, stacked on PR #324:

1. #333: the macOS check fails on every `main` push. The Nix sandbox on macOS does not
   let the `observability` suite bind `127.0.0.1` for its ClickHouse server.
2. #326: `publish-nix-store` never finds the store that the check job saved. The two
   jobs calculate the cache key with `hashFiles('**', ...)` over different trees: the
   check job runs Python modules before the key is calculated and writes `__pycache__`
   files into the checkout. The publisher skips the upload and reports success.
3. #329: each of the 98 mutant tests builds the same base copy of the model (56 s on
   this VM), about 90 minutes per platform per run.
4. #327: `publish-nix-store` has `needs: check` over both platforms, so a failed macOS
   check stops the publication of a passed Linux check.
5. #328: the `mutants` job reruns all 12 mutant suites on every `main` push and nightly
   run, also when the Nix derivation of a suite is the same as in an accepted run.

The issues give the evidence (hosted runs, ClickHouse durations). Each fix is one pull
request of the stack, in the order above.

## Required outcomes

- **#333.** The `observability` suite derivation allows local networking in the macOS
  sandbox. No other suite gets this permission. The Linux derivation changes only by
  this attribute.
- **#326.** The check job, the `mutants` job and `publish-nix-store` calculate the same
  primary key for the same commit and platform, whatever files the earlier steps of a
  job write into the checkout. The key still excludes `plans/` and `reviews/`, and the
  restore prefixes stay valid, so the archives that exist now can still be restored.
  When the publisher finds no archive for the key, its log says so as a warning.
- **#329.** A test process builds the base copy of the two Lean packages once, and each
  later measurement in the process uses it. Each measurement still checks that every
  case has the expected verdict with the unchanged model. Each mutant still gets a
  fresh copy of the built base. The documented time of a base build is the measured one.
- **#327.** On an eligible run (`main` push or nightly), each platform publishes its
  saved store when its own check passed, also when the check of the other platform
  failed. Only a store that a passed check saved is published: a failed check saves no
  store, so its outputs are never published. When an earlier run of the same tree
  passed on that platform, its saved store is the store of that tree and is published
  again, also if the current check failed; the upload then adds no new paths. The
  `attic-publish` environment, the token scope and the trusted events stay the same. A
  cancelled run publishes nothing.
- **#328.** A mutant suite whose Nix derivation is the same as in an accepted `main`
  push or nightly run on the same platform does not run again: the job restores the
  JUnit report of that run and retains it as the job's report. Only a passed run of an
  eligible event saves a report. Any change of the derivation (sources, inputs, pins,
  toolchain) runs the suite. Pull request runs can reuse reports but never save them.

## Tests and acceptance

- `tests/test_nix_test_targets.py`: the evaluated `observability` derivation has
  `__darwinAllowLocalNetworking = true`, and no other suite has it.
- `tests/test_ci_workflow.py`: the three jobs use one key expression that comes from a
  step that runs before any step that writes into the checkout; a test runs the key
  command in a temporary Git repository before and after it writes `__pycache__` and
  build files, and gets the same key, and a different key after a change of a tracked
  file outside `plans/` and `reviews/`. The publisher's gate is per platform and needs
  the platform's saved archive, not the success of both checks. The `mutants` job keys
  its report cache by the suite derivation and saves only on a passed eligible run.
- `tests/mutation_edits_test.py`: two `measure` calls with a fake Lake and a fake
  runtime build the base once and build each mutant copy, and the unchanged-model check
  still runs in each call.
- `docs/ci.md` describes the new key, the per-platform publication and the reuse of
  mutant reports; its documentation tests pass.
- End of the task: `just test-full`, `just verdict`, `just test-nix`,
  `just test-scheduled-checks`, and one mutant test by name for #329
  (`tests/conformance_function_mutants_test.py -k printf`). The hosted checks of the
  pull requests are the evidence for the workflow changes; macOS runs only on `main`.

## Relevant code and constraints

- `build-support/tests.nix`, `suite`: `environment` is merged into the derivation, so a
  derivation attribute goes there.
- `.github/workflows/ci.yml`: `nix-community/cache-nix-action` runs its save step with
  `post-if: success()` (pinned `7df957e3`), so an archive under a commit's primary key
  exists only after a passed check job of that tree and platform, in this run or an
  earlier one. The publisher can use this as the acceptance signal of its own platform.
- A matrix job cannot give one output per matrix entry reliably, which is a reason to
  avoid job outputs for the per-platform gate.
- `conformance/resolve_mutants.py`, `measure` and `verdicts`; `tests/mutant_sets.py`.
  The Nix suite runs one pytest process, so a process-wide base is one build per suite.
  The base is read-only after its build; the mutant copies are taken with
  `copytree(..., symlinks=True)`.
- `nix-instantiate build-support/default.nix -A scheduledTests.SUITE` evaluates a suite
  in about 1 s with no import from derivation, so the `mutants` job can calculate the
  derivation path before it restores the large store.
- The GitHub cache holds about 10 GB, nearly all store archives (#327); a mutant report
  is a few kilobytes.
- `docs/ci.md` and `plans/20260929-attic-ci.status.md` (the earlier upload inside the
  check job was rolled back; publication stays in its own job).
- Do not run the mutant suites locally (`just test-mutants`), and do not start manual
  macOS runs.
