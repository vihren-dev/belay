# Record the provenance of each test execution (#332)

Created 2026-11-06. Status: DONE (2026-11-06).
Audience: implementers and reviewers.
Progress: [status](20261106-test-provenance.status.md).
Inspected base: the #330 fix of [the narrower mutant inputs](20261106-narrow-mutant-inputs.task.md).

## Present problem

The owner asked for a fix of #332. Each row of `belay_observability.test_executions`
has `metadata = {}`: the analysis of the mutant-suite cost (#328 to #331) could not
separate CI runs from local runs, Linux from macOS, or tell the commit and the Nix suite
of an execution. `docs/test-observability.md` says to add metadata fields "when a
concrete query needs them"; #332 names the query: test time per suite, platform and CI
event, and the runs of each `main` push. `experiments/observability/README.md` chose the
source: allowlisted CI variables and jj commit and change IDs, attached outside the
derivations.

## Required outcomes

- Each execution that the host Nix wrapper (`tools/observability_nix.py`, which the `just`
  test recipes and CI use) imports because its builder ran during the command records, in
  `metadata`, the values that are available:
  - `event`: `GITHUB_EVENT_NAME` on GitHub Actions, otherwise `local`.
  - `platform`: the Nix system name of the host, for example `x86_64-linux` or
    `aarch64-darwin`.
  - `run_id`, `run_attempt` and `job`: the GitHub Actions run, attempt and job, on CI only.
  - `commit`: `GITHUB_SHA` on CI. Locally, the jj commit ID of the last snapshot of the
    working copy `@`, and `change`, its change ID. Edits after the last jj command are
    not in that snapshot, so locally these IDs do not identify unsnapshotted inputs.
  - `suite`: the Nix suite name of a successful output. An execution recovered from the
    log of a failed build has no `suite`: `nix-build` interleaves the logs of parallel
    builders without a prefix, so a frame does not name its derivation.
  A value that is not available is absent. No value is guessed.
- Per-run provenance never enters a Nix derivation or a builder. The builder writes the
  same manifest as now (`metadata: {}`), and the host adds the provenance when it imports
  the execution from a Nix output or a build log.
- The change does not touch the shared harness files that every Nix suite reads (`common`
  in `build-support/tests.nix`: the pytest plugin, the records, spool, upload and log
  modules), so no suite derivation changes and no cached test result is lost. Pytest
  sessions on the host outside the wrapper keep `metadata: {}`; they are not part of the
  query of #332.
- The wrapper does not import an execution that started before the command, that is a
  cached result. A cached result was imported by the command that built it. Importing it
  again with its original `metadata: {}` would replace the provenance in ClickHouse
  (`ReplacingMergeTree` keeps the last row of an `execution_id`), and ADR 0028 forbids
  relabeling it with the provenance of the retrieving command. So a result that a direct
  `nix-build` built is no longer recovered from the cache by a later wrapper command; the
  wrapper must build it. ADR 0028 ("Reimporting cached Nix results recovers original
  observations") is amended with this change and its reason.
- The ClickHouse schema and the uploader do not change. Metadata stays a JSON object.
- `docs/test-observability.md` lists the fields and gives the query of #332.

## Tests and acceptance

- Unit tests of the provenance function with a given environment: a GitHub Actions
  environment gives all CI fields; an empty environment gives `local`, the platform and
  no CI fields; a failing or missing `jj` leaves `commit` and `change` absent; variables
  outside the allowlist never appear.
- A test of the wrapper's collection with two prepared outputs: an execution that started
  before the command is skipped, one that started during it is imported with the
  provenance and the suite name of its output.
- A test that recovery from a build log adds the provenance.
- The existing observability tests (`tests/test_observability.py`,
  `tests/test_observability_identity.py`, the ClickHouse suite) pass, and the Nix
  derivations of all test suites are unchanged.
- Acceptance after the merge: the query of #332 groups the executions of the first CI
  run and of one local `just` run by event and platform. The pull request says that this
  needs the first `main` run and the upload workflow.

## Key points for the implementer

- `import_execution` (`tools/observability_spool.py`) and `recover`
  (`tools/observability_logs.py`) are shared files that stay unchanged. The wrapper can
  stage an execution in a temporary directory, write its manifest with the provenance
  there, and import that copy; for build logs it can recover into a staging spool first.
- `import_execution` rejects a second import of the same identity with other bytes. A
  command that reaches one execution twice (a link farm and its child) must write the
  same metadata both times, so compute the provenance once per command.
- The started time of a builder's execution and the start of the command come from the
  same host clock. Compare them in UTC. Substituted outputs started earlier and are
  skipped.
- The suite name of a Nix output is in its store path: `HASH-sqlite-verifier-test-NAME-1`.
  A link farm entry is a symlink to that path.
- Run `jj --ignore-working-copy` with a short timeout, so that reading the commit does not
  snapshot or change the working copy while tests run.
- The CI uploader (`tools/observability_ci.py`) reads artifacts as data and must not add
  provenance: the test job that wrote the artifact did.
