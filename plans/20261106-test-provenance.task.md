# Record the provenance of each test execution (#332)

Created 2026-11-06. Status: open.
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

- Each execution that a repository command runs records, in `metadata`, the values
  that are available:
  - `event`: `GITHUB_EVENT_NAME` on GitHub Actions, otherwise `local`.
  - `platform`: the Nix system name of the host, for example `x86_64-linux` or
    `aarch64-darwin`.
  - `run_id`, `run_attempt` and `job`: the GitHub Actions run, attempt and job, on CI only.
  - `commit`: `GITHUB_SHA` on CI; locally the jj commit ID of the working copy `@`.
    Locally also `change`, the jj change ID of `@`.
  - `suite`: the Nix suite name, for an execution of a Nix test suite.
  A value that is not available is absent. No value is guessed.
- Provenance never enters a Nix derivation or a builder. A builder records the same
  manifest as now. The host adds the provenance when it imports the execution from a
  Nix output or a build log. No derivation changes, so no cached test result is lost.
- The host imports an execution from a Nix output only when that execution started
  during the command (the builder ran). A cached output was imported by the command that
  built it; importing it again would replace the provenance in ClickHouse
  (`ReplacingMergeTree` keeps the last row of an `execution_id`). A pytest session on
  the host records its provenance when it starts.
- The ClickHouse schema and the uploader do not change. Metadata stays a JSON object.
- `docs/test-observability.md` lists the fields and gives the query of #332.

## Tests and acceptance

- Unit tests of the provenance function with a given environment: a GitHub Actions
  environment gives all CI fields; an empty environment gives `local`, the platform and
  no CI fields; a failing or missing `jj` leaves `commit` and `change` absent; variables
  outside the allowlist never appear.
- A test of the Nix wrapper's collection with two prepared outputs: one execution that
  started before the command is skipped, one that started during it is imported with the
  provenance and the suite name of its output.
- A test that recovery from a build log adds the provenance.
- The existing observability tests (`tests/test_observability.py`,
  `tests/test_observability_identity.py`, the ClickHouse suite) pass.
- Acceptance after the merge: the query of #332 groups the executions of the first CI
  run and of one local run by event and platform. The pull request says that this needs
  the first `main` run and the upload workflow.

## Key points for the implementer

- The pytest plugin (`tools/observability_pytest.py`) also runs inside builders, where
  `BELAY_OBSERVABILITY_BUILD=1`. There it must keep writing `metadata: {}`, or the
  provenance of the host would enter the derivation's output.
- `import_execution` rejects a second import of the same identity with other bytes. A
  command that imports one execution twice (a link farm and its child) must write the
  same metadata both times, so compute the provenance once per command.
- The started time of a builder's execution and the start of the command come from the
  same host clock. Compare them in UTC. Substituted outputs started earlier and are
  skipped.
- The suite name of a Nix output is in its store path: `HASH-sqlite-verifier-test-NAME-1`.
  A link farm entry is a symlink to that path.
- Run `jj --ignore-working-copy`, so that reading the commit does not snapshot the working
  copy, with a short timeout. Record the commit of `@`: the code that ran is the working
  copy.
- The CI uploader (`tools/observability_ci.py`) reads artifacts as data and must not add
  provenance: the test job that wrote the artifact did.
