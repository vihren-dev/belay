# Observability extraction experiments

Status: DONE, 2026-11-02. Created 2026-11-02. Audience: the team.

Result: [experiment report](../experiments/observability/README.md), with
[captured summaries](../experiments/observability/results.json).

## Purpose

The owner requests repeatable experiments that determine how to collect review,
test, coverage, proof and build data as development continues. The owner requires
supported interfaces and small integrations. A mechanism that requires compiler
patches, private protocols, source rewriting or elaborate interception is rejected
for the first implementation, even if it can produce more detail.

The experiments belong in the dedicated `observability-experiments` jj workspace,
under `experiments/observability/`. Production collectors, ClickHouse deployment,
CI policy changes and automatic test removal are outside this task.

## Required outcome

The experiment report identifies each requested signal as collect now, collect
with a small documented integration, defer, or unavailable in the measured scope.
Every accepted mechanism has a runnable example, captured output, tool versions,
an extraction description and its limitations. Negative results are evidence:
the report must not turn a failed probe into an unsupported workaround.

The report covers these questions:

- Can the existing review records be exported without losing findings, resolutions,
  checklist versions or existing statistics? Which requested fields do they lack?
- Can pytest provide inventory, selection, stable parametrized identities, phase
  timing, outcomes and partial results through documented hooks and JUnit output?
  What survives ordinary failure, setup failure and process termination?
- Can coverage.py/pytest-cov associate Python execution with cases, including a
  subprocess? Does collection preserve attribution, rather than just total coverage?
- What can the pinned Lean and Lake expose through their normal commands: messages,
  imports, build reuse, profiling, axiom dependencies and existing repository exports?
  Do these answer runtime path coverage or only build/proof questions?
- Can Nix expose derivation identities, dependency changes, build versus reuse,
  timing and failed-test output without parsing its private event protocol?
- How are CI run/attempt/job/platform identities and local source identities joined
  to these results? What is available directly, and what needs a small wrapper?
- What existing requirement and mutation records can support overlap analysis?
  Distinguish batch results from a per-test mutant detection matrix.

The final recommendation defines a small initial data contract, extraction points,
collection cadence and explicit unknown states. It distinguishes live measurements
from cached artifacts, runtime coverage from proof dependencies, and measured
capabilities from proposals. It explains how the data will support continuing
analysis of suite growth and unnecessary execution.

## Verification

Bounded experiments exercise the integrations end to end with the pinned tools.
Python probes cover passing, failing, skipped, parametrized and setup-error cases,
selection and a terminated run. Coverage probes distinguish two code paths and
check subprocess attribution explicitly. Lean/Lake probes compare a fresh build,
reuse and a changed input; demonstrate ordinary diagnostics, imports, profiling
and axiom output; and inspect existing Belay dependency/proof-cost outputs where
available. Nix probes compare a fresh build, reuse, changed relevant and irrelevant
inputs, and a deliberate failed test build. Review export is checked against
existing records/statistics. These are explicit research probes, not additions to
the permanent test suite of dependency behavior.

Each probe has a timeout, writes to an isolated output directory, and checks its
observations against its fixture. A sandboxed Nix experiment target supplies
reproducible evidence for probes that can run in a builder. Nix-daemon and local
execution observations remain separately labelled. The report gives reproduction
commands and references small captured summaries rather than checking in logs
without bounds. Existing records and development evidence are not modified.

## Relevant code and constraints

`tools/review_records.py`, `tools/review_log.py` and `tools/review_stats.py` own
review history. `conftest.py`, `pytest.ini`, `tools/test_reports.py`,
`tools/ci_checks.py`, `tests/ci_scope.py` and `build-support/tests.nix` define
test collection, reports and reuse. `.github/workflows/ci.yml` retains CI output.

`conformance/instrument_model.py` rewrites selected branches and is not a basis
for a new supported Lean coverage mechanism. `conformance/model_assertions.py`
emits concrete-case proofs and axiom reports. `build-support/theorem-dependencies.nix`
already exports theorem dependencies. `packages/belay/Belay/Sqlite/ProofCost*.lean`
provides existing proof-cost data with a narrower meaning than full proof time.

Nix builders have no uploader credentials or network dependency for collection.
An imported proof artifact is not a freshly checked theorem. A missing coverage
hit in a partial instrumenter does not justify skipping a test. Stable test names
do not identify unchanged inputs; source and runtime identities are also needed.
