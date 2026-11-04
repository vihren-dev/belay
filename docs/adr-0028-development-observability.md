# ADR 0028: Pytest observability with ClickHouse

Date: 2026-11-02. Revised: 2026-11-04. Status: PROPOSED.
Audience: designers and reviewers. Implementation has not started.

## Problem and scope

The owner needs a continuing record of test executions and durations during local
development and CI. New pytest cases and suites must inherit collection and
automatic upload without changes to individual tests.

This decision replaces the earlier observability proposal with three features:

- One ClickHouse instance, described and operated in the devops repository, with
  the schema below. The [devops handoff](observability-devops-handoff.md) gives
  the capabilities and connection information that Belay needs.
- `pytest-reportlog` enabled for every repository pytest suite.
- A small uploader, called automatically by the shared local and CI test paths.

Review-history migration, coverage, Lean proof/dependency measurements, dashboards
and automatic test selection are outside this scope. Existing review storage and
JUnit consumers continue to work.

## Current basis

The [experiments](../experiments/observability/README.md) exercised public pytest
hooks, partial results after abrupt exit, Nix result reuse and failed-build logs.
They did not validate reportlog or ClickHouse ingestion. Their broader
recommendations are historical findings, not requirements of this decision.

[`pytest-reportlog`](https://github.com/pytest-dev/pytest-reportlog) writes and
flushes a JSON object per event. Its native records include `SessionStart`,
`CollectReport`, `TestReport`, `WarningMessage` and `SessionFinish`. Test reports
carry `nodeid`, phase, outcome and duration. Preserve these records without a
custom event vocabulary or a fork of reportlog.

The shared suite factory in [`build-support/tests.nix`](../build-support/tests.nix)
sets `PYTEST_DISABLE_PLUGIN_AUTOLOAD=1`. Merely installing reportlog is insufficient.
The local environment is in [`nix/dev-shell.nix`](../nix/dev-shell.nix), and shared
pytest configuration starts at [`conftest.py`](../conftest.py).

## D1. Store executions and native events

Use database `belay_observability` with two tables and two views. The devops repo
owns deployment of this schema; this ADR defines the producer/consumer contract.

```sql
CREATE DATABASE IF NOT EXISTS belay_observability;

CREATE TABLE IF NOT EXISTS belay_observability.test_executions
(
    execution_id UUID,
    started_at DateTime64(6, 'UTC'),
    metadata String DEFAULT '{}'
)
ENGINE = ReplacingMergeTree
ORDER BY execution_id;

CREATE TABLE IF NOT EXISTS belay_observability.test_events
(
    execution_id UUID,
    event_id UUID,
    test_node_id Nullable(String),
    kind String,
    data String
)
ENGINE = ReplacingMergeTree
ORDER BY (execution_id, event_id);

CREATE VIEW IF NOT EXISTS belay_observability.test_executions_unique AS
SELECT * FROM belay_observability.test_executions FINAL;

CREATE VIEW IF NOT EXISTS belay_observability.test_events_unique AS
SELECT * FROM belay_observability.test_events FINAL;
```

`execution_id` identifies one actual pytest session. Generate it and `started_at`
when that session starts, and retain them in `execution.json` beside its
`report.jsonl`. A new run gets a new ID; retries and cached artifacts keep the
original ID and timestamp. A collection-only session has no executed test cases.

`metadata` is an optional JSON object; `{}` is valid and has no required keys.
`data` contains the complete native report object. Both are stored as JSON text
in `String` columns; the uploader validates objects and JSON-encodes these strings
inside each `JSONEachRow` row. Native ClickHouse JSON storage is not required.
Add metadata or dedicated columns only when a concrete query needs them.

Derive `event_id` as UUIDv5 with the execution UUID as namespace and the original
one-based reportlog line number, in decimal, as name. Preserve line positions
across copies and retries. `test_node_id` comes from `nodeid`, or is null when
absent. `kind` is `$report_type`. Retain unknown event kinds and additional fields.
Use native phase timestamps and durations in `data`; do not invent an event time
from the upload time. Session completion and exit status come from `SessionFinish`.

Rows are immutable observations: replay sends the same row for the same ID.
Consumers query the `_unique` views. `ReplacingMergeTree` merges alone do not
guarantee unique query results; the views apply `FINAL` before counting or joining.
Count test outcomes from their phases, not the number of event rows. A missing
call or session completion is not a passing result. Invocation/cache-request
tables and a separate source-snapshot identity are not required.

## D2. Enable reportlog in the shared pytest setup

Add reportlog to every repository pytest environment and load it explicitly where
plugin autoloading is disabled. Shared pytest setup assigns a distinct report
directory per execution and enables reporting automatically, including direct
`pytest` and `python3 -m pytest` runs using the repository configuration.

Existing `just` recipes, source checks, scheduled and mutant suites, and pytest
subprocesses that exercise repository tests use this setup. The shared Nix suite
factory includes its files and dependencies in every suite. A future test needs
only normal pytest discovery and any existing Nix suite registration. A new runner
must inherit the same setup; it must not require a list of tests to observe.

Keep local reports in a persistent spool outside version control. Nix builders
write reports as build artifacts. Generate execution identity inside the running
builder, not as a changing derivation input. Keep sandboxing and cache reuse.

Reportlog has no test-start event: an abrupt exit during setup can leave no report
for that test. Retain complete available lines and report incomplete sessions.
Do not add a custom start-event collector in this scope. Failures before pytest
initializes, or loss of the whole machine, can leave no usable report.

## D3. Upload automatically outside Nix builders

The uploader reads an execution manifest and its reportlog, wraps native events
in the schema above, and sends batches using ClickHouse's HTTP interface and
`INSERT ... FORMAT JSONEachRow`. Python's standard library is sufficient.
Insert the execution row and event rows; retain the files until all inserts are
confirmed. The two inserts need no cross-table transaction: interrupted delivery
can temporarily leave partial data, and replay completes it.

Local pytest finalization automatically attempts upload after reportlog closes.
Add a shared host-side Nix test runner that collects artifacts and attempts upload
after the build, on success or failure. Route all current Nix test recipes and CI
jobs through it. Keep credentials and network access outside builders.

For failed Nix builds, preserve the manifest and complete reportlog lines through
the framed build-log export exercised by the experiment. Extract them before
cleanup. If the whole builder is killed before export, its last records can be
lost; this MVP does not promise complete capture in that case.

Upload has a bounded overall deadline and bounded network requests. Collection
or delivery errors produce a separate diagnostic and preserve the test/build
exit status. Keep undelivered files for automatic retry on the next test command.
Do not upload a file while its producer can still append to it. A stopped
producer's unterminated final line is reported and excluded; a malformed complete
line is reported and retained for diagnosis, rather than silently discarded.

CI uses finalization that runs after failed tests too, and retains undelivered
files as artifacts. A trusted CI upload job handles runs without database
credentials, using artifacts as data and the uploader from trusted code. Scheduled
CI retries retained artifacts before their retention expires. Local direct runs
and CI need no manual upload command in the normal path. The same uploader can
also be invoked explicitly for diagnosis or replay.

Network loss after a successful insert can leave its acknowledgement uncertain.
Retry with unchanged IDs; the views prevent double counting. Reimporting cached
Nix results recovers original observations and never creates a new execution.
Do not relabel them with the retrieving machine's time or metadata.

## Acceptance

Observability is supporting code under [AGENTS.md](../AGENTS.md#goal-core-and-supporting-code)
and [R18](review-checklist.md). Keep its tests proportional to the integration we
own. R11 still requires regression tests for behavior changes; R15 excludes tests
of dependency behavior without a known or suspected problem. Every retained test
names the repository behavior it protects and has bounded subprocesses.

### Permanent regression tests

Keep a small suite that checks our shared configuration and uploader:

- Shared setup enables reporting and automatic upload, including finalization
  after failure. A small discovered-test fixture checks inheritance; configuration
  checks cover the common Nix factory and local/CI entry points.
- The uploader preserves representative native records, including unknown fields
  and empty metadata, and handles partial files and failed-build log extraction.
  It does not turn an incomplete report into a successful result. Do not maintain
  an exhaustive matrix of pytest/reportlog outcome semantics.
- Concurrent sessions get separate artifacts. Replays and cached artifacts retain
  their execution and event IDs; fresh executions get new IDs. These checks need
  small fixtures, not repeated real Nix builds.
- Network failure and uncertain acknowledgement retain files for automatic retry,
  preserve the test/build exit status and respect upload deadlines. Include our
  artifact recovery path for CI jobs without credentials. A controlled HTTP server
  can exercise uploader behavior without a live production database.

Keep one focused integration check of our uploader and schema in a disposable
database matching the deployed version. Replay the same observations and query
the `_unique` views before background merges;
counts stay unchanged, while a fresh execution increases them. Run it when the
schema or ingestion changes, not for every unrelated commit. It checks our keys,
serialization and views, not ClickHouse's general deduplication behavior.

### One-time commissioning checks

Before declaring implementation complete, record evidence that:

- Real local pytest and CI produce queryable names, phases, outcomes and durations.
  Exercise the current test routes, including scheduled/mutant jobs and failed-run
  recovery. Demonstrate automatic upload of a newly discovered parametrized test
  and a temporary suite using the shared Nix factory.
- A real fresh Nix execution and a cache hit preserve the intended identities and
  counts. Failed and interrupted runs retain available records within D2/D3's
  stated limits. Representative outcome demonstrations can use temporary fixtures;
  they do not become a permanent test suite for pytest or reportlog.
- The devops handoff verifies local/CI connectivity, permissions and persistence
  against the deployed ClickHouse version. Those are deployment checks owned by
  devops, repeated when relevant configuration changes, not Belay pytest checks.

Keep the acceptance record and remove temporary demonstration suites, targets
and deployment probes after recording their results. Permanent regression tests
remain. The earlier experiments do not satisfy these commissioning requirements.

## Cleanup and retained evidence

The custom collector and probe runners in `experiments/observability/` are research
scaffolding, not production dependencies or permanent CI checks. Do not carry the
coverage, Lean, proof-cost or review-export probes into the reduced implementation.
They currently have no production callers, so archiving them saves maintenance,
not test execution time.

When retiring the runnable experiments, retain the report, `results.json` and the
source/readers needed to reproduce the historical evidence. A pinned historical
snapshot with working reproduction instructions can hold the runnable material;
update links before removing it from the active tree. Do not leave broken replay
commands or require old probes to track new production interfaces.

Delete implementation scaffolding and replaced paths; update their callers, per R4.
Keep existing JUnit reporting, CI summaries and review tooling: this decision does
not replace them. ADR acceptance alone does not authorize their removal. Local
telemetry remains a development observation, not conformance evidence (ADR 0020).

## References

- [Reportlog implementation](https://github.com/pytest-dev/pytest-reportlog/blob/main/src/pytest_reportlog/plugin.py)
- [ClickHouse HTTP inserts](https://clickhouse.com/docs/interfaces/http)
- [ClickHouse query-time deduplication](https://clickhouse.com/resources/engineering/clickhouse-optimize-table-final)
- [ADR 0020: local build loop](adr-0020-local-build-loop.md)
