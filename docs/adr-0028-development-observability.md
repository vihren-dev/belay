# ADR 0028: Continuous development observability

Date: 2026-11-02. Status: PROPOSED. Implementation has not started.
Audience: designers and reviewers.
Owner request: retain review statistics outside the repository and continuously
measure test-suite growth, overlap and unnecessary execution, locally and in CI.
The owner requested extraction experiments and requires ordinary tool interfaces
rather than compiler patches, private protocols or elaborate interception.
Storage proposal: one self-hosted ClickHouse server, as discussed with the owner.
Evidence: [experiment report](../experiments/observability/README.md) and
[captured summaries](../experiments/observability/results.json).
Related: [ADR 0010](adr-0010-lake-builds-and-artifact-cache.md),
[ADR 0011](adr-0011-product-trust-and-development-integrity.md), and
[ADR 0020](adr-0020-local-build-loop.md).

## Problem and measured limits

Review history grows in `reviews/`; removing it without preserving findings,
resolutions and checklist versions would lose the evidence used to improve the
review process. The experiment round-tripped 3,580 records, about 3.2 MB of JSONL,
without changing the statistics. Existing records lack duration and model version.

The owner suspects overlapping tests and runs after unrelated changes. The
experiments establish extraction mechanisms, not the amount of wasted work:

| Observation | Consequence |
| --- | --- |
| Public pytest hooks expose collection, selection, starts and phase results; ten existing tooling tests agree with JUnit. | Use a small explicit plugin for every configured pytest run. |
| An abrupt process exit preserves partial events but produces no JUnit file. | Keep incomplete attempts; absence of a result is not a pass. |
| Python contexts work with `core = ctrace` on the measured pin; subprocess lines lack the parent test context. | Use periodic parent-process coverage and retain unattributed execution. |
| Lean exposes diagnostics, module imports and elaboration profiles. Existing exporters expose proof dependencies and optional proof-body costs. | Retain these signals with their measured meaning. They are not runtime path coverage. |
| Lake reuses an unchanged build but invalidates on an imported module change, including an unused declaration. | Measure conservative build dependencies before proposing narrower checks. |
| Fresh and reused Nix builds return the same build JSON; cached events retain their original execution ID. | Separate invocations from executions. |
| Failed Nix outputs can exist without being valid store paths; framed test records survive in build logs. | Recover our log records; do not scan failed output directories. |

CI identities were tested with fixture environment variables, not a live Actions
job. The probes did not measure production overhead, distributed pytest workers,
retry plugins, macOS, ClickHouse ingestion or deployment reliability. The decisions
below specify that remaining integration work; they do not claim it is implemented.

## D1. Store observations independently of builds

Use one ClickHouse database for structured development observations. Producers
write versioned JSONL bundles first. A small importer validates and inserts them
in batches through ClickHouse's documented HTTP interface. No message broker,
custom ingestion service or general tracing platform is required initially.

Local commands write to a per-user spool outside the checkout, with separate
files for concurrent processes. A local uploader sends completed bundles when
the configured server is reachable. CI retains the same bundles as Actions
artifacts, including after test failure. An importer on the ClickHouse host pulls
those artifacts with read credentials; hosted runners do not need access to the
private database. Both routes use the same schema and import code.

Nix builders write files and framed log records only. They receive no database
address, uploader credential or network dependency. CI/local invocation IDs and
timestamps stay outside derivation inputs. Actual execution IDs are generated
inside the process that runs the tests, so cached outputs preserve their origin.

Transport is retryable and at least once. Assign each observation a stable ID
before its first write; retry the same ID and payload. Reject a conflicting
payload for an existing ID. Preserve a bundle until insertion is confirmed;
an ambiguous response is retried. Published queries must deduplicate by logical
ID before counting, including before background merges have run. A
`ReplacingMergeTree` table alone does not guarantee duplicate-free query results;
use a view with explicit query-time deduplication. Do not build additive
materialized aggregates directly from retryable inserts.

Telemetry failure leaves test/build exit codes unchanged. Report collection and
upload failures separately. A deployment must set a spool byte limit; when full,
stop recording new telemetry and report the gap instead of deleting unacknowledged
records silently. Missing or malformed bundles remain visibly incomplete. Closing
an append preserves events across the measured process exit, not a machine failure.

## D2. Keep identity, scope and completeness in every analysis

Every bundle has schema and producer versions, repository identity, observation
time, producer origin and a completeness state. Use these logical records; the
implementation can choose tables without changing their meaning:

| Record | Required identity and meaning |
| --- | --- |
| Invocation | UUID; actual checked-out commit and jj change ID when available; dirty/source snapshot identity; command/selection; CI run, attempt, job and platform or local origin; start/end and outer elapsed time. |
| Test execution | Execution UUID, producer version, test inventory and runtime/build identities. One real pytest session, not one retrieval of its reports. |
| Test attempt and events | Execution, pytest node ID including parameters, attempt ordinal and worker identity where applicable; ordered event IDs, setup/call/teardown times, outcomes, skip/xfail information and incomplete state. |
| Invocation references | Invocation to artifact/execution references. Repeated retrieval adds a reference, not another test execution. |
| Review event | Stable record ID, original review/finding IDs, commit, reviewer, checklist versions, finding and resolution payloads; duration/model identity only when supplied by the producer. |
| Snapshot | Content identity, source/runtime/tool versions, measured scope and completeness; dependency edges, coverage memberships or semantic links. |

Use an explicit allowlist for CI/environment metadata. Credentials and a complete
environment dump are never part of an observation.

Record timestamps for correlation and monotonic elapsed time for durations. Keep
CI and local runs separate by default, and compare timings within platform,
runner class, toolchain, execution mode and instrumentation mode. Store both
invocation source identity and the source identity that produced a cached artifact.
A mutable jj change ID is not a content identity. A partial inventory is not the
full suite; a renamed node ID is a new identity unless an explicit mapping exists.

First seeing an execution ID does not establish that the current machine ran it:
it may arrive from a binary cache. Store attribution as observed execution,
reused known execution, or unknown, with the evidence for the label. Nix build
JSON alone supplies no exact local-build/substitution timeline. Parse documented
JSON with an explicit version check; Nix's new CLI remains experimental upstream.

The initial pytest integration supports ordinary single-process runs. It must
detect unsupported worker/retry configurations and report incomplete attribution,
not merge attempts under one key. Supporting such configurations requires a
separate integration test. Pytest cannot identify semantic cases hidden in loops;
case-level counts are available only where an existing harness emits case IDs.

## D3. Collect inexpensive records continuously

| Signal | Collection point and cadence |
| --- | --- |
| Review findings and resolutions | Existing review commands, every invocation; add elapsed time and reported model version prospectively. |
| Pytest inventory, selection and phase results | Documented hooks in local and CI pytest configuration, every run, with JUnit retained for ordinary tooling. |
| Invocation and selection context | Existing recipes/CI router, every configured invocation; explicit requested, scheduled or scope-rule reason, otherwise unknown. |
| Nix artifacts and dependencies | Documented derivation/store queries when an artifact identity is first observed; record references on every invocation. |
| Lean diagnostics and dependencies | Existing compilation/report commands; refresh snapshots when source/artifact/tool identities change. Reuse the theorem exporter. |
| Existing proof costs | Import existing fresh reports when available, once per artifact identity. Preserve heartbeat unit, scheme and stale status. |
| Semantic and mutant links | Export existing tags/target mappings when inputs change; export observed mutant results from already scheduled mutation runs. |

Explicit pytest configuration covers direct pytest use in the configured
environment as well as recipes. Ordinary Lean/build timing covers commands routed
through the project entry points. Arbitrary external commands are outside the
collection boundary and must not be represented as observed runs.

Start and completion events distinguish deselection, runtime skips, setup errors,
ordinary failures and incomplete attempts. Retain collection errors and the outer
process exit too. Forward our framed events to Nix builder logs and recover them
through `nix log` after failure. The probe forwards after pytest returns; full
builder cancellation can still lose those records. Report that limit until a
bounded streaming integration is verified. Never inspect private daemon events.

The mutation probe only exported five static target/guard mappings. Source
inspection found `conformance.resolve_mutants.measure` already returns `killed`
and case-level changed verdicts for the cases it executes. Retain that result and
the selected-case set at `tests.mutant_sets.measure_set`; it is not an all-pairs
test/mutant matrix. Unexecuted pairs remain unknown. The 17 sampled authored JSON
cases had no requirement tags; do not manufacture requirement coverage from them.

## D4. Use coverage as periodic, bounded evidence

Collect Python line membership by test with pytest-cov contexts on one weekly
representative full run and on explicit requests. Use the documented `ctrace`
core for the measured Python 3.14 pin. Preserve empty/shared contexts and mark
subprocess lines unattributed. Record included tests, files, source hashes,
configuration and tool versions; compare overlap only within compatible snapshots.
Keep this instrumentation mode separate from ordinary timing trends.

Use Lean module/declaration dependencies for impact exploration. Use native Lean
profiles on request for elaboration-cost investigations. Keep the existing proof
cost collector opt-in; do not broaden its compiler interception for observability.
Its heartbeats exclude statement elaboration and kernel checking. Importing a
compiled theorem or rereading its costs is not a new proof-checking execution.

Do not add Lean source rewriting, compiler instrumentation, subprocess context
monkey-patching or private Nix protocol parsing. No experiment established a
supported per-test Lean runtime coverage collector. No coverage percentage,
shared footprint or dependency graph authorizes skipping or deleting tests.
Future test selection needs a separate decision and validation against full runs;
the current required checks and judge remain unchanged.

## D5. Move review history without losing its meaning

Keep checklist definitions and their versions in the repository. Preserve full
review and resolution payloads in ClickHouse, including original IDs and the
existing deterministic ordering: date, review before resolution at the same
second, then original record path. Historical duration and model fields stay
unknown. New record IDs must be safe under concurrent workspaces.

Before switching writers, export all tracked records, verify count/content
identity and existing `review-stats` output against the imported data, and restore
a backup to verify recovery. Then switch review writers/readers and update
`AGENTS.md`, CI record checks and command documentation together. New history goes
to the spool/database; remove the tracked archive from the current tree after
verification. Preserve old commits. Keep the historical import reader for replay,
not a second ongoing repository writer.

Resolution commands must still validate the referenced finding. They can use a
cached record plus local pending events when offline; if the finding is unavailable,
report that validation cannot finish. Database unavailability must not silently
drop a review or turn missing history into an empty successful statistics report.

This ADR is proposed. Until its implementation replaces the workflow, the current
`AGENTS.md` requirement to commit review records still applies.

## D6. Retain enough history for continuing decisions

Proposed initial retention is one year for detailed execution/invocation records,
90 days for coverage/dependency snapshot payloads, and two years for daily trend
summaries. Retain review history without an automatic expiry. Keep small snapshot
identities and expiry markers as long as referencing records. On-demand native
profiles remain ordinary diagnostic artifacts; they are not routinely imported.
Expired detail means unavailable, not zero coverage. Compute summaries from
deduplicated records before deleting detail and state their sample counts.

These are initial policy choices, not measured storage requirements. Measure
compressed bytes per record/snapshot, daily volume, ingestion lag and spool size
during the first two weeks. Forecast retained size from measured daily volumes
and retention, with separate headroom for merges and backups. Back up the database
to a different failure domain and verify restore before removing repository history.
Deployment must select the server version, endpoint, credentials, disk budget and
backup destination. None of these was tested by the extraction experiments.

Publish a weekly SQL-based report, with links to the underlying observations:

- Suite growth: collected and selected counts, new/removed identities, run
  frequency, failures and incomplete attempts.
- Cost: total observed test time, invocation wall time, comparable per-test
  duration distributions and retry cost when attribution is supported. Summed
  test time is not CI wall time when work runs concurrently.
- Potential waste: repeated executions of unchanged inputs, broad dependency
  invalidation and Python footprint overlap. Label these candidates, not proof
  that tests are redundant. Preserve unique failures and mutant detections.
- Review process: findings and resolutions by checklist version, acceptance and
  rejection rates, unresolved age and duration where known. Include review/rule
  opportunities so a rule with no findings is not mistaken for an unused rule.
- Collection health: missing bundles, upload lag, rejected schemas, duplicate
  deliveries, incomplete coverage, retained bytes and expired detail.

Local observations help explain development cost. They do not become the trusted
conformance evidence of ADR 0011 or replace Nix checks under ADR 0020. The database
is an analysis store, not a source of correctness verdicts or a new merge gate.

## Acceptance of the later implementation

End-to-end checks must exercise local and CI bundle collection, offline replay,
duplicate delivery, conflicting IDs, concurrent producers and database recovery.
Replaying a cached Nix artifact must add no fresh test executions. Failure and
termination fixtures must retain partial records without inventing completion;
unsupported attribution must remain explicit. Review import and restored data
must reproduce existing statistics, including resolution ordering ties.

Reuse the experimental fixtures for correct Python contexts and Lean data scope.
Verify weekly queries with known duplicates, expired snapshots and partial
inventories. Measure collection overhead on representative project runs before
enabling it by default; record the measured budget and result in the implementation
task. Test ingestion against the chosen ClickHouse version and CI artifact path.
This ADR does not prescribe SQL DDL, a dashboard framework or deployment steps.

## Alternatives and references

Keeping review history in Git does not address the owner's accumulation problem.
JUnit alone loses the measured abrupt-exit case and selection history. Always-on
coverage adds unmeasured cost and still does not cover Lean paths. A custom compiler
or daemon integration violates the owner's maintenance constraint. A larger
telemetry platform is unnecessary for the measured extraction points.

Tool-interface references are collected in the experiment report. Storage choices
use ClickHouse's documented [HTTP interface](https://clickhouse.com/docs/interfaces/http),
[ReplacingMergeTree semantics](https://clickhouse.com/docs/engines/table-engines/mergetree-family/replacingmergetree)
and [backup/restore facilities](https://clickhouse.com/docs/operations/backup).
