# ADR 0028: Continuous development observability MVP

Date: 2026-11-02. Status: PROPOSED. Implementation has not started.
Changed 2026-11-03 at the owner's request: narrow the proposal to an MVP,
use optional JSON invocation metadata and leave the remaining schema open.
This replaces the broader collection, retention and reporting proposal of
2026-11-02. The owner will continue reviewing the tables one by one.
Audience: designers and reviewers.
Owner request: retain review statistics outside the repository and continuously
record test executions and durations, locally and in CI. The longer-term questions
are suite growth, overlap and unnecessary execution. The owner requires ordinary
tool interfaces and a schema that grows only when an actual need arises.
Evidence: [experiment report](../experiments/observability/README.md) and
[captured summaries](../experiments/observability/results.json).
Related: [ADR 0010](adr-0010-lake-builds-and-artifact-cache.md),
[ADR 0011](adr-0011-product-trust-and-development-integrity.md), and
[ADR 0020](adr-0020-local-build-loop.md).

## Problem and measured basis

Review history grows in `reviews/`. We need to stop that accumulation while
preserving the findings, resolutions and checklist versions used by the existing
statistics. The experiment round-tripped 3,580 records, about 3.2 MB of JSONL,
without changing the statistics.

Public pytest hooks expose test identities, selection, starts, phase durations
and outcomes. Ten existing tooling tests produced completion events that agreed
with JUnit. An abrupt exit retained partial events but produced no JUnit file.
Cached Nix results retained the original execution ID; fresh and reused builds
returned the same build JSON. Our framed records survived in failed-build logs.
These observations support a small collector and importer.

The experiments did not test ClickHouse installation or ingestion, live CI
collection, distributed pytest workers or retry plugins. The MVP still needs
those integrations that its scope uses. Broader experiment recommendations are
possible extensions, not additional MVP requirements.

## D1. Collect reviews and test executions

The MVP captures existing review and resolution records, plus pytest execution
events with test identities, durations and outcomes. Collection runs continuously
in local development and CI through the configured pytest environment and project
entry points. Keep JUnit for existing consumers. Use pytest's documented hooks
and the existing review commands; do not build a general tracing framework.

Retain starts and available phase results so failures and partial runs remain
visible. Use the existing JSONL/log approach for failed Nix test builds. The probe
forwards events after pytest returns; killing the entire builder before that can
lose records. The MVP must state this limit rather than claim complete capture.
It does not promise observation of arbitrary commands outside the configured
entry points or semantic cases hidden inside a Python test's loop.

Python coverage, dependency snapshots, Lean diagnostics/profiles/proof costs,
mutation results and requirement links are deferred. They are not prerequisites
for the MVP. Keep their experimental findings for a later decision driven by a
specific analytical question. Test selection and removal remain unchanged.

## D2. Start with an intentionally incomplete schema

Invocation metadata is a generic JSON object named `metadata`. An empty object
`{}` is valid. There are no required metadata keys initially. The earlier list of
command, revision, selection, selection reason, CI identifiers and environment
columns is withdrawn; these can become optional metadata keys when needed.
Do not populate them merely because the producer can obtain them.

Keep only the identity and lifecycle fields needed to link observations and
interpret execution results as dedicated fields. Their exact definitions, and
the remaining tables, stay open for the owner's table-by-table review. This ADR
does not approve the earlier full table layout or prescribe ClickHouse DDL.

Add a metadata key when a concrete query needs it. Add or promote a dedicated
column when querying or validating that data warrants it. Older records can lack
the new key; absence means unknown, not a default value inferred after the fact.
No backfill or general schema-migration framework is required for optional keys.
Metadata must not contain credentials or a complete environment dump.

A separate `source_snapshot_id` and `dirty` field are not required for this
jj-based MVP. If source identity is later collected, the full working-copy
commit ID captured by jj before the command can be optional metadata. A jj change
ID does not identify immutable contents. Files can still change during a local
run, and ignored/generated files or runtime artifacts are not identified by that
commit alone; an extra snapshot hash would not solve those execution boundaries.

An invocation requests work; an execution actually runs tests. Preserve this
semantic distinction without requiring a particular table arrangement. Missing
metadata limits comparisons: for example, we cannot assume two durations came
from comparable environments when those environments were not recorded.

## D3. Deliver files to one ClickHouse database

Use one self-hosted ClickHouse server. Producers write JSONL files, and a small
import command inserts batches through its documented HTTP interface. Local
files outside the checkout and CI artifacts provide buffering and replay. Use
simple scheduled import invocations for continuing collection. Hosted CI can
publish artifacts for the ClickHouse host to retrieve, so it need not reach the
private database. No custom ingestion service or message broker is required.

Nix builders write files and our framed log records only. Keep uploader credentials
and network access outside builders. Invocation IDs and timestamps must not enter
derivation inputs and invalidate caches. Generate execution identity when the
tests actually run, and preserve it when their artifact is retrieved.

Keep these correctness requirements in the MVP:

- Reimporting the same observations must not double-count them. Preserve stable
  observation identities across replay and make published queries deduplicate
  before counting; background table merges alone are insufficient.
- Retrieving cached test results must not count as another execution. First seeing
  an execution ID is not proof that the current machine ran it.
- Missing completion must not become a passing result. Keep available partial
  results and report collection failures without inventing a termination cause.
- Collection or upload failure must not change the test/build result. Keep files
  for retry until import is confirmed, and report delivery failures separately.

The MVP implementation must choose a working server version, endpoint and access
configuration. This ADR does not require a full deployment framework, dashboards,
fixed retention periods, daily aggregates or a catalogue of weekly reports.
Measure storage growth before choosing retention policies; do not enable automatic
expiry merely to fill in the previously proposed retention table.

## D4. Move review history with a narrow migration check

Preserve existing review/resolution payloads, original IDs and checklist versions.
Preserve the reader's ordering: date, review before resolution at the same second,
then original record path. Historical fields not present in the records stay
unknown. Additional duration or model metadata is deferred until needed.

Export the tracked records and import them into ClickHouse. Verify record content
and counts, and reproduce existing `review-stats` output before stopping repository
writes. Retain the original export outside the checkout for recovery. Then update
writers, readers, CI record checks, command documentation and `AGENTS.md` together;
remove the tracked archive from the current tree while preserving old commits.
Keep the historical import reader for replay, not a second ongoing writer.

Resolution commands must still validate their referenced finding. If that record
is unavailable, report that validation cannot finish. Missing database access
must not silently drop a review or produce an empty successful statistics report.
The current instruction to commit review records applies until implementation
replaces it. Updating this proposed ADR does not change the current workflow.

## MVP acceptance and deferred work

The MVP succeeds when we can query historical reviews and actual test executions
from local development and CI, including test durations and outcomes, without
accumulating new review records in the repository.

Verify that outcome with a local run, a CI run, review-history import with matching
statistics, and replay of the same import. Include failed and interrupted test
runs, collection/upload failure, and reuse of a cached test artifact to check the
four correctness requirements in D3. An invocation with `metadata: {}` must work.
Use bounded integration checks for our collector and importer, rather than a broad
acceptance matrix for deferred features.

Detailed table definitions remain under discussion. Retention schedules,
automatic aggregates/reports, advanced delivery mechanisms and the additional
signals in the experiment report require a concrete need before entering scope.
The MVP supplies execution history; it does not establish test redundancy or a
safe mechanism for skipping Lean tests. Local observations remain development
telemetry, not the trusted conformance evidence of ADR 0011 or a replacement for
the Nix checks of ADR 0020.

## References

The experiment report links the extraction interfaces and records their limits.
ClickHouse documents its [HTTP interface](https://clickhouse.com/docs/interfaces/http)
and [ReplacingMergeTree deduplication semantics](https://clickhouse.com/docs/engines/table-engines/mergetree-family/replacingmergetree).
