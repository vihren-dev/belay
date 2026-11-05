# Test observations

Audience: developers. Pytest records each repository session automatically. The
report contains test node IDs (including parametrized case names), setup/call/
teardown outcomes and durations. Existing JUnit reports remain available.

Local runs retain `execution.json` and native `report.jsonl` under
`build/observability/<execution UUID>/`. Set `BELAY_OBSERVABILITY_SPOOL` to use
another persistent directory. Keep that directory outside version control.

Set these runtime environment variables using the credentials from devops:

| Variable | Meaning |
| --- | --- |
| `BELAY_CLICKHOUSE_URL` | HTTPS endpoint, without credentials or query parameters |
| `BELAY_CLICKHOUSE_USER` | Writer identity |
| `BELAY_CLICKHOUSE_PASSWORD` | Writer password |
| `BELAY_CLICKHOUSE_CA` | Optional PEM CA file for a private certificate authority |

HTTP is accepted only for loopback tests. The database is `belay_observability`.
The uploader creates its database, tables and views before sending pending
observations. Devops does not need to create the schema. The writer needs
CREATE DATABASE for `belay_observability`, CREATE TABLE and CREATE VIEW within
that database, and INSERT and SELECT on its two tables. Creation uses
`IF NOT EXISTS`; it does not change existing tables. Permission or schema errors
retain the files for retry. Do not put credentials in Nix expressions or committed shell files.

Pytest finalization tries delivery after closing the report. A missing endpoint,
network failure or interrupted acknowledgement retains observations for retry
after the next test command. Upload has a 15-second process deadline, a
three-second request timeout and a 1 MiB batch limit. An oversized row or malformed
complete line stays in the spool for diagnosis. An incomplete final line from a
stopped process is excluded with a diagnostic. A session without `SessionFinish`
is incomplete, not successful. Native reportlog does not record test-start events.

`.uploaded` marks a confirmed delivery. Delivered files remain available for
inspection and can be removed when no producer or uploader is using the spool.
Removing an undelivered directory loses its pending observations. To retry or
diagnose delivery explicitly, run `python3 -m tools.observability_upload`. To
replay a delivered observation, remove only its `.uploaded` marker first.

The `just` test recipes use the shared host Nix runner. Successful Nix outputs
contain reports; failed builders export reports through their logs. Cached
outputs retain the original execution ID and timestamp. Calling `nix-build`
directly retains successful reports in its output but does not run host delivery;
use the recipes or `python3 -m tools.observability_nix --timeout 2700 nix-build ...`.
Builders have no upload credentials or database access. If a builder dies before
its export runs, its last observations can be lost.

## CI setup

CI test jobs retain `belay-observability-*` artifacts for 14 days. The separate
`Upload test observations` workflow uses code from `main`, reads completed CI
artifacts as data, and retries retained artifacts daily in expiry order. It never
checks out or executes a pull request's code. Replays keep the same IDs.

Use the existing `belay-observability` GitHub environment, with deployment
restricted to `main`. Configure these existing GitHub environment values:

| Kind | Name | Uploader use |
| --- | --- | --- |
| Variable | `BELAY_CLICKHOUSE_INTERNAL_URL` | Runtime `BELAY_CLICKHOUSE_URL` |
| Variable | `BELAY_CLICKHOUSE_CA_PEM` | PEM CA certificate written to a temporary file |
| Variable | `BELAY_CLICKHOUSE_USER` | Runtime database user |
| Secret | `CLICKHOUSE_PASSWORD` | Runtime `BELAY_CLICKHOUSE_PASSWORD` |

The workflow writes the CA PEM to the runner's temporary directory and sets
`BELAY_CLICKHOUSE_CA` to that file. The uploader uses it for TLS certificate and
hostname verification. The file is removed when the upload step exits. Missing
URL or CA values stop the step with a configuration error. No system-wide CA
installation is needed. The existing `BELAY_CLICKHOUSE_URL` GitHub variable
remains available during migration, but this workflow reads the internal URL.

The uploader joins Tailscale with GitHub OIDC through the official action before
sending observations. It reads the existing environment secrets
`TS_OAUTH_CLIENT_ID` and `TS_AUDIENCE`. The client ID belongs to the federated
identity `tailscale_federated_identity.belay_ci` managed in devops; the input
name does not mean an OAuth client secret is required. No variable migration
is needed.

The identity needs writable `auth_keys` scope for the existing `tag:belay-ci`.
Devops provides access to Vihren DNS and shared HTTPS for the internal endpoint.
The older `.ts.net:8443` endpoint remains available during migration. OIDC trust
must match GitHub's immutable repository identity and constrain the
repository/owner IDs, environment and exact production workflow ref.
Commission on `main`; no temporary `ci-test` trust is requested.
The action checks peer connectivity, then the uploader checks database delivery.
Only the uploader job receives the network identity; test jobs retain artifacts.
The connection step has a five-minute limit. The runner is ephemeral and the
Tailscale action logs it out when the job ends.

Provisioning is tracked in [devops issue #56](https://github.com/vihren-dev/devops/issues/56).
The endpoint certificate must chain to the supplied CA and match the URL hostname. Database or network
outages do not change CI test results. Commissioning must inspect upload logs
and query ClickHouse: the workflow's success status alone does not prove delivery.

The implementation uses the ADR schema export in
`build-support/observability-schema.sql` and ClickHouse 26.8.7.19-lts from pinned
nixpkgs. Live local upload, automatic pytest delivery and replay were verified against
ClickHouse 26.5.1.882. The cacheable integration check still uses 26.8.7.19-lts;
matching that pin and live CI commissioning remain pending. CI upload requires
this workflow and its uploader code on `main`.

## Queries

Query `test_executions_unique` and `test_events_unique` to avoid counting replayed
inserts twice before ClickHouse merges them. For example:

```sql
SELECT test_node_id,
       JSONExtractString(data, 'outcome') AS outcome,
       JSONExtractFloat(data, 'duration') AS duration_seconds
FROM belay_observability.test_events_unique
WHERE kind = 'TestReport' AND JSONExtractString(data, 'when') = 'call';
```

Setup or teardown failures also affect the test result. A missing call phase is
not a passing result. `metadata` starts as an empty object; add fields when a
concrete query needs them.
