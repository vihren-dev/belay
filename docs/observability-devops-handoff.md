# ClickHouse request for the devops repository

Date: 2026-11-04. Status: requested capabilities; not yet provisioned.
Audience: the person managing the devops repository.

Please describe and provision one persistent ClickHouse instance for Belay's
pytest execution history. Belay will write JSONL reports locally and in CI, then
upload batches over HTTP outside Nix build sandboxes. The service records ongoing
test names, outcomes and durations. It does not run tests or collect coverage.

## Service and schema

- Manage the instance configuration, pinned stable version and schema deployment
  in the devops repository. One server is sufficient for this MVP.
- Create database `belay_observability` and the two tables and two query views
  defined in [ADR 0028, D1](adr-0028-development-observability.md#d1-store-executions-and-native-events).
  The contract uses `ReplacingMergeTree`, UUID, UTC `DateTime64`, nullable strings,
  JSON stored as strings, and views with `FINAL`. It needs no experimental types.
- Support authenticated HTTP `POST` requests with
  `INSERT ... FORMAT JSONEachRow`, and SQL reads for analysis. Synchronous batch
  inserts are sufficient; acknowledge a successful completed insert, not merely
  receipt in an in-memory queue. Preserve ClickHouse error responses through any
  reverse proxy. Support `wait_end_of_query=1` so the uploader can check completion.
- Provide persistent disk storage that survives service restart and replacement.
  Back up the database and document restoration. Monitor disk use and service
  availability through the existing devops facilities. Start without a deletion
  TTL; decide retention and capacity changes from measured growth.

## Connectivity and access

- Provide an HTTPS endpoint reachable from developer machines and the trusted CI
  uploader. A private network is suitable if both have a documented route to it.
  The endpoint need not be reachable from Nix builders.
- Provide an uploader identity with INSERT permission on the two tables, without
  schema-changing or administrative privileges. Provide a separate analysis
  identity that can SELECT the `_unique` views and their underlying tables as
  required by the view security configuration. Analysis uses the views.
- Provision local and CI credentials at runtime. Keep them out of source control,
  derivation attributes and the Nix store. Document rotation and revocation.
- Keep database credentials out of jobs that execute untrusted pull-request code.
  Such jobs retain reports; a trusted Belay CI job uploads those artifacts as data.
  Belay owns that job and its retry schedule, not the database deployment.

## Information to return to the Belay maintainer

Return the devops change link, ClickHouse version, HTTPS endpoint, database name,
authentication method, credential references, and any CA or network setup needed
on a developer machine or CI runner. State request-size and timeout limits so the
uploader can keep its batches and deadlines within them. Also give the backup
location, restore instructions, and the person responsible for the service.
Send credential references through the normal secret-management process; do not
put credential values in this document or a pull request.

## Handoff verification

These are commissioning checks owned by devops. Record their results and repeat
them when the relevant deployment configuration changes; do not add them to
Belay's ordinary pytest suite. Remove temporary deployment probes afterward.

Verify authenticated insert and read access from a developer machine and the
trusted CI uploader environment. In a disposable database with the same schema,
insert one execution and its events twice: the `_unique` views must return one
copy immediately. Confirm that an uploader cannot change the schema, that an
analysis identity cannot insert, and that data survives a server restart.

Belay owns reportlog configuration, execution IDs, report artifacts, uploader
code, automatic local/CI invocation and replay tests. No message broker, custom
ingestion service, replica cluster or dashboard is required for this handoff.
