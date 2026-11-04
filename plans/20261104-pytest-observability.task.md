# Automatic pytest observability

Created: 2026-11-04. Status: DONE for repository implementation.
Deployment matching and live commissioning are deferred by the owner as recorded below.

Implement [ADR 0028](../docs/adr-0028-development-observability.md) in a PR
stacked on #303. Every repository pytest session produces native reportlog
events and an immutable execution manifest. Local finalization and the shared
host Nix runner attempt bounded delivery and retry retained observations.
Failures preserve the test status. Cached results retain their original IDs.
CI retains undelivered observations and a trusted job uploads artifacts as data,
including observations from untrusted pull requests and scheduled retries.

Keep two tables and two FINAL views. Metadata is an optional JSON object. Do
not add coverage, review migration, dashboards or test selection.

## Acceptance

Small permanent regression tests exercise shared pytest setup, failure
finalization, concurrent artifact isolation, immutable replay IDs, native and
unknown records, partial and malformed reports, failed-builder log recovery,
bounded HTTP failure and uncertain acknowledgement, and trusted CI recovery.
Tests use representative fixtures rather than a matrix of dependency behavior.

One separate Nix suite runs the uploader against a disposable pinned ClickHouse
and verifies immediate unique-view counts on replay and fresh execution. The
source-identity checks verify that relevant inputs invalidate that derivation
and unrelated Lean changes do not. Existing host ownership excludes this suite.
All subprocesses and service lifetimes have limits.

Run the repository's applicable Nix checks before the implementation PR. Record
fresh/cached and failed Nix recovery demonstrations. Remove temporary probes
after recording results; preserve the historical experiments and their readers.

## Constraints and owner decisions

The shared setup is `conftest.py`; `build-support/tests.nix` disables plugin
autoloading. `nix/dev-shell.nix` supplies local and CI Python dependencies.
`justfile` and `tools/ci_checks.py` route local/CI commands. Keep existing JUnit
reports and summaries. The `tests/nix_suites.json` ownership registry must
include the integration check. Credentials must never enter derivations or
untrusted CI jobs. Report upload cannot change test results.

On 2026-11-04 the owner authorized implementation with the ADR schema and a
pinned local ClickHouse version, with deployment matching and live commissioning
deferred. Devops issue vihren-dev/devops#47 is open with no handoff. Do not claim
live deployment acceptance. The owner reviews this work, as instructed in this
conversation; do not invoke the agent reviewer.

## Schema ownership follow-up

The owner reports that ClickHouse is deployed without a schema. The uploader
must create the versioned database, tables and views before inserting pending
observations. Creation is repeatable and uses existing request deadlines and
failure retention. The existing cacheable integration check starts with no
database and verifies creation and replay. A denied creation must retain files
without a delivery receipt. Verify live delivery when connection details are
available; this session has no endpoint or credentials configured.
