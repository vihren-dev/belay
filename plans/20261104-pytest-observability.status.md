# Automatic pytest observability status

Created: 2026-11-04. Status: DONE for repository implementation.
Deployment matching and live commissioning remain deferred by owner decision.

Task: [20261104-pytest-observability.task.md](20261104-pytest-observability.task.md).
Specification: [ADR 0028](../docs/adr-0028-development-observability.md).

## Progress

- Rebased PR #303 on current `main` (`528ea92d`) and pushed its branch. No conflicts.
- Read the common pytest, Nix suite, host recipe and CI reporting paths.
- Verified devops issue #47 with the restricted `gh-devops` command. Deployment
  information is pending; the owner authorized deferring matching and live commissioning.
- The pinned nixpkgs supplies ClickHouse 26.8.7.19-lts. Reportlog needs a pinned
  Python package definition; it is not in this nixpkgs Python package set.
- The owner authorized direnv for this workspace after the rebase.
- Task-file validation: checked links and scope against the current ADR. No
  production code changed in this commit. Review is by the owner.

## Deployment follow-up

Deployment matching, credentials, connectivity and live commissioning remain
with devops and are explicitly deferred. The implementation PR targets the
rebased #303 branch, `experiments/observability-extraction`.

## Implementation

- Added pinned pytest-reportlog 1.0.0 to the dev shell and common Nix suites.
  The shared pytest plugin creates manifests, isolates concurrent producers with
  file locks, and attempts delivery after reportlog closes.
- Added standard-library JSONEachRow upload, stable UUIDv5 event IDs, strict
  object validation, bounded requests, a hard worker deadline and retained retries.
- Added failed-builder frames and the common host runner for all five Nix test
  recipes. Successful and cached outputs import their original observations.
- CI retains observations in both test jobs. A separate workflow uses `main`'s
  uploader, read-only GitHub access and the observability environment. It handles
  completed CI runs and daily retries without executing artifact contents.
- Added the narrow cacheable `tests.observability` suite and its ownership,
  source-identity checks and developer configuration guide.
- Nix integration evidence: `/nix/store/4ygk0a8217j9ay5gxcamhlx9ds2zi9mw-sqlite-verifier-test-observability-1`.
  One test passed against ClickHouse 26.8.7.19-lts, including replay with merges
  stopped and a fresh execution. Pytest reported 0.55 seconds overall.
- Development checks exercised `test_observability.py`, `test_observability_identity.py`,
  `test_pytest_harness.py`, `test_resources.py`, `test_recipe_limits.py`,
  `test_nix_test_targets.py`, `test_test_ownership.py`, and `test_ci_workflow.py`.
  These host checks are not conformance evidence. Required check results appear below.
- Owner review replaces the agent reviewer for this work.

## Deadline correction

- Self-review found that the explicit diagnostic CLI did not share the hard
  process deadline of automatic upload. Both now use the same bounded child.
  Manifest reads are bounded before decoding, including malformed local files.
- The focused development checks are `tests/test_observability.py`; the final
  Nix integration check will validate the changed uploader against the schema.
- A second self-review correction keeps the Nix client in its caller's process
  group. GNU timeout bounds it without detaching it from an enclosing CI kill.
  The host-runner regression now verifies this process-group relationship.
- Pytest now exports the chosen spool to child processes. Copied temporary
  harnesses retain their undelivered reports in the caller's persistent spool;
  a nested real-pytest regression protects this route.
- Checklist self-review named the delivery and recovery limits (R1), kept HTTP
  status diagnostics actionable without exposing response bodies (R10), and
  checked that the guide describes the implemented paths (R13/R19). No Lean
  propositions or proofs changed, so R3 has no applicable changes.

## Acceptance

- `just test-full`, `just test-nix`, `just test-scheduled-checks` and `just verdict`
  completed successfully on the initial implementation. The full Nix output has
  1,429 passing tests; the scheduled output has 50. No mutant tables changed.
- Follow-up corrections passed focused regressions and the final cacheable
  ClickHouse check. The [acceptance record](../reports/20261104-pytest-observability/README.md)
  identifies the revisions and immutable outputs, and distinguishes broad
  initial-implementation checks from final targeted checks.
- A temporary new Nix suite demonstrated fresh/cached identity, relevant-input
  invalidation, assertion failure and abrupt-exit recovery. Its fixture was
  removed after preserving the observations. No live deployment is claimed.
- Documentation links and the SQL export's agreement with the ADR were checked.
  Owner review replaces the agent reviewer throughout this task.

## Uploader-owned schema follow-up

- The owner reports deployment without a schema and assigns schema creation to
  the uploader. The code and docs now use Belay's fixed SQL file before the
  first pending insert in a worker, within the existing request/process limits.
- Schema creation uses `IF NOT EXISTS`. It does not alter existing objects.
  Failed creation retains reports without a delivery receipt. Both automatic
  and explicit upload use this behavior.
- The existing Nix integration check now starts without the database and lets
  the uploader create it. It then stops merges and checks replay and fresh-run
  counts. Evidence: `/nix/store/kjmlswp4s87j8fx7yi344jdl179ic1ci-sqlite-verifier-test-observability-1`;
  one check passed in 0.64 seconds against ClickHouse 26.8.7.19-lts.
- Focused development checks: `tests/test_observability.py`,
  `tests/test_observability_identity.py`, and `tests/test_pytest_harness.py`.
  These cover permission-denied retention, concurrent/nested reporting and
  complete Nix inputs. Host results are not conformance evidence.
- Code follow-up: DONE. Live commissioning remains BLOCKED on connection
  details: no `BELAY_CLICKHOUSE_*` variables in this session, no issue #47
  handoff, HTTP 403 for devops repository contents, and HTTP 404 for Belay's
  environment configuration under the restricted GitHub identity. Requested
  the endpoint and credential reference from the owner; no live claim is made.
- Owner review remains the review policy. No Lean or mutant tables changed.

## Live local verification and CI environment

- Loaded the owner-provided runtime credentials without recording their values.
  After the CREATE DATABASE grant was applied, the uploader created both tables
  and both views on ClickHouse 26.5.1.882. The retained execution uploaded six
  events; replay kept unique counts at one execution and six events. A fresh
  pytest execution uploaded automatically, with all three phase reports queryable.
  This is deployment verification, not semantic conformance evidence. The
  cacheable integration pin remains 26.8.7.19-lts; version matching is pending.
- GitHub has environment `belay-observability`, restricted to branch `main`.
  Updated the workflow, its existing configuration check and the developer
  handoff to use that name. Targeted development check:
  `tests/test_observability.py::test_ci_credentials_are_separate_from_test_code`.
- CI run 41813149317 completed successfully and retained the main test and
  mutant observation artifacts. Run 41847294761 is still in progress at inspection.
- CI delivery cannot run yet: PR #308 remains open and the uploader workflow
  does not exist on `main`. Environment variables/secrets cannot be inspected
  with this VM's GitHub integration (HTTP 403). No CI delivery success is claimed.
  The expected configuration is URL and USER as variables, PASSWORD as a secret.
- Owner review remains required before merge. The environment restriction was
  left intact; no unreviewed branch received database credentials.

## Tailscale OIDC workflow follow-up (2026-11-05)

- PR #308 is merged. Production upload still needs private network access:
  commissioning run 41854390554 failed DNS resolution on the GitHub runner.
- Added the official Tailscale action pinned to v4 commit
  `064b10558093f38325e838ddea35486bdc6b1d5c`, whose default client is 1.104.4.
  The uploader requests a GitHub OIDC token, uses `TS_CLIENT_ID` and
  `TS_AUDIENCE` environment variables, and joins as `tag:belay-observability`.
  It checks the deployed host before upload and bounds setup to five minutes.
- No source filter was added, as requested by the owner. The test jobs have no
  Tailscale credentials. No custom networking code or new permanent test suite
  was added. The existing workflow boundary check covers the changed setup.
- Documentation names the exact identity, variables and TCP port 8443 required
  from devops. Live OIDC commissioning depends on that provisioning and is
  separate from repository checks. Owner review replaces the agent reviewer.

- Repository implementation: DONE. Existing workflow-boundary and documentation
  development checks: `test_ci_credentials_are_separate_from_test_code` and
  `tests/docs_test.py`. Four checks passed; these are configuration checks,
  not semantic conformance evidence or a live OIDC test.
- Created [devops issue #56](https://github.com/vihren-dev/devops/issues/56)
  using the VM's restricted `gh-devops` wrapper. The issue contains the precise
  workflow inputs, repository/owner IDs, trust restrictions, network destination,
  and handoff acceptance checks. Provisioning and live verification remain pending.
