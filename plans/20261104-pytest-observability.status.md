# Automatic pytest observability status

Created: 2026-11-04. Status: IN PROGRESS.

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

## Remaining

Implement collection, upload, Nix and CI integration; validate and open the
stacked PR. Deployment matching, credentials, connectivity and live commissioning
remain with devops and are explicitly deferred.

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
  These host checks are not conformance evidence. Full required checks follow.
- Owner review replaces the agent reviewer for this work.

## Deadline correction

- Self-review found that the explicit diagnostic CLI did not share the hard
  process deadline of automatic upload. Both now use the same bounded child.
  Manifest reads are bounded before decoding, including malformed local files.
- The focused development checks are `tests/test_observability.py`; the final
  Nix integration check will validate the changed uploader against the schema.
