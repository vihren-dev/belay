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
