# Status: a `docs/` folder that separates user pages from internal pages

Date: 2026-11-17. Status: IN PROGRESS.
Task: [20261117-docs-folder-structure.task.md](20261117-docs-folder-structure.task.md).

## Relevant files

- `docs/`, `README.md`, `AGENTS.md`, `CONTRIBUTING.md`, `team-guide.md`
- `tests/docs_test.py`, `tools/review.py`, `tools/review_log.py`
- `experiments/observability/default.nix`, `.github/CODEOWNERS`

## Tests for each commit

`python3 -m pytest tests/docs_test.py tests/test_review.py tests/restriction_registry_test.py`

## Progress

- 2026-11-17: task and status files written.
