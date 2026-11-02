# Observability extraction experiment status

Status: OPEN. Created 2026-11-02. Audience: the team.

Task: [observability extraction](20261102-observability-extraction.task.md).
Workspace: `/home/codex/work/sqlite-verifier-observability` (`observability-experiments`).
Base: `187ea5104e7a1ae64477fc46b8e0e4743da27ae4` (`main` at creation).

## Progress

- Created the dedicated workspace. The owner approved `direnv allow` on 2026-11-02.
- Inspected the current collection points named in the task. The base contains
  the theorem-dependency exporter; reuse it rather than creating another exporter.
- Defined bounded experiments and the owner's supported-interface constraint.
- Experiment results, acceptance checks and extraction recommendations are pending.

## References

- `experiments/observability/` will contain the explicit probes and report.
- `build-support/theorem-dependencies.nix` and `tools/theorem_dependencies.py`:
  existing declaration export.
- `tools/review_records.py`, `tools/review_stats.py`: review export and statistics.
- `build-support/tests.nix`, `tools/test_reports.py`: test results and reuse.
- ADR 0011 and ADR 0020: distinguish local observations from Nix evidence.

## Checks

No implementation changes or experiment claims yet. Specification review pending.
