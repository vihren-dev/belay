# SELECT automation specification checkpoint

Created 2026-10-28. Status: IN PROGRESS.
Audience: team. Task: [required outcome](20261028-select-automation-spec.task.md).
ADR 0027 is reserved for this work; the ADR has not yet been written or accepted.

## Current state

- Baseline: main `3e2212ed6983f36144b7fc5bdce9b263f939e50f`, Lean 4.34.1.
- Source inspection found existing SQL weakest preconditions, `mvcgen`
  integration, `sql_run`, `sql_auto`, and expression simplification. The SELECT
  rule leaves model-coverage and universal selected-output obligations.
- Earlier consumer probes are exploratory only. They are not Nix acceptance
  evidence for this task. The consumer NOT NULL theorem uses a general table
  projection rule; broader execution adapters remain absent there.
- The disk-space gate blocked work at 8.37 GiB free. A fresh resource check now
  passes. No cleanup was performed by this task.
- Development shell initialization is being verified. No specification checks
  or implementation acceptance cases have passed yet.

## Work remaining

Experiments and source inventory; ADR and acceptance contract; formal review
views; owner decisions; focused Nix validation, independent review and the
required task-boundary checks. No production automation is implemented here.

## Open design axes

Claim syntax and success conditions; general versus automatically discharged
fragments; operator and expression coverage; schema-fact acquisition; source
contexts and correlated queries; output alternatives and row order; trusted
proof boundaries; rule selection, user hints, failure diagnostics and budgets.
