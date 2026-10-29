# SELECT automation specification checkpoint

Created 2026-10-28. Status: IN PROGRESS.
Audience: team. Task: [required outcome](20261028-select-automation-spec.task.md).
The owner explicitly requested number ADR 27 for this work. The
[ADR draft](../docs/adr-0027-compositional-select-proofs.md) and
[acceptance draft](../docs/select-automation-acceptance.md) are not yet accepted;
gaps in earlier ADR numbers do not change that request.

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
- Development shell initialization passed: Lake reports Lean 4.34.1. No specification checks
  or implementation acceptance cases have passed yet.
- Planning commit `1783df21` received independent review with no must findings.
  Its two should findings concern the owner-selected ADR number and the
  owner-local location of earlier consumer probes; both are clarified here.

## Installed checker fix (2026-10-29)

The experiment run exposed six failures in the existing SQL-file checker tests.
Both Nix environments set `MACOSX_DEPLOYMENT_TARGET=14.0`, but
`tests/sql_file_support.py::toolchain_environment` discarded it. Lake then used
`99.0`, invalidated the executable trace and tried to rebuild the checker in
the read-only Nix store.

The owner authorized a small fix with no unnecessary new tests. The helper now
preserves the deployment target when present. No test cases or Nix
configuration were added.

Focused Nix validation passed for all seven caller test modules. A temporary
`PYTEST_ADDOPTS` override selected existing tests, with the declared sources,
runtime, sandbox and timeouts unchanged:

- `surface`: 24 passed, 354 deselected, in `surface_sql_files_test.py`,
  `surface_sql_file_root_test.py`, `surface_sql_records_test.py`,
  `surface_sql_lake_inputs_test.py` and `surface_proof_cost_report_test.py`.
  Report: `/nix/store/k4bhqv5cxr63nl9z8p14cdy7vyvy2dpm-sqlite-verifier-test-surface-1/junit.xml`.
- `surfaceS6`: six passed, 59 deselected, in `surface_sql_check_test.py` and
  `surface_sql_check_roots_test.py`.
  Report: `/nix/store/s5ypavrppr9ch6njrrf74n8aar93rbz4-sqlite-verifier-test-surfaceS6-1/junit.xml`.

Fix status: DONE in commit `8a2b159a`. Independent Claude review
`20261029T074907Z-8a2b159a` returned no findings.

## Work remaining

The owner selected Lean-only specification artifacts after PIDE startup found
no compatible HOL heap. The unchecked Isabelle files were removed; no Isabelle
build or PDF is required. The Lean fixtures and written semantic review cover
are the target-specific formal specification artifacts for this task.

The isolated `select-experiments` workspace contains bounded fixtures in the
existing surface test harness. Its Nix runtime build completed at
`/nix/store/jh9zgilri7ckdrssni872wjrjsbadx7h-sqlite-verifier-test-surface`.
This is build evidence only, not evidence that the new experiments passed.
The host Python lacks pytest-timeout; tests use the Nix suite's declared Python,
which includes it. No dependency was installed or test timeout removed.

Source review found that a `Run` observation is not equivalent to arbitrary
branch-universal programs, that `.may` faults require readiness checks, and
that three subquery certainty conditions are distinct. The ADR now specifies
these boundaries explicitly. A 22-case automatic acceptance matrix and
constructor-level semantic coverage are proposed, not claimed as implemented.

Experiments and source inventory; ADR and acceptance contract; formal review
views; owner decisions; focused Nix validation, independent review and the
required task-boundary checks. No production automation is implemented here.

## Open design axes

Claim syntax and success conditions; general versus automatically discharged
fragments; operator and expression coverage; schema-fact acquisition; source
contexts and correlated queries; output alternatives and row order; trusted
proof boundaries; rule selection, user hints, failure diagnostics and budgets.
