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
- Development shell initialization passed: Lake reports Lean 4.34.1.
- Four retained SELECT experiment tests passed in the complete Nix `surfaceS6`
  suite: 69 tests, no failures, errors or skips, 699.816 seconds.
  Report: `/nix/store/kqiwv5v55hh5g0zg1pr70b4rby9zv8hx-sqlite-verifier-test-surfaceS6-1/junit.xml`.
  These are feasibility checks, not acceptance of the proposed automation.
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

The checked fixtures are integrated from the isolated `select-experiments`
workspace into the primary working change. They use the existing surface test
harness and the Nix runtime at
`/nix/store/jh9zgilri7ckdrssni872wjrjsbadx7h-sqlite-verifier-test-surface`.
The Nix suite's declared Python includes pytest-timeout. No dependency was
installed or test timeout removed.

The experiment baseline is the pinned Lean 4.34.1 runtime and unchanged model
source `3e2212ed`. Each module has a 60-second process limit; each test has a
180-second limit. The schema and execution fixtures set recursion depth 8192.
They inherit Lean's finite heartbeat default and disable background SQL checking.
The four successful checks establish:

- `SelectAutomationCore`: universal collection cardinality and WHERE properties,
  with concrete duplicate, empty aggregate and alternative-result boundaries.
- `SelectAutomationSchema`: a universal NOT NULL projection theorem with explicit
  resolution, presence and calmness premises. Empty and populated instances
  discharge every premise. Existing `sql_auto [db.notNull]` fails first.
- `SelectAutomationSources`: nested-source certainty, ordering, NULL extension
  in joins and fault boundaries on concrete evaluator inputs.
- `SelectAutomationExecution`: branch-universal success, the raw output wrapper,
  SQL/preparation errors, continuing context, vacuity and unsupported stops.

The harness checked 23 named axiom reports (7 + 3 + 5 + 8), allowing only
`propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
Nix test times were 1.778, 3.845, 3.515 and 2.298 seconds respectively; these
include harness and elaboration work and are not tactic-cost measurements.

Source review found that a `Run` observation is not equivalent to arbitrary
branch-universal programs, that `.may` faults require readiness checks, and
that three subquery certainty conditions are distinct. The ADR now specifies
these boundaries explicitly. A 22-case automatic acceptance matrix and
constructor-level semantic coverage are proposed, not claimed as implemented.

The source map identifies existing constructors, laws and semantic traps. The
review cover links the checked Lean statements to whole execution and evaluator
views. Review finding 1 was rejected with a clarification that model windows
mean LIMIT/OFFSET, not SQL OVER. Finding 2 was fixed by removing numeric rule
priorities and explaining the shared registry's imported-library purpose.

Integrated revision `2dab0fe0` received independent Claude review
`20261029T080752Z-2dab0fe0` with no findings. The conformance verdict passed:
`/nix/store/ycpq2vi5qagfavihhv7pr4p4m0piq0wj-sqlite-verifier-verdict`, with
5,653 agreements, 2,109 unsupported observations and no other result classes.
The Nix documentation check covered all 6,065 authored declarations:
`/nix/store/qf8fll0jxlnls4v1djqznhg3z6ry2hk4-sqlite-verifier-public-documentation-1`.

`just test-nix` completed its host process checks. This records the required
workflow check, not additional proof or conformance acceptance evidence.
An initial `just test-full` run stopped because the host sandbox denied `ps`
to the existing process-cleanup test. The owner approved the unsandboxed rerun;
its source checks passed and its Nix suites are running.

Remaining: finish `just test-full` and `just test-scheduled-checks`, then owner
review of the complete cover. No production automation is implemented here.

## Open design axes

The revised proposal fixes the successful-result bridge domain, entry goal forms,
rule matching and ordering, local/global registration, replay meaning and reuse
of current public budgets. The owner review concerns these proposed interfaces
and the stated automatic coverage, not unresolved implementation prerequisites.
The new procedure's performance and the A01-A22/B01-B11 acceptance results can
only be established during implementation; this specification does not claim them.
