# Restore acceptance checks needed by the proof refactor

Date: 2026-10-28. Status: IN PROGRESS.
Audience: the implementation team.
Record: [status](20261028-proof-refactor-ci.status.md).
Baseline: PR [295](https://github.com/vihren-dev/sqlite-verifier/pull/295),
commit `e8f46dae`, production packages equal main `3e2212ed`.

## Present failures

The [Linux check](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40674073648/job/122767884009)
fails while Lake builds consumers of installed Belay packages. The SQL-file,
checker and proof-cost tests share `tests/sql_file_support.py:installed_layout`.
It links package entries, including `.lake`, into read-only Nix outputs. Lake
tries to rebuild `Belay.Sqlite.Model:shared` and gets permission denied. The
reason the shared-library trace requires a rebuild remains to be diagnosed;
permission changes to the Nix store are not a repair.

The same run's [resolver mutant job](https://github.com/vihren-dev/sqlite-verifier/actions/runs/40674073648/job/122767884035)
times out in `test_every_mutant_changes_a_verdict`: 344 seconds at the 300-second
pytest limit, while mutant copies build `VerifierConformance.Classify`.
The current test measures all eleven resolver/control mutants in one test.
The existing [mutant time-limit task](20261025-query-mutant-time-limit.task.md)
describes bounded grouping after renewed hosted failures; its historical
resolver timing no longer establishes enough headroom for this revision.

Hosted run `40702241901` at repair head `16ab6ad7` passes all six resolver
measurements but exposes two further failures. The query-resolution mutant
`no_such_column` fails while compiling `Resolution/OperandArms`: the executable
classifier imports a theorem that the deliberately changed resolver invalidates.
The import path passes through `Resolution/QueryExprs`, an import-only module
that currently includes the operand equation proofs. The join-mutant measurement
also exceeds its existing 300-second test deadline. These failures extend this
task's scope as described below; they do not authorize changed SQL semantics.

Full hosted run `40742662857` at `bbd2eeac` executes the final implementation.
The Linux resolver, comparison and query-resolution measurements pass, and
the complete Linux table-mutant suite passes. The general Linux mutant suite
then reaches its 2,700-second aggregate limit after 21 of 63 tests complete.
On macOS, the arithmetic and combined write/row-write/delete measurements
reach their 300-second test limits. The model suite also reports a 15-second
Lean subprocess timeout in the unsigned oversized-hex default case for SQLite
3.46.0. Its other sign/version cases pass. These measured workload failures
extend the acceptance repair to both supported hosted platforms.

## Required behavior

Unmodified Nix-built dependencies support real Lake consumers in the installed
sibling layout used by the existing tests. Builds and checker commands work
after relocation without writing to the source Nix outputs. Preserve the actual
SQL-file loading, dependency identities, stale/missing/corrupt record diagnostics,
library selection, no-rebuild checker guarantee and proof-cost reporting.

Establish why Lake requests the shared-library rebuild before selecting the
fix. Repair the fixture or producer artifact boundary that the diagnosis
identifies. Unchanged dependency modules and shared libraries must replay without
compilation or relinking, retaining the existing
[native-artifact reuse contract](20261024-model-native-artifacts.task.md).
Making dependencies writable to permit rebuilding is not sufficient. Preserve
freshness checks, reuse existing helpers and keep the repair narrow.

All existing resolver/control mutants remain measured and must change an
authored case verdict. The unchanged model still agrees on every case used by
each measurement. Each independently scheduled measurement completes within
the existing finite test and subprocess deadlines with practical headroom on
the hosted Linux runner. Preserve exact mutant edits, guard coverage, verdict
semantics and case coverage; a timeout is a failure, never a killed mutant.
Reuse the existing measurement harness and bounded grouping patterns. No larger
timeout, automatic retry, skipped mutant or weaker assertion is authorized.

The executable classification path must compile deliberately changed operand
resolution without importing its equation-proof modules. Keep those proofs,
their statements, attributes and checked documentation available to their real
proof consumers through explicit imports. Preserve executable definitions and
the unchanged-model classification. A compilation failure must remain a test
failure; it cannot count as a detected semantic mutant.

The existing six query-resolution mutants and 22 join mutants must all build
and change the verdict of their existing target cases. The join tables name
20 distinct target cases. Split the join workload into bounded
measurements if needed, preserving the complete mutant/target mapping, native
records, unchanged-model agreement and finite deadlines. Reuse the existing
measurement helper. No new harness or scheduling framework is part of this repair.

Every existing mutant measurement must have exactly one scheduled owner, and
every mutant, target case, native observation and guard must remain covered.
The aggregate general-mutant workload must fit its existing suite limit on
both hosted platforms. Use the existing Nix suite ownership and CI matrix to
bound the work assigned to each job. Arithmetic and write measurements must
also fit their unchanged per-test limit, including setup and cleanup. Keep
the 300-second test, 2,700-second mutant-suite, subprocess and hosted-job
deadlines unchanged. Do not replace detection with compilation failure, skip
work, add automatic retries or introduce a scheduler or another runner type.

The oversized-hex default test must compare the same prepare phase and error
message for both signs and SQLite 3.51.0/3.46.0 within the existing 15-second
Lean subprocess limit. The generated fixture imports only the dependencies
it uses. Its result contains only strings; the
neighboring default-value test serializes model values and has different
codec requirements. Preserve that neighbor and the shared check helper's
timeout, compiler invocation and trust assertions. No SQL semantics change
is authorized.

## Ownership and acceptance

Own the shared installed-layout helper, directly required build-artifact fixes,
the resolver mutant test and focused harness checks. Inspect all helper callers.
The relevant existing tests are the SQL-file/root/record/Lake-input suites,
`surface_sql_check_test.py`, `surface_sql_check_roots_test.py` and
`surface_proof_cost_report_test.py`. Resolver measurement is in
`conformance/resolve_mutants.py` and `conformance_resolve_mutants_test.py`.
The extended scope includes `Resolution/QueryExprs`, direct imports needed by
operand-equation proof consumers, and the join measurement in
`tests/conformance_table_mutants_test.py`. Query-resolution measurement remains
in `tests/conformance_query_mutants_test.py`. Keep executable and proof bodies
unchanged when repairing the import boundary.

The full-run follow-up also owns the affected arithmetic/write measurements,
`tests/nix_suites.json`, the existing scheduled/mutant inventories, their Nix
definitions and CI matrix, and existing routing/ownership checks. The separate
default-fixture work owns only `tests/column_default_value_test.py`. These two
work surfaces can proceed in isolated workspaces; coordinate Nix execution.

Nix must execute the formerly failing installed-consumer checks through the
existing `surface` and `surfaceS6` suite owners. Confirm dependency native artifacts
replay without rebuilding and preserve the checker test's no-build assertions. Retain
one focused regression only if these existing consumers do not cover the cause.

Run the affected resolver mutant check through its existing Nix owner, retaining
per-measurement reports and all eleven mutant identities. Verify the partition
has neither missing nor duplicated mutants, through existing coverage machinery
where possible. Record local Nix evidence and the subsequent hosted Linux result
separately. Mutant definitions and mathematical semantics are unchanged.

Also run the existing query-resolution measurement and every resulting join
measurement through their current Nix owners. Verify that the union of groups
retains each original mutant and each original target mapping exactly once.
Record actual durations and the subsequent hosted result separately. Complete
package compilation, checked documentation and the existing full acceptance
must cover the explicit proof imports. Use the coordinator's shared acceptance
slot; no whole mutant suite is run locally.

For the full-run follow-up, existing inventory/routing checks must establish
complete, non-overlapping ownership. Focused Nix measurements cover each
changed group and the full sign/version default fixture, with the normal
runtime inputs and unchanged limits. Retain concrete durations and compare
them with actual hosted measurements. Successful execution of every scheduled
mutant suite and the model suite on both hosted platforms is the completion
gate. A partial log before an aggregate timeout establishes only the named
completed measurements, not suite success. Reuse existing tests; temporary
partition and timing audits are acceptance evidence, not new permanent gates.

Apply normal review and check cadence. Full acceptance uses the coordinator's
build slot; do not run whole mutant suites locally. No new CI service, registry,
runner implementation or permanent artifact snapshot is required. Update this record with the
diagnosis, chosen boundary, acceptance evidence and any remaining limitations.

The proof workers own model preservation modules, comparison/lookup lemmas and
surface primitive imports. Do not edit their files. Coordinate shared build
configuration or test-suite registrations before editing; investigate on the
unmodified PR baseline so unrelated proof changes cannot explain the result.
If a repair requires a product/specification judgment, stop the dependent work
and report the evidence, options and recommendation to the owner.
