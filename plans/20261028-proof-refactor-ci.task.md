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

## Ownership and acceptance

Own the shared installed-layout helper, directly required build-artifact fixes,
the resolver mutant test and focused harness checks. Inspect all helper callers.
The relevant existing tests are the SQL-file/root/record/Lake-input suites,
`surface_sql_check_test.py`, `surface_sql_check_roots_test.py` and
`surface_proof_cost_report_test.py`. Resolver measurement is in
`conformance/resolve_mutants.py` and `conformance_resolve_mutants_test.py`.

Nix must execute the formerly failing installed-consumer checks through the
existing `surface` and `surfaceS6` suite owners. Confirm dependency native artifacts
replay without rebuilding and preserve the checker test's no-build assertions. Retain
one focused regression only if these existing consumers do not cover the cause.

Run the affected resolver mutant check through its existing Nix owner, retaining
per-measurement reports and all eleven mutant identities. Verify the partition
has neither missing nor duplicated mutants, through existing coverage machinery
where possible. Record local Nix evidence and the subsequent hosted Linux result
separately. Unrelated mutant families and mathematical semantics are unchanged.

Apply normal review and check cadence. Full acceptance uses the coordinator's
build slot; do not run whole mutant suites locally. No new CI service, registry,
runner or permanent artifact snapshot is required. Update this record with the
diagnosis, chosen boundary, acceptance evidence and any remaining limitations.

The proof workers own model preservation modules, comparison/lookup lemmas and
surface primitive imports. Do not edit their files. Coordinate shared build
configuration or test-suite registrations before editing; investigate on the
unmodified PR baseline so unrelated proof changes cannot explain the result.
If a repair requires a product/specification judgment, stop the dependent work
and report the evidence, options and recommendation to the owner.
