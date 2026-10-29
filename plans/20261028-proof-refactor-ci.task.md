# Restore acceptance checks needed by the proof refactor

Date: 2026-10-28. Status: DONE (2026-10-29).
Audience: the implementation team.
Record: [status](20261028-proof-refactor-ci.status.md).
Baseline: PR [295](https://github.com/vihren-dev/sqlite-verifier/pull/295),
commit `e8f46dae`, production packages equal main `3e2212ed`.

## Completion decision, 2026-10-29

The owner accepted completion after the local and Linux acceptance passed:
“I'll merge. We'll fix any issues if they arise. We can consider the goal
finished.” This accepts the current repair review and defers macOS validation.
For closing this task, that explicit decision supersedes the both-platform
acceptance and further owner-review gates recorded below. macOS remains
unverified; it is not recorded as passed. The earlier requirements and failure
history are retained as the implementation and acceptance record.

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

Hosted run `40771508608` at `c9fa3f73` passes the new arithmetic measurements
but times out in the eight-mutant JSON reading/extraction measurement after
four value-suite cases pass. The failure reaches the 300-second test limit
while workers compile and execute classifiers; it is not an aggregate timeout.
The seven-mutant non-arithmetic number measurement passes in 278.68 seconds,
leaving only 21.32 seconds of test headroom. The JSON-function, JSON-each/clock
and date/modifier measurements do not execute after that first failure.

Manual run `40841195886` at `b2f5e6b0` passes every Linux mutant owner and the
Linux main check. Its macOS core owner passes all six resolver measurements,
then comparison passes in 284.33 seconds and query evaluation reaches the
300-second limit (303.16 seconds with cleanup). The stack waits for a mutant
classifier build; it does not identify the mutant or a semantic assertion
failure. The combined evaluation group has seven mutants. Query resolution,
keys/aliases, UPSERT/conflict algorithms and rebuild measurements remain unrun.

The same manual run's macOS model owner executes all 241 cases: 239 pass and
two historical-name rejection cases (`TableProperties`, `IndexDefinition`)
reach their 10-second Lean subprocess limits with blank output. The other
eleven names, catalog/row-shape checks and row codec checks pass. Each name
starts a separate compiler with the same broad model and resolution-codec
imports. The Linux owner passes all thirteen historical-name cases. These
cases certify completed ADR 0008 vocabulary cleanup, not current SQL behavior.

The same run's macOS JSON/date owner passes six measurements, then the five
date-function mutants exceed the 300-second test limit (305.65 seconds with
cleanup). The date-modifier measurement remains unrun. JSON values pass in
278.49 seconds and lookup/errors in 241.77 seconds; JSON functions, validation,
`json_each` and clock pass in 193–218 seconds. The date failure waits for
classifier builds, with no semantic assertion failure. Its complete suite
time is 1,661.38 seconds, below the aggregate limit. These observations require
further bounded measurements and separate ownership for JSON and date/clock.

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

The value follow-up must also give JSON reading/extraction and the other number
rules practical per-test headroom. All eight JSON mutants and seven other number
mutants retain their exact edits, guards and targets in disjoint measurements.
The numeric/FROMless and JSON/date/clock workloads have separate static owners:
splitting the two measured groups otherwise grows the current value owner to
ten tests, whose individual limits can exceed the unchanged aggregate limit.
Use the existing inventory, suite helper and CI matrix. The unexecuted tail
requires focused timing evidence; any further split preserves its existing
table and guard meanings. No new mutation, oracle, measurement framework or
production definition is required.

The core follow-up gives the three comparison mutants and seven evaluation
mutants practical per-test headroom on both platforms. Split the existing
measurements further at semantic boundaries inside their current tables,
retaining every exact edit, target and guard. The four
unrun tail measurements require focused timing evidence; further grouping may
be needed for their existing query-resolution, key/alias, conflict and rebuild
rules. Preserve the unchanged model's agreement and the existing native case
suppliers. Base setup and cleanup count toward each limit. Additional groups
must also fit their static owner's aggregate limit; use the existing ownership
mechanism when a split requires another owner. No test/harness framework,
production change, larger limit or automatic retry is part of this follow-up.

Retire the thirteen `test_replaced_model_names_absent` cases as completed
ADR 0008 migration scaffolding. The no-alias rule and existing source cleanup
checks remain in force. Preserve `test_whole_shape_conformance`, the row codec
golden/corrupt-input checks, `compile_checks` and its callers unchanged. Remove
only the obsolete module-docstring claim and the source scanner's exemption
for this historical-name matrix. Do not replace it with another name matrix,
import-text test or permanent audit. No production code or deadline changes.

The JSON/date follow-up gives the JSON reading and date-function measurements
practical per-test headroom and covers the unrun date-modifier tail. Its
thirty-four mutants retain their exact edits, target/guard maps and native
case suppliers. Refine groups at their existing semantic boundaries: JSON
conversion/rendering and path/error rules, date inputs/results, and date
modifier arithmetic/order/keywords. Focused timing evidence determines the
final groups. Setup, baseline agreement and cleanup remain inside each limit.
JSON and date/clock have separate static owners through the existing inventory
and CI matrix, so their expanded measurements also fit the aggregate budget.
Keep accepted JSON-function, validation, `json_each` and clock measurement
contracts unchanged; their static owner or file may change. No mutation table,
production code, native oracle, harness, deadline or retry policy changes.

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
`tests/conformance_table_mutants_test.py`. The core follow-up moves
query-resolution measurement to
`tests/conformance_query_resolution_mutants_test.py`. Keep executable and proof bodies
unchanged when repairing the import boundary.

The full-run follow-up also owns the affected arithmetic/write measurements,
`tests/nix_suites.json`, the existing scheduled/mutant inventories, their Nix
definitions and CI matrix, and existing routing/ownership checks. The separate
default-fixture work owns only `tests/column_default_value_test.py`. These two
work surfaces can proceed in isolated workspaces; coordinate Nix execution.

The value follow-up owns `tests/conformance_query_value_mutants_test.py`, the
extracted `tests/conformance_json_date_mutants_test.py`, the existing
inventories/matrix and their documentation. The later JSON/date follow-up
splits that combined file and owner as described below. Existing table/guard
data in `conformance/` remains unchanged.
Arithmetic and FROMless measurements retain their accepted contracts. The
JSON-function tail has six mutants; JSON-each/clock and date/modifier each have
ten. These are relevant diagnostic surfaces, not permission to alter the
unaffected model or the already accepted mutant owners.

The core follow-up owns `tests/conformance_query_mutants_test.py`, narrowly
extracted files for its existing measurements if needed, and the existing
inventories, matrix and documentation. Its tables are `query_mutants`,
`key_mutants`, `alias_mutants`, `upsert_mutants` and `algorithm_mutants` under
`conformance/`; their entries, target maps and guard meanings stay unchanged.
The resolver and rebuild files keep their accepted measurement bodies and may
change static ownership only. The rebuild tail still needs a timing result.
Do not change the other accepted owners or the pending JSON/date/table work
without further evidence and a recorded task extension.

The historical-name retirement owns only that matrix and docstring in
`tests/shared_table_shape_test.py` and its obsolete `ABSENCE_CHECKS` exemption
in `tests/resolution_cleanup_test.py`. Keep the latter's frontend architecture
and replaced-name source checks. Retain the old source revision and Linux
thirteen-case Nix result as migration evidence. The existing model owner must
pass the remaining catalog/row-shape and codec tests, and the existing source
suite must pass the cleanup checks. With no other changes the model owner
collects 228 cases after retirement. The current hosted model owner must pass
on both platforms; historical passes do not establish the new source's result.

The JSON/date follow-up owns the existing combined test file, its narrowly
extracted JSON and date/clock measurements, and the existing ownership
inventories, CI matrix and documentation. Keep `json_mutants`,
`json_function_mutants`, `json_each_mutants`, `clock_mutants`,
`date_function_mutants` and `date_modifier_mutants` unchanged. Coordinate the
shared inventories with the core follow-up worker; isolated test-file work can
proceed independently. The pending table owner and numeric value/core measurements
are outside this follow-up's scope.

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

Value follow-up evidence must cover every resulting changed measurement and
the three previously unexecuted tail measurements, through their actual Nix
owners. Record individual times, complete mutant/target/guard membership and
the resulting workload of each owner. Hosted/local timing ratios can inform
grouping but cannot establish hosted success. Preserve already accepted
measurements where their source inputs match. The existing ownership/routing
checks must cover the extra static owner; no new permanent partition test is
needed. The full hosted completion gate above still applies.

Core follow-up acceptance covers every resulting comparison/evaluation group
and all four previously unrun tail measurements through focused existing Nix
owners. Retain exact identities, target/guard maps, native case suppliers and
their disjoint union. Record each duration, total owner workload and any local
resource settings that differ from hosted execution. The earlier Linux passes
are diagnostic evidence where an edited test file changes the Nix source;
they are not cache hits for the new file. Use the existing routing checks and
one-time membership audit, with no new permanent partition gate. Successful
current hosted execution on both platforms remains required.

JSON/date acceptance covers every resulting changed or moved measurement,
including the previously unrun modifier rules, through focused existing Nix
owners. Retain exact thirty-four-mutant membership, edits, guards, target maps
and selected native cases in a one-time audit. Record the static owner budgets,
individual durations and any local resource settings that differ from hosted
execution. Timings from earlier groups can inform partitioning but do not
establish new-source or hosted acceptance. Use the existing routing checks;
no permanent partition test or replacement harness is required. Both current
hosted platforms must pass the complete resulting scheduled owners.

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
