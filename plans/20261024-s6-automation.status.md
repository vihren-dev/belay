# Status: S6 effect rules and automation

Created 2026-10-24. Status: OPEN. Part 1 in progress (started 2026-10-26); parts 2 and 3 have not started.
Task: [task file](20261024-s6-automation.task.md).
Specs: ADR17 S6; production execution/assertion/pattern tasks; S5 checker.

## Scope and inputs

This task completes the required proof tactics and their checked effect/frame
rules. It preserves the flexible semantic primitives. Dependency analysis is
conservative and supplies certificates to proved rules; disjoint table names
alone do not establish full commutation. The S6 prototype's counter, clock,
trigger and all-continuation examples remain acceptance cases.

The production execution, assertion and migration tasks plus S5 are
prerequisites. Final FK and table-rebuild work supplies the example semantics.
No production automation, general footprint engine or completion is claimed.

## Progress

- 2026-10-24: specified checked certificates, explicit proof routes, tactics,
  stable proof suggestions, S5 integration and private guide acceptance.
  Review 20261024T152950Z-8b118fbc found no musts or shoulds. Implementation
  remains unassigned pending its listed prerequisites.
- 2026-10-26: inputs refreshed against main after #270 and the possible write
  executions (#271): the prerequisites are implemented, the task names the current
  modules, the query-equivalence example, three acceptance parts (the rebuild example
  waits for the table-rebuild task) and the guide changes recorded here for the guide
  acceptance task. Assigned for part 1.

## Part 1 plan, 2026-10-26

Scope: acceptance part 1 only (effect and frame specifications, conservative dependency
certificates, all-continuation program rules). No tactics, S5 integration or code actions (part 2)
and no INSERT SELECT, RENAME or DROP COLUMN (part 3). The table-rebuild agent owns the model run,
statement and INSERT SELECT files and the surface execution proofs for several executions; part 1
adds new modules only and adds lines to the shared registries.

Modules to add (each below 200 lines, checked Verso docstrings):

- Model (registered in the model `lakefile.toml` globs and in `Belay/Sqlite/Model.lean`):
  `PlainUpdateEffect` (stored rows of an error-free plain UPDATE step, no choice output),
  `PlainWriteErrors` (a failed plain INSERT, UPDATE or DELETE step keeps database and snapshot),
  `SimpleQueryAppend` (a simple query that reads only columns below a width gives the same results
  when cells are appended to its rows), `CertifiedQueryOutputs` (step outputs of such a query on two
  connections whose table scans differ by appended cells).
- Surface (registered in the `belay` `lakefile.lean` globs and in `Belay/Sqlite.lean`):
  `PlainUpdateEffect` and `AddColumnEffect` (fresh-run `ifOk` rules for UPDATE and for ADD COLUMN of a
  plain TEXT field, like `Sql.ifOk_send_plainInsert`), `SqlFrames` (a frame as a statement about every
  branch, with pure, bind, one-step and `Output.oneOf` rules), `PlainWriteFrames` (structural
  sufficient frames of plain writes: other tables, catalog, snapshot, settings), `ReadCertificate`
  (certificate structure, validity, soundness theorem), `ReadAnalysis` (the untrusted analyzer that may
  return unknown), `ReadCertificateExpansion` (weak preservation across the lowercase-field expansion
  from a certificate) and `CertifiedQueryCommutation` (full commutation of a certified query with a
  migration, using `QueryFrames`).
- Tests: Lean fixtures `tests/surface/S6Rules*.lean` (positive rules, negative fixtures) and
  `tests/surface_s6_rules_test.py`.
- Shared files touched, added lines only: the two lakefiles, the two barrels, the guide notes below.

Guide changes to record for the guide acceptance task: none yet.
