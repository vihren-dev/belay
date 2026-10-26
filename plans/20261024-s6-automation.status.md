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
- 2026-10-26: part 1 commit 1: statement effect rules (UPDATE, ADD COLUMN), frames and shelter rule, read
  certificates with the untrusted analyzer, weak preservation and full commutation rules, positive and negative
  fixtures and `tests/surface_s6_rules_test.py`. Local fixture runs pass; Nix results follow at the end of part 1.

## Part 1 plan, 2026-10-26

Scope rule from the owner (2026-10-26, applies to all parts): the specific examples of the user guide
(customers, accounts, signup, purge, notBlocked, the email_lower expansion and so on) are not part of the
core (model package) or the surface (belay package). Everything under `packages/` is general: laws about
statement families, frames, certificates and their soundness, stated over arbitrary tables, columns and
schemas with explicit premises, with no module, declaration or premise shaped around one guide example.
Guide examples appear only as test fixtures under `tests/surface` and their pytest drivers. Part 1 adds no
`NormalizedField*`-style module and does not extend the existing `NormalizedField*` modules. A guide
example that general rules cannot prove is recorded below as an open point, not as an example-specific
lemma in a package.

Scope: acceptance part 1 only (effect and frame specifications, conservative dependency
certificates, all-continuation program rules). No tactics, S5 integration or code actions (part 2)
and no INSERT SELECT, RENAME or DROP COLUMN (part 3). The table-rebuild agent owns the model run,
statement and INSERT SELECT files and the surface execution proofs for several executions; part 1
adds new modules only and adds lines to the shared registries.

Modules added (each below 200 lines, checked Verso docstrings; all general):

- Model (registered in the model `lakefile.toml` globs and in `Belay/Sqlite/Model.lean`):
  `PlainUpdateEffect` (stored rows of an error-free plain UPDATE, no choice output), `AddColumnEffect`
  (database after ADD COLUMN), `NonQueryOutput` (a step of a statement that is not a query gives no choice
  output), `PlainWriteFrame` (a plain INSERT, UPDATE or DELETE changes only the rows of its target and keeps
  snapshot and settings), `ReadOnlyFrame` (a query or prepare error step keeps the connection), `ShelterFrame` (`Connection.shelter`,
  `Statement.ShelteredFrom`, `Connection.shelter_step`: a plain write of another table or a read keeps the
  catalog, the table at a position, the snapshot and the settings),
  `SimpleQueryAppend` (a simple query that reads only columns below a width gives the same results when cells
  are appended to its rows) and `CertifiedQueryOutputs` (step outputs of such a query on two connections whose
  table scans differ by appended cells, for any table and any added cells).
- Surface (registered in the `belay` `lakefile.lean` globs and in `Belay/Sqlite.lean`):
  `PlainUpdateEffect` and `AddColumnEffect` (fresh-run `ifOk` rules for UPDATE and ADD COLUMN, like
  `Sql.ifOk_send_plainInsert`), `SqlFrames` (`Sql.Frame` as a claim about every branch, with pure, one-step,
  bind, map and composition rules), `PlainWriteFrames` (`Statement.ShelteredAt` and
  `Sql.Frame.sendStatements_sheltered`: scripts of plain writes of other tables and reads keep the catalog, the
  table at a position, the snapshot and the settings), `ReadCertificate` (certificate, validity, obligations,
  `output_eq`), `ReadAnalysis` (the untrusted analyzer that may return unknown, `analyze_sound`),
  `ReadCertificatePreservation` (weak preservation of a certified read across any migration whose
  obligations hold) and `CertifiedQueryCommutation` (full commutation of a certified read with a migration under
  a constant clock).
- Tests: `tests/surface_s6_rules_test.py` (six tests, listed in `tests/nix_suites.json`) with fixtures
  `tests/surface/S6RulesEffects.lean` (UPDATE and ADD COLUMN effects, conditional and total fresh triples),
  `S6RulesFrames.lean` (frames of a program with an output-dependent continuation, a read with two permitted
  results, the snapshot of an open transaction), `S6RulesQueryPattern.lean` (the migration query pattern of the
  guide proved by the general certificate rules for every bound value), and the negative fixtures
  `S6RulesNegativeReads.lean` (SELECT star, metadata, counter read), `S6RulesNegativeCertificates.lean` (different
  change counts, unmodeled syntax, a certificate whose soundness obligation fails), `S6RulesNegativeFrames.lean`
  (trigger, foreign-key action, generated column, rollback) and `S6RulesNegativeClock.lean` (moving clock).
- Shared files touched, added lines only: the two lakefiles, the two barrels, `tests/nix_suites.json`.

Dropped from the first plan: `PlainWriteErrors` (the failure cases are inside `PlainWriteFrame`) and
`ReadCertificateExpansion` (replaced by the general `ReadCertificatePreservation`, which has no expansion in it).

Rules that the tests exercise by name: `Sql.ifOk_send_plainUpdate`, `Sql.ifOk_send_addColumn`,
`plainUpdate_database`, `Sql.Frame.bind`, `Sql.Frame.sendStatements_sheltered`, `ReadAnalysis.analyze_sound`,
`ReadCertificate.output_eq`, `ReadCertificate.preservesAt_send`, `ReadCertificate.commutesOn_send`.

Guide changes to record for the guide acceptance task: none so far. The guide's lookup-after-expansion
claim is now also provable by the general certificate rules; the guide text needs no change.

Open points:

- The guide's migration query pattern is proved for one concrete database and every bound value
  (`S6RulesQueryPattern.lean`), not for every admitted database with a site. The existing
  `NormalizedField*` lemmas already prove the universal output equality for the guide table, and the general
  rules would need an `appended` obligation for every database of the site. Options: (a) leave it, (b) state
  the obligations for a site structure in a fixture. Recommendation: (a) for part 1; revisit in part 2 when the
  tactics need a source of obligations.
- The rule `ReadCertificate.commutesOn_send` takes a constant clock, the obligations at the connection of
  the run, and the premise `admittedKept` as premises; it accepts any `admitted` predicate that meets them. The
  fixture `S6RulesQueryPattern.lean` chooses the `admitted` predicate that holds only at the original connection
  and clock,; a wider predicate must also satisfy `admittedKept`. A moving clock is a negative fixture
  (`S6RulesNegativeClock.lean`): the premise of a constant clock fails and the commutation claim is false.
