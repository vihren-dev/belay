# Table rebuild: query inserts and ALTER rewrites

Created 2026-10-24. Status: OPEN. Implementation follows task review and the
completed query-source/view representation. No concurrent alternative catalog.
Status: [progress](20261024-table-rebuild.status.md).
Specs: [ADR 0019](../docs/adr-0019-guide-sql.md), D4 and slice 5;
ADR 0017 S6's rebuild; ADR 0022's validity and separate foreign-key atoms.

## Scope and accepted decision

The guide's rebuild copies rows into a replacement table and renames it. The
current model accepts VALUES inserts and ADD COLUMN, but lacks query inserts,
table/column rename and DROP COLUMN. This task supplies the complete ADR19 D4
over the supported SQL language, including its existing conflict algorithms,
upsert clauses, triggers, foreign keys and newly completed views/CTEs.

On 2026-10-24 the owner accepted exact SQLite source evaluation. An independent
INSERT SELECT can stream; a destination read or row trigger can require source
materialization. This affects which error happens first and whether earlier
writes survive FAIL. Do not always evaluate all rows first, and do not replace
the accepted streaming/materialization work with a model restriction.

Only SQLite's default `legacy_alter_table = OFF` behavior is in scope. Existing
restrictions on unrelated SQL remain explicit; this task does not add writable
attached databases, virtual tables or INSTEAD OF triggers.

## Required outcomes

- **Query inserts reach the existing row engine.** SQL text, syntax/resolved
  forms, codecs, execution, conformance and surface forms support INSERT SELECT
  and REPLACE SELECT. Source queries include supported simple/compound SELECT,
  derived sources, ordinary CTEs and views, with parameters and nested queries.
  Destination column lists, omitted/default/generated columns, rowid rules,
  affinity and constraints use the same contracts as existing inserts.
- **Preparation agrees with SQLite.** Resolve destination and query names,
  column counts, conflict targets and RETURNING in SQLite's order and scopes.
  A destination column is not an implicit outer source binding. Preserve valid
  SQL errors separately from model restrictions. SELECT/ON CONFLICT grammar
  ambiguities follow the pinned parser; the surface must not reinterpret text
  to make it parse differently. Existing RETURNING/upsert restrictions remain.
- **Read and write timing is observable.** Source evaluation and row insertion
  follow the pinned engine's streaming/materialization behavior, including
  destination reads through views/CTEs/nested queries and row triggers. Sorting,
  grouping, DISTINCT, compounds and LIMIT/OFFSET retain their own evaluation
  and error behavior. A source-expression failure is not silently moved before
  an earlier insertion conflict, or after it when native evaluates it first.
  Existing plan-sensitive-query restrictions remain exact; they cannot justify
  refusing an otherwise supported streaming case.
- **Effects and failures are exact.** Preserve ABORT/FAIL/ROLLBACK/IGNORE/REPLACE,
  supported ON CONFLICT clauses, FK actions, trigger order and raises, partial
  writes, RETURNING output, change counters and last-insert state. Query rows
  and writes share the actual statement's bindings, clock and connection.
  Counters observed by the source follow native evaluation timing. A failure
  followed by another statement uses the real resulting state on both existing
  stop-on-error and continue-after-error run paths.
- **Renaming a table preserves its identity and rewrites its references.**
  `ALTER TABLE t RENAME TO u` keeps rows, rowids, constraints, indexes and
  triggers while updating the names/references SQLite updates under the default
  setting, including views and foreign keys whether enforcement is on or off.
  Object collisions, nonexistent/wrong-kind targets and invalid dependent
  schema definitions have SQLite's prepare errors. Table/index/catalog positions
  must not accidentally make a stored reference point to another object.
- **Renaming a column follows binding, not spelling.**
  `ALTER TABLE t RENAME COLUMN a TO b` rewrites the relevant table constraints,
  generated expressions, keys, indexes, triggers, views and foreign-key column
  references. Identically spelled columns in unrelated scopes, string literals,
  aliases and unrelated objects keep their meaning. Detect ambiguities created
  by a rename where SQLite rejects them. Preserve native declared/output names,
  quoting-dependent expression text and later resolution behavior. A successful
  rename preserves cell values, rowids, affinity and collation.
- **Dropping a column rewrites storage and rejects live dependencies.**
  `ALTER TABLE t DROP COLUMN a` removes the allowed column and its stored cells,
  preserving the remaining cells' positions/values, rowids and table order as
  required by the model. Keys, indexes, constraints, generated expressions,
  foreign keys, triggers and views retain SQLite's dependency checks, including
  definitions whose names cannot resolve after the change. Test the difference
  between constraints owned solely by the removed column and dependencies that
  survive it, against native behavior. A failed ALTER leaves the schema and rows
  unchanged; it cannot partly rewrite one dependent object before failing.
- **Transactions and object lifetime remain correct.** ALTER participates in
  snapshots/rollback. Statements after it resolve against the new schema;
  rollback restores both catalog definitions and stored rows. Late-resolved
  view/trigger definitions cannot retain stale positions or skip SQLite's
  schema validation. DDL counters and output shapes remain native.
- **Existing invariants and proof interfaces extend to the new forms.**
  Prove Admitted/Valid preservation for actual outcomes of all new statements
  and their run paths, including partial writes and rollback. Extend the
  separate FK atom/frame/preservation matrix with the required mapping transport
  and schema conditions. Neither FK atom is silently included in Valid. Expose
  narrow query-to-insert and rename/drop contracts needed by S6's rebuild proof;
  clients must not unfold an entire new execution branch to use them.
- **The guide's rebuild has the right concrete behavior.** With enforcement
  explicitly enabled before the transaction, the unsafe DROP-based rebuild
  exhibits its cascade. The corrected rebuild retains the intended parent and
  child rows and yields the expected foreign_key_check result. Also exercise
  the initial-FK-off default and pragma changes inside transactions. This task
  supplies exact execution and model lemmas; S6 proves the universal guide claim.
- **Documentation and evidence state the delivered scope.** Update the semantic
  subset and ADR implementation record. Public propositions describe all
  hypotheses and error/vacuous cases, with short proof sketches. Record measured
  conformance gains and remaining restrictions, not lexical SQL counts.

## Tests and acceptance

Pinned SQLite 3.51.0 is the oracle for authored cases. Include the accepted
precedence example: source rows `2, 1, -9223372036854775808`, destination UNIQUE
value `1`, and `INSERT OR FAIL INTO dest SELECT abs(x) FROM src`. Without a row
trigger the unique failure leaves the newly inserted `2`; with an AFTER INSERT
trigger containing `SELECT 1`, materialization hits integer overflow first and
does not insert `2`. Also cover self-insertion without recursive growth, empty
sources, destination reads hidden in supported views/CTEs, and source counters.

The insert matrix includes explicit/implicit columns, default/NULL/generated
values, INTEGER PRIMARY KEY and WITHOUT ROWID, bound parameters, aggregates,
sorting and compounds; all supported conflict paths, RETURNING, FK actions and
triggers; failures at prepare, source evaluation and insertion; and a later
statement that observes partial effects. Cover LIMIT certainty explicitly.

The ALTER matrix includes table/column names colliding or differing by case,
quoted identifiers and literal text, schema-qualified references where already
supported, aliases/shadowing, keys and expression/partial indexes, generated
columns, FK enforcement on/off, late-resolved/nested views, triggers, invalid
dependent definitions and rollback. Native errors and unchanged post-failure
state are both checked. Successful operations test the rewritten references by
executing later queries/writes, not only inspecting a syntax value.

Kernel examples and Nix-selected surface fixtures use sql/db!/db.run, the
new model contracts and the concrete corrected/unsafe rebuild. Audit exported
proofs for forbidden axioms; no native computation certifies a theorem. Use
finite timeouts and existing test infrastructure. Target relevant mutants only
with `-k`, including eager-source evaluation and incomplete schema rewrites.

Capture frozen predictions before changes. Preserve all existing mustAgree
claims; classify every changed prediction against native behavior. New authored
corpus/claim/lock changes belong to a separate judge PR that needs owner
approval before merge. The implementation PR leaves the lock unchanged.

Three acceptance parts: query-source inserts; table/column renames; DROP COLUMN
and integrated rebuild/proof coverage. Each coherent commit gets focused checks,
dev-build, relevant dev-verdict and independent review. Each part ends with
post-review `just test-full` and `just verdict`. Task end runs `just test-nix`
and `just test-scheduled-checks`. Only Nix results are acceptance evidence.

## Existing interfaces and ownership

The model's Resolution/WriteResolution, Resolution/InsertCells, RowEngineInsert,
RowEngineKeySteps, RowEngineTriggers, ForeignKeyPhases, StatementStep and query
evaluator own the current behavior. Translation/Writes.valueRows currently
refuses SELECT sources. The slice-4 view/CTE catalog and resolution contracts
must be integrated before implementation. Do not maintain a second representation.

Pinned sqlite3Insert and readsTable in parser/upstream/sqlite3.c distinguish
streaming and temporary-table paths. sqlite3AlterRenameTable,
sqlite3AlterRenameColumn and sqlite3AlterDropColumn define rewrite/validation
behavior. Their token-aware references matter because expression spelling can
be an output name. A textual global replacement is not an adequate model.

Separate source-production/error contracts from existing row insertion and
catalog rewrite/validation contracts where they have different responsibilities.
No VM, duplicate SQL interpreter or generic schema-change framework is required.
Reserve shared syntax/catalog/statement cases, barrels and run laws with the
query-source/FK/S4 agents. Files remain below 200 lines. Report a genuine spec
contradiction before changing semantics; continue independent work meanwhile.
