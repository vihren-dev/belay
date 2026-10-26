# Table rebuild: query inserts and ALTER rewrites

Created 2026-10-24. Checked on 2026-10-26 against the code at `4fc773a5` and
native SQLite 3.51.0; the check changed no requirement. Status: OPEN. The
prerequisites have landed (section "Starting point"). No concurrent alternative
catalog. Status: [progress](20261024-table-rebuild.status.md).
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

On 2026-10-25 the owner selected possible write executions for plan-dependent
behavior. Secondary-index choices can change rowids, partial writes and error
precedence; even a total ORDER BY does not fix expression-evaluation barriers.
Represent the permitted production traces and their resulting states explicitly.
Do not claim that the model's fixed scan is the pinned planner's chosen plan,
implement that planner, or narrow this task to plan-independent inserts.

Only SQLite's default `legacy_alter_table = OFF` behavior is in scope. Existing
restrictions on unrelated SQL remain explicit; this task does not add writable
attached databases, virtual tables or INSTEAD OF triggers.

## Starting point (checked 2026-10-26)

- **Landed prerequisites.** Derived tables, ordinary CTEs and stored views
  (`CatalogEntry.view`, `CatalogView`), the two foreign-key atoms with their
  statement and run laws, the ADD COLUMN default correction, and the model name
  trace (`resolveStatementTraced`; DONE 2026-10-26) are in the code.
- **Missing forms.** `Syntax.Statement.insert` takes VALUES rows only, and
  `addColumn` is the only ALTER form. The frontend refuses a SELECT source,
  RENAME and DROP COLUMN.
- **What a catalog stores.** A table holds resolved forms by position: CHECK
  conditions, generated expressions, index keys and filters, and the child
  columns of its foreign keys. A foreign key names its parent table and parent
  columns as written. A view and a trigger are syntax (`CatalogView`,
  `CatalogTrigger`) that resolves against the catalog at each use. A rename
  therefore rewrites a table or index by name only. It rewrites views, triggers
  and foreign-key parents by binding. A DROP COLUMN also shifts the column
  positions in the resolved forms.
- **Stored source text is rewritten and observable.** In 3.51.0 the output name
  of an unaliased expression column of a view is the text of the expression, and
  the label of an unnamed CHECK constraint is its text. A rename rewrites the
  name tokens of this text. After `RENAME COLUMN a TO "Z z"` the view column
  `a+1` is named `"Z z"+1`, and a nested `(select a from t t2 where t2.a > 0)`
  becomes `(select "Z z" from t t2 where t2."Z z" > 0)`. After
  `RENAME TO "u v"`, `t.a+1` is named `"u v".a+1`, and a failing
  `CHECK(t.b > 0)` reports `u v`, because SQLite dequotes a label that starts
  with a quote. The model syntax keeps this text as a string
  (`ResultColumn.expression`, the CHECK label) and does not keep the place of its
  name tokens. The implementer chooses how the model learns these places.
- **Name trace.** It covers the queries and expressions of one statement. Its
  gap list (status of the name trace) matters here: the trigger programs and
  the CREATE and ALTER bodies are untraced, and a name inside a stored view has
  the use site as its path (`exact = false`).

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
  retain the pinned engine's streaming/materialization distinctions, including
  destination reads through views/CTEs/nested queries and row triggers. Sorting,
  grouping, DISTINCT, compounds and LIMIT/OFFSET retain their own evaluation
  and error behavior. A source-expression failure is not silently moved before
  an earlier insertion conflict, or after it when native evaluates it first.
  Existing plan-sensitive-query restrictions remain exact; they cannot justify
  refusing an otherwise supported streaming case.
- **Plan-dependent executions preserve complete effects.** Define the admitted
  source-production traces, including row order, evaluation barriers, source
  errors and interaction with preceding insertions. Each resulting alternative
  carries its own output/error, database, connection counters and other changed
  execution state. A later statement runs from that alternative's state. Do not
  merge states cell by cell or choose each later output independently. A source
  row permutation alone cannot describe a sorter that evaluates a later error
  before the first write. Mandated materialization, explicit ordering and
  conflict semantics constrain the alternatives; they are not arbitrary runs.
  State the abstraction's admitted choices without claiming that the pinned
  planner realizes every choice. Include every supported native outcome.
- **Execution and proof clients share the alternatives.** Extend the existing
  statement/run and public branch interfaces to carry possible write states;
  the current query-output-only `Output.oneOf` is insufficient. Prove that the
  actual/canonical run is admitted and that run composition retains each
  branch's reached context. Validity, FK laws, Succeeds, ordinary/fresh triples
  and equivalence/migration laws quantify all admitted branches. Deterministic
  statements remain the singleton case. No theorem about one chosen traversal
  can stand in for a universal write claim. Share this execution meaning with
  conformance rather than adding a second evaluator in the harness.
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
  rename preserves cell values, rowids, affinity and collation. The binding of
  each name is the one that `resolveStatementTraced` records; the rename adds no
  second lookup rule. It closes the trace gaps that it needs, and does not read
  a name of a stored view or trigger by spelling.
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

Retain the paired native index probes: source `(id,x)=(1,20),(2,10)` scanned
without and with an index on x produces different destination rowid/value
associations, and different retained writes when destination UNIQUE value 10
already exists under OR FAIL. Also retain the ORDER BY k probe with source
`(id,x,k)=(1,2,1),(2,1,2),(3,-9223372036854775808,3)` and destination UNIQUE 1:
without an index on k, overflow precedes any insertion; with the index, 2 is
inserted before UNIQUE fails. Both observed executions must be admitted, with
their own later-query observations and counters. These witnesses do not prove
that the represented alternatives are complete; kernel laws must establish
the production/run composition contract for all admitted branches.

Cover matching INSERT triggers with WHEN 0, UPDATE-only triggers, RETURNING,
destination reads in dead expression branches and unused CTEs. These distinguish
compiled-read/materialization rules from textual occurrence or runtime reachability.
Preserve the eligible `INSERT INTO dest SELECT * FROM src` transfer case's source
rowids, including gaps; an explicit destination column list can instead allocate
new rowids. Keep this source-row identity through the shared insertion boundary.

Conformance checks membership in permitted complete executions, including later
state observations. It must reject a mixture of outputs from incompatible
branches. Add kernel fixtures where one admitted write branch violates a claimed
postcondition, and positive all-branch examples. Target mutants that collapse
the alternatives to a canonical scan, evaluate all source expressions eagerly,
or pair one branch's output with another branch's state. Preserve existing
deterministic claims and classify every prediction change. Any needed evidence
format, claim or judge change follows the separate reviewed judge-PR workflow.

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

Capture frozen predictions before changes: the base `4fc773a5` has 55 files, one
for each corpus input. After each model change compare all of them. A prediction
may change only for a case that the new forms make supported. Preserve all
existing mustAgree claims; classify every changed prediction against native
behavior (the verdict forbids DISAGREE in the claimed corpora). New authored
corpus/claim/lock changes belong to a separate judge PR that needs owner
approval before merge. The implementation PR leaves the lock unchanged.

Three acceptance parts: query-source inserts; table/column renames; DROP COLUMN
and integrated rebuild/proof coverage. Part plan (owner decisions of 2026-10-26):
part 1 is done in two stages. Stage (a), which every option needs, is the syntax,
text translation, codecs and the SQLite-ordered preparation of INSERT SELECT.
Stage (b) is the exact source production and the insertion fold; it waits for the
possible-executions interface task, and the coordinator says when to merge it.
Part 2 starts with a syntax change that records the place and quoting of the name
tokens of stored source text (view result-column text, CHECK raw text) and the
quoting of the new name of an ALTER, because the renames must rewrite them token
by token; the translator records them in the syntax. Each coherent commit gets focused checks,
dev-build, relevant dev-verdict and independent review. Each part ends with
post-review `just test-full` and `just verdict`. Task end runs `just test-nix`
and `just test-scheduled-checks`. Only Nix results are acceptance evidence.
The scheduled-checks recipe follows the owner's handoff override, recorded in
[coordination](20261024-adr17-coordination.status.md): no broad local mutant
suite; use relevant mutants by `-k` and leave the full mutant suite to CI.

## Existing interfaces and ownership

The model's Resolution/WriteResolution, Resolution/InsertCells, RowEngineInsert,
RowEngineKeySteps, RowEngineTriggers, ForeignKeyPhases, StatementStep and query
evaluator own the current behavior. Translation/Writes.valueRows currently
refuses SELECT sources. The slice-4 view/CTE catalog and resolution contracts
are in the code (`Resolution/QuerySourceExpansion`, `CatalogView`); extend them.
Do not maintain a second representation.

Pinned sqlite3Insert and readsTable in parser/upstream/sqlite3.c distinguish
streaming and temporary-table paths. sqlite3AlterRenameTable,
sqlite3AlterRenameColumn and sqlite3AlterDropColumn define rewrite/validation
behavior. Their token-aware references matter because expression spelling can
be an output name. A textual global replacement is not an adequate model.

The read-only `adr17_table_rebuild_readiness.md` and
`table-rebuild-probes/source_timing.{py,json}` under the workspace research notes
retain the pinned source locations and 28 bounded native probes. The note's
section "Readiness conclusion and owner decision" is superseded by the decision
of 2026-10-25; its line numbers fit the pinned `parser/upstream/sqlite3.c`
(SHA256 `dc58f0b5`). Existing
QueryFunctions/Subqueries collect complete rows and lose source stop positions;
PossibleOutput changes query observations but does not supply write states.
The accepted extension must expose these missing execution contracts, including
their public proof and conformance consumers. Owner decision of 2026-10-26: the
alternatives interface (the possible executions of a write, with its public
proof and conformance consumers) is the separate task
`plans/20261026-possible-write-executions.task.md`, implemented in its own
workspace; this task consumes it.

Separate source-production/error contracts from existing row insertion and
catalog rewrite/validation contracts where they have different responsibilities.
No VM, duplicate SQL interpreter or generic schema-change framework is required.
Reserve shared syntax/catalog/statement cases, barrels and run laws with the
query-source/FK/S4 agents. Files remain below 200 lines. Report a genuine spec
contradiction before changing semantics; continue independent work meanwhile.
