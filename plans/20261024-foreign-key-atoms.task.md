# Foreign-key facts and their preservation

Created 2026-10-24. Status: DONE (2026-10-26).
Status: [status file](20261024-foreign-key-atoms.status.md).
Scope: [ADR 0022](../docs/adr-0022-database-validity.md), slice 5 and its
2026-10-24 amendment; [ADR 0017](../docs/adr-0017-user-surface.md), S6.
Base inspected: `vihren-dev/sqlite-verifier`, PR #239, commit `98a07bfe`.

## Problem and accepted decision

The current `Database.ForeignKeysHold` mixes row truth with the current choice
of parent key. SQLite 3.51.0 allows DROP INDEX to remove a parent's supporting
unique key while `foreign_keys` is on. Matching rows remain, but preparing
`foreign_key_check` then fails with a foreign key mismatch. ADR 0022 D3's earlier
unconditional preservation claim was false.

On 2026-10-24 the owner selected two separate atoms: parent-schema compatibility
and row-reference validity, with a revised public API and proofs. Both remain
outside `Database.Valid`. This task delivers the current statement forms; later query-source and
ALTER work must extend the laws when it adds statement forms.

Amended by owner decision on 2026-10-24: first correct the shared engine NULL
check to use the selected parent mapping. For a located parent, test the child
columns of that comparison, including repeated columns. With no selected
comparison, retain SQLite's declaration-column fallback. The old original-column
rule incorrectly accepts `(99,NULL)` in the repeated-key example below. Revise
the default atom mapping and proofs to match the corrected engine.

Further accepted on 2026-10-24: foreign-key actions use the selected mapping
for their child targets too. Correct CASCADE, SET NULL and SET DEFAULT, together
with assigned/changed columns used by constraints, generated columns and
UPDATE OF triggers. Preserve repeated selected targets and leave unused declared
columns unchanged, as pinned SQLite does. Add native regressions for both
mapped-NULL and mapped-action corrections.

Further accepted on 2026-10-25: correct ADD COLUMN's REFERENCES default check.
With enforcement on, a nonempty table rejects a REFERENCES column whose default
is neither absent nor a literal NULL. An empty table can accept it. Preserve
SQLite's default-form distinction: `NULL` and `(NULL)` qualify, but `(+NULL)`
does not qualify merely because it evaluates to NULL. Pinned native also
accepts the bare `+NULL` (grammar literal); the last DEFAULT of a column decides.
The model leaves `+NULL`, `-NULL` and parenthesized defaults unsupported, so
the proven cases are the absent default, `NULL` and the non-NULL spellings. This correction, with
native regressions and updated preservation laws, joins the planned execution
changes. Do not replace the correction with a NULL-only proof restriction.

## Required outcomes

1. **Explicit row meaning.** A public primitive describes row-reference validity
   for a supplied mapping of each declared foreign key. The mapping determines
   the NULL-test columns, parent identity and resolved rowid or column-pair
   comparison. Located targets use the selected child projection; absent or
   mismatched targets use the declaration-column fallback. It retains parent affinity,
   collation and INTEGER PRIMARY KEY rules. The row atom says: each child row
   has a NULL key cell, or a parent row satisfies that comparison. Supporting
   index existence is not part of this atom. A missing target is explicit: a
   NULL child key satisfies the row fact; a non-NULL key does not.
2. **Separate schema meaning.** A second atom says that every declared foreign
   key has a supported parent mapping, and that the current catalog selects
   exactly the supplied mapping. It checks declarations even with empty child
   tables or only NULL child keys. An absent parent, unsupported key, mismatched
   arity or different selected mapping fails it. Caller-supplied mappings cannot
   omit a declaration to make a database-wide fact pass vacuously. Use the
   existing `Catalog.parentKey` selection rules rather than a parallel algorithm.
3. **Usable defaults and precise checks.** A convenience operation derives the
   mappings selected by the current catalog. With those mappings, the row check
   agrees with the corrected engine's `ForeignKeyLink.satisfied` for every row.
   Both atoms have table and database forms, executable checks, decidability
   and kernel-checked equivalence lemmas. The surface exposes both atoms and
   the explicit-mapping primitive. It replaces the old `ForeignKeysHold` API
   and all callers, without compatibility aliases. The default remains exact
   SQLite behavior, including repeated key columns.
4. **Correct pragma laws.** Revise the `foreign_key_check` laws to name the new
   row fact with catalog-selected mappings. State preparation separately from
   row generation. Neither an empty violation list nor the row atom alone
   proves that the parent schema is compatible. A missing parent and a present
   but nonunique parent can have different preparation behavior. Document the
   exact conditions of the full statement law and retain table-specific checks.
5. **Independent frame laws.** A schema frame names the catalog declarations,
   parent definitions and eligible indexes that it reads. A row frame names
   child rows, parent rows, parent-column definitions and the supplied mapping.
   Dropping only a supporting index preserves row truth under transported
   mappings, even if the drop shifts catalog positions; schema compatibility
   may fail. Stable table identity or explicit transport must prevent a mapping
   from silently referring to another table after a catalog edit. A parent-row
   deletion with enforcement off can preserve schema compatibility and break
   row truth. These laws expose actual dependencies for S6 footprints.
6. **Statement and run laws.** Give conditional preservation laws for each atom
   over the current `runStatement`, `runSqlFrom`, `runSql` and `runScriptFrom`
   paths. Cover the actual resulting database on success and error, including
   partial FAIL writes, triggers, foreign-key actions, snapshots and rollback.
   Conditions name input/schema/mapping/connection facts and allowed effects;
   they must not assume the desired final atom or restate the whole theorem.
   Data writes with enforcement on use the same resolved mapping that their
   checks enforce. Parent-write laws also name the needed consistency between
   child scans and parent lookups: their affinity rules can differ. Expose that
   comparison premise and proved structural sufficient conditions; enforcement
   and compatible schemas alone do not establish it. DDL that adds a declaration
   or changes parent-key selection
   needs an explicit schema/mapping condition. Do not promise unconditional
   preservation for CREATE TABLE with a forward reference or DROP INDEX.
   Expose individual atom laws and convenience combined laws. The existing
   `Admitted` and `Valid` preservation theorems continue to hold.
   ADD COLUMN uses the corrected enforcement, table-emptiness and default-form
   checks. Its rejection leaves both catalog and rows unchanged; successful
   cases still require the schema/mapping premises of the separate atoms.
7. **A usable proof boundary.** Reuse the existing row/run preservation machinery
   where its contract fits. Foreign-key facts depend on more than one table;
   do not force them into a table-local `WriteLaws` premise that hides parent
   reads or copy the entire interpreter into a proof module. Any added shared
   contract must be needed by these laws. S6 can combine the schema and row
   facts for its cascading rebuild proof without unfolding the row engine.
8. **Documentation matches the formulas.** Update the model and surface docs,
   guide examples in this repository, and ADR 0022's implementation record.
   Each proposition states its quantifiers, dependencies, assumptions and
   vacuous cases. Each public law has a short proof sketch. Record an atom-by-
   statement matrix of preservation conditions and concrete necessity examples.

## Observable examples and acceptance

The test suite must distinguish the atoms, not just exercise their definitions:

- Compatible parent schema and matching rows: both atoms hold. A child orphan
  inserted with enforcement off: schema holds and row truth fails.
- A matching child followed by DROP of the supporting unique index: supplied
  row truth remains, schema compatibility fails and native pragma preparation
  reports a mismatch. Put the index before the child in catalog order to check
  mapping transport. Check a second eligible index and changed selection too.
- Missing and nonunique parents with empty or all-NULL child keys: schema
  fails and row truth holds. A non-NULL child with no target fails both.
- Composite keys, implicit primary keys, INTEGER PRIMARY KEY, parent affinity,
  NOCASE and NULL behavior use the existing comparisons. Include filtered and
  expression indexes, mismatched collations and implicit-PK arity.
- Preserve this supported repeated-column case exactly:
  `CREATE TABLE p(a,b,PRIMARY KEY(a,a));`
  `CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));`
  after inserting parent `(1,2)`, child `(1,99)` succeeds with enforcement on
  and the pragma returns no violations. SQLite selects child `x` twice; do not
  silently reinterpret it as the written `(x,y)` to `(a,b)` pairing.
- In the same schema, child `(99,NULL)` fails under enforcement. Stored with
  enforcement off, it produces a `foreign_key_check` violation. NULL in unused
  `y` does not exempt it; NULL in selected `x` does. Check the shared helper's
  callers in write phases and pragma checks, including UPDATE and parent-row
  changes. Missing-target checks retain the declaration-column fallback.
- For the repeated-key schema with ON UPDATE CASCADE, updating parent `a` from
  1 to 99 changes child `(1,NULL)` to `(99,NULL)`, not `(99,99)`. With an unused
  non-NULL `y`, CASCADE leaves it unchanged too. SET NULL and SET DEFAULT also
  update only the selected projection. Compare an UPDATE OF unused-column
  trigger with one watching the selected column; generated dependencies and
  constraint checks receive the actual assigned/changed targets. Cover parent
  UPDATE and DELETE actions, ordinary composite keys and rowid parents.
- Include the native scan/lookup necessity example: parent `p(k TEXT UNIQUE)`
  stores `'1'`, child `c(x INTEGER REFERENCES p(k))` stores `1`, and an AFTER
  DELETE trigger on the parent inserts `'01'` when deleting `'1'`. The DELETE
  succeeds with enforcement on, but foreign_key_check then reports the child.
  Preserve SQLite's behavior and state the missing comparison premise in the
  conditional theorem; do not assume final row validity to conceal this case.
- Compare ADD COLUMN REFERENCES with enforcement on/off and empty/nonempty
  tables. Retain the mismatch where a nonempty child accepts `DEFAULT 99` in
  the old model even when native rejects it, including a matching parent 99.
  Cover omitted default, `NULL`, `(NULL)`, `(+NULL)`, a cast producing NULL,
  numeric constants, parenthesized expressions and CURRENT_TIMESTAMP wherever
  the existing syntax supports them. Check the native error precedence and
  unchanged catalog/rows after rejection, as well as successful controls.
  Evaluate defaults through the existing code; their value alone must not
  erase the syntax distinction that the native REFERENCES check observes.
- The statement/run matrix covers foreign keys on/off, immediate constraints,
  NO ACTION/RESTRICT/CASCADE/SET NULL/SET DEFAULT, triggers, conflict outcomes,
  explicit transactions and rollback. Unsupported deferred constraints retain
  their current result. Include counterexamples that show why each substantive
  preservation condition is needed and a non-vacuous successful run per family.
- Kernel examples and surface fixtures exercise both primitive and convenient
  APIs and the pragma laws. Audit exported proofs for forbidden axioms such as
  `sorryAx` and `ofReduceBool`; no native computation certifies a theorem.
- Capture a frozen-prediction baseline before model edits. Classify every changed
  prediction against pinned native SQLite; only changes explained by the accepted
  mapped-NULL, mapped-action and ADD COLUMN default corrections are planned.
  Preserve all mustAgree claims;
  do not weaken a claim to hide a regression. Native probes use the pinned 3.51.0 build. Use
  existing test infrastructure, finite subprocess timeouts and real Nix suite
  registration. Add authored native regression evidence through the existing
  corpus workflow. Corpus/claim/lock changes belong in a separate judge PR with
  owner approval required before merge; the implementation PR leaves them alone.
- Each coherent commit has targeted checks, `just dev-build` for package edits,
  and independent review. At each acceptance-part boundary run `just test-full`
  and `just verdict`; at task end run `just test-nix` and
  `just test-scheduled-checks`. The owner's cadence override is recorded in
  [the build-boundary status](20261024-text-build-boundaries.status.md).
  Status and PR acceptance claims cite only Nix results.

Two acceptance parts: mapped-NULL/action corrections, split API, checks, pragma
correspondence and frames; the ADD COLUMN default correction, statement/run
preservation laws and downstream proof examples. Both parts
are required for slice 5 to be complete. The implementer chooses the work units.

## Existing code and constraints

All paths below are below `packages/belay-sqlite-model/Belay/Sqlite/Model/`:
`ForeignKeysHold.lean`, `ForeignKeySatisfied.lean`, `ForeignKeyCheckLaws.lean`,
`ForeignKeyCheck.lean`, `ForeignKeyMatch.lean`, `ForeignKeyPhases.lean`,
`ForeignKeyWrites.lean`, `ForeignKeyRows.lean`, `Resolution/ParentKeys.lean`, `Resolution/Drops.lean`,
`DatabaseWriteLaws.lean`, `RowEngineFacts.lean`, `RunHolds.lean` and
`ScriptRunHolds.lean`. Surface export: `packages/belay/Belay/Sqlite/Database.lean`.
Native selection/actions: `sqlite3FkLocateIndex` and `fkActionTrigger` in `parser/upstream/sqlite3.c`.
`sqlite3AlterFinishAddColumn` checks the default's syntax before emitting the
nonempty-table REFERENCES error. Reuse the existing ADD COLUMN resolution and
execution boundary; keep its table-dependent check in the actual run path.

`Catalog.drop` renumbers positions. Parent selection can depend on index order.
`matchIndex` permits repeated parent columns, as the accepted slice-4 decision
requires. The old child NULL test reads columns unused by that mapping; this
task corrects it in the shared helper rather than separately patching each caller.
The old atom is not the conjunction of the new atoms, because empty child rows
can satisfy it even when the parent schema is incompatible. Prove correspondence
to the corrected native behavior rather than strengthening the row fact silently.

Stop and report a specification finding if an execution-semantic change is
needed beyond the accepted mapped-NULL/action and ADD COLUMN default corrections,
if the split cannot express SQLite's rules, or if a
preservation claim has a native counterexample not handled by its stated
conditions. Continue independent work while the owner decides.
