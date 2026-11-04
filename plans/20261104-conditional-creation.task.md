# Conditional table and index creation

Date: 2026-11-04. Status: OPEN.
Audience: the implementation team.
Specification: [ADR 0030](../docs/adr-0030-conditional-creation-and-expression-grouping.md),
slice 1 (D1 to D3, the first item of D7, the slice-1 parts of D8). Accepted by the owner on
2026-11-04; owner decision 1 follows recommendation (a).
Record: [status](20261104-conditional-creation.status.md).
Source baseline: main `528ea92`.

This is core work: it adds two statement forms to the model. It changes predictions, so it
adds claims and a corpus; those go into the claims pull request at the end of the ADR (D8).

## Required behavior

When the task is done, all of these are true:

1. **Syntax (D1).** `Syntax.Statement.createTable` and `createIndex` have the last field
   `ifNotExists : Bool := false`, with a docstring that says what it means and which value to
   use without the clause. Every statement that the model wrote before keeps its meaning.
2. **Translation (D1, D2).** The translation of `CREATE TABLE` and `CREATE [UNIQUE] INDEX`
   records the clause and no longer refuses it. Every other refusal of the translation stays,
   also with the clause (`TEMP`, a schema name, `AS SELECT`, the unmodeled column and table
   forms).
3. **Resolution (D3).** With the clause:
   - `CREATE TABLE` whose name is a table or a view resolves to `.drop []` with
     `catalog.drop []`; with an index of the name it gives `there is already an index named %s`;
     with a free name or a trigger of the name it resolves as without the clause.
   - `CREATE INDEX` whose name is an index (any table, terms, filter or `UNIQUE`) resolves to
     `.drop []` with `catalog.drop []`; a table or a view of the name gives
     `there is already a table named %s`; a free name resolves as without the clause.
   - Every check before the name check gives its error as today: the reserved name of a
     table; for an index the missing table, the view target, the reserved table and the
     reserved index name. No check after the name check runs for a no-op.
   - Without the clause, every resolution is as today. A schema description (`resolveSchema`)
     accepts the clause with the same meaning.
4. **Effects.** A no-op outputs `.done 0` and keeps the database, the transaction state and
   the counters (`changes()`, `total_changes()`, `last_insert_rowid()`). A free name runs as
   without the clause, also the `UNIQUE` check over existing rows.
5. **Proofs (D7, first item).** Each theorem that the context of ADR 0030 lists for
   `resolveCreateTable` and `resolveCreateIndex` holds for the new field: with the no-op case,
   or with the premise `ifNotExists = false` where the theorem is about creation only. The
   public `Script.createIndex_allOk_iff` and `Succeeds.iff_createIndex` state the success of
   the index statement with the clause in their conditions. Every new proposition has its
   plain-words docstring.
6. **Documentation.** `docs/semantic-subset.md` removes `IF NOT EXISTS` from the refused forms
   and documents it for tables and indexes, in the commit that changes the behavior.

## Tests

- **Translation**: `tests/syntax_mapping_test.py` checks that the clause gives the flag for
  both forms and that the other refusals stay with the clause.
- **Authored corpus**, recorded with the native oracle (version 7 records), for each row of
  the table "Conditional creation: SQLite" of the ADR; the error order (a reserved name,
  `no such table` before the index name, `views may not be indexed`); bodies that SQLite does
  not read on an existing object (duplicate column, unknown column in an index term or
  filter); `UNIQUE` over duplicates with an existing and a free name; the counters after a
  no-op; a no-op in a transaction that rolls back; ASCII case folding of names. Every case
  agrees, and the corpus is new and claimed in the claims pull request with all its cases in
  `mustAgree`.
- **Promotions**: v4 and v5 `index-if-not-exists`, v4 and v5 `index:index-6.1c:32`, v5
  `index6:index6-14.1:57` and `fkey5:fkey5-10.1:51` agree and go into `mustAgree`. The verdict
  of every other case of every claimed corpus stays.
- **Kernel-checked surface examples** in `tests/surface`: the no-op keeps the database and the
  counters (as `ClaimsViewCreate.lean` does for views), and creation with the clause equals
  creation without it when the name is free.

## Implementation notes

- `resolveCreateTable` and `resolveCreateIndex` are in `Resolution/Definitions.lean`; the
  precedent is `resolveCreateView` (`Resolution/ViewDefinitions.lean`) and
  `resolveCreateTrigger`. The callers that pass the fields are in the statement resolver
  (`Resolution/StatementArms.lean` and its users) and in `resolveSchema`.
- The translation refuses the clause at `Translation/Tables.lean` (`absent header[3]!`) and
  `Translation/Schema.lean` (`absent parts[3]!`) in `belay-sqlite-text`.
- A last field with a default keeps positional constructions, but every pattern match on the
  two constructors must name the new field. Search `packages/`, `tests/surface` and the Python
  that writes Lean statements.
- Before writing the per-theorem cases, analyse the most general form (owner rule): one lemma
  that a statement that resolves to `.drop []` with `catalog.drop []` keeps the database and
  the counters and outputs `.done 0`, for the four CREATE forms, and one resolution lemma per
  form for the no-op condition. The trigger laws (`CreateTriggerStep.lean`) show the premise
  pattern.
- The model's `no such table` message has no schema prefix; compare with the error codes and
  the model's messages, as the existing index cases do.
