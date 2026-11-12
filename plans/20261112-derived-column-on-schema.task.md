# Task: short proofs of the derived-column migration on a schema

Created 2026-11-12 (status: `20261112-derived-column-on-schema.status.md`). Issue #376, launch blocker.

## Problem

The most common migration adds a column and fills it from the other columns:

```sql
ALTER TABLE customers ADD COLUMN email_lower TEXT;
UPDATE customers SET email_lower = lower(email);
```

Two agents that followed the page for agents (`docs/guide/agents.md`, PR #373) on 2026-11-10
found these problems with the schema `shop` of that page:

1. **Reads.** `addEmailLower preserves namedCustomers on shop` follows from
   `DerivedColumnMigration.queryPreserves`, but the proof needs a `Site` (15 fields) and a
   `Site.ReadPreserved` (7 fields) for each database of the schema: 150 to 180 lines for two reads
   (`tests/surface/Schema/Tests/DerivedColumnSchemaPremise.lean`). The helpers of that proof are in
   `tests/surface/`, so a consumer project cannot import them, and both agents wrote them again.
2. **Success.** `Succeeds addEmailLower (·.HasCatalog shop)` is `unknown` for `#sql_check`, and
   `sql_auto` fails. No law of the library states that this migration succeeds.
   `addColumn_plain_step` and `backfill_step` assume that the step continued without an error.

Owner decision, 2026-11-12: full scope for the launch. The scope is (a) a builder for the `Site`
and `ReadPreserved` facts from a `db!` schema and a `HasCatalog` premise, (b) a success law for the
derived-column migration, and (c) a compiled example that the page for agents links.

## What must be true when the task is done

### Reads (a)

- For a schema `schema : Database` and a migration script with the derived-column shape (one
  `ALTER TABLE … ADD COLUMN` and one `UPDATE … SET column = value` of that table, as `sql` text), a
  user proves `M preserves Q on schema` for a read `Q` that the law covers. The proof uses public
  declarations of the `belay` package only and has at most 5 lines. The user writes no field of
  `Site` or `Site.ReadPreserved`. The user also does not restate the migration or the read as
  syntax trees: the proof works from the scripts as the `sql` text gives them.
- The facts that the law needs are checked once, on the catalog of `schema`, by a computation
  that the kernel evaluates (`decide +kernel` or `rfl`). They are not checked by `native_decide`,
  so the theorems have only the axioms `propext`, `Classical.choice` and `Quot.sound`.
- The builder is a primitive, not the only door (workspace rule 19). Public declarations give,
  from the checked facts, the `Site` for each database of the premise and the `ReadPreserved` of
  each covered read. A user can use them with `queryPreserves`, `queryTranslates`,
  `Site.run_state` and `Site.branch_database`, and can still build a `Site` or a `ReadPreserved`
  by hand for a case that the check does not cover.
- The check is general: it is not about `shop`, `customers` or `lower`. It covers each table,
  column definition, written value and simple read (one table, no join, no subquery, a filter and
  result columns of old columns) for which a `Site` and a `ReadPreserved` exist with a calm query.
  The docstrings of the public declarations state what the check does not cover.
- When a fact does not hold, the check is false, so the proof fails. It does not give a theorem
  that is false. Examples: `SELECT *` (the result gets the new column), a column name that the
  table already has, a trigger that an UPDATE of the new column fires, and a value that reads
  the clock or a parameter.

### Success (b)

- A law states that the derived-column migration succeeds, as `Succeeds M domain`, on each
  database of a domain that gives a `Site`, for every complete environment, when the written value
  cannot fail. "Cannot fail" is a condition that the kernel can decide on the resolved value. It
  must include the type check of a `STRICT` table: a value that the new column of a `STRICT`
  table does not accept makes the `UPDATE` fail.
- With the builder of (a), a user proves `Succeeds addEmailLower (·.HasCatalog shop)` in at most
  5 lines, with the same rules as for reads: public declarations, kernel evaluation, no syntax trees.
- When the value can fail, the condition is false. `#sql_check` shows that the boundary is real:
  for a migration whose value can fail, for example a `STRICT` table whose new `INTEGER` column gets
  a text value, `#sql_check` of its `Succeeds` claim gives `false`.

### Example and documentation (c)

- A compiled example in `tests/surface` (guide examples stay out of the packages) gives, for
  `shop` and `addEmailLower`, the refutation of the `SELECT *` read, the two read theorems
  (`namedCustomers`, and the lookup of a customer id by email for every email), and the success
  theorem. It uses only the route of (a) and (b). It replaces the hand proof of
  `DerivedColumnSchemaPremise.lean`: the helpers `siteOf`, `namedKept`, `lookupKept`,
  `select_resolves` and the syntax restatements are deleted (repository rule "Replaced code").
- `docs/guide/agents.md` links the example. It no longer says "150 to 180 lines", and it no
  longer says that no theorem states `Succeeds addEmailLower (·.HasCatalog shop)`. The table of
  laws names the success law and the builder. `skills/belay/SKILL.md` and its templates name them
  where they name `queryPreserves`.
- An agent that follows the page proves the two reads and the success claim. The check is a test
  of the page with a fresh agent, as for PR #373, recorded in the status file. It is not an
  automated test.

## Tests

- The compiled example is a fixture of a Python surface test. The test checks that the module
  compiles without warnings, and that `#print axioms` of each read theorem and of the success
  theorem gives only `propext`, `Classical.choice` and `Quot.sound`.
- The example compiles as a module of a consumer Lake project that requires only the `belay`
  package (as `tests/sql_file_support.py` builds one). This shows that no helper of `tests/surface`
  is necessary.
- Boundary fixtures: the check is false (a `#guard` or a `#guard_msgs` of the failed proof) for
  `SELECT *`, for a column name that exists, for a trigger that fires on the UPDATE, for a value
  with a parameter, and for a value that can fail. For the `STRICT` case of (b), `#sql_check` gives
  `false`.
- A second schema, other than `shop`, with a different table position (the table is not the first
  in the catalog) and a filter of another type, shows that the check is not specific to `shop`.
- `tests/surface_derived_column_test.py` and the other tests that use
  `DerivedColumnSchemaPremise.lean` are updated. Each test has a timeout, and the fixtures take
  less than 60 seconds each.

## Tricky points

- **Quantified fields.** `Site.ReadPreserved.resolvesBefore` and `resolvesAfter` quantify over
  every `ResolveState` with a given catalog, and `Site.contextFree` is
  `Resolved.Expr.ContextFree`, which quantifies over all evaluation contexts
  (`packages/belay-sqlite-model/.../Queries/Evaluation/DerivedColumnTable.lean`). A computation can
  evaluate one state or one context only. The builder needs lemmas that transfer the result:
  resolution of a simple select depends on the catalog only (`resolveStatement_select_table` in
  `Schema/Dispatch/SelectColumnResolution.lean` returns the same state), and a resolved value
  without clock, counter, parameter or subquery reads is context-free.
- **Rows come from the database, facts from the catalog.** All fields of `Site` except
  `table.rows` and `present` depend on the catalog only. `Database.table_of_catalog`
  (`packages/belay/.../Schema/Dispatch/SelectCatalogExecution.lean`) gives `present` from a
  `HasCatalog` premise. The migrated catalog `(site.reached triggers).catalog` depends on the
  catalog and the triggers only.
- **Scripts as data.** `sql` text elaborates to a `Script` whose statements are syntax trees with
  values. A check that takes the scripts themselves needs no restatement, but the kernel must
  reduce the `sql` term to its statements. The shape check must also require the parameter lists
  that the law takes (`migration … addValues updateValues triggers`).
- **Success needs more than the site.** `Site.run_state` assumes that every output has no error
  (`ok`). The success law must prove it: `ALTER TABLE … ADD COLUMN` continues on the site
  (`addColumn_plain_step` assumes a continued step), and the `UPDATE` continues on every row
  (`backfill_step` assumes `noError`). The value can fail through a fallible call
  (`Resolved.Expr.isFallibleCall`), through the type check of a `STRICT` column, and through a
  limit of the model, such as the length of a text. Each one needs a premise or a proof. Triggers
  that the migration registers can fail too, for example with a name that exists. The law can
  cover the migration without triggers only; it then says so in its docstring.
- **The schema of a project is a run of its file.** Since #371, the skill and the page for agents
  define `shop` as `(Database.empty.run (sql_file "db/schema.sql")).db`, not as `db!`. The check
  must work with that form too: the kernel then reduces the run of the file's script to get the
  catalog. The example uses that form, and a test also covers a `db!` schema.
- **Kernel cost.** The hand proof decides each fact with `decide +kernel` on the closed catalog of
  `shop`. One check of all facts must stay within the default `maxHeartbeats`, so that a user
  needs no option.
- **Existing laws.** `DerivedColumnMigration.queryPreserves` and `queryTranslates`
  (`packages/belay/.../Programs/StatementRunLaws/DerivedColumnQueries.lean`), `Site.run_state` and
  `Site.branch_database` (`DerivedColumnMigration.lean`), and `Site` (`Schema/Columns/DerivedColumnMigration.lean`).
  The new laws build on them. Each file stays below 200 lines.
- **A schema that changes with its file.** When the project adds the migration to
  `db/schema.sql`, `shop` changes, and the check of an old migration becomes false (the column
  exists). The build then fails, which is correct; the page for agents already tells the user to
  give old claims their own copy of the old schema.
- **Plain words.** Each new proposition and theorem has its plain-words docstring, with each case in
  which it requires nothing, and a proof sketch where the repository rules require one.
