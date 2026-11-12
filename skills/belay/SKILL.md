---
name: belay
description: Prove facts about SQLite schemas, migrations and queries with the Lean library Belay. Use when you add or change a migration, a schema or a query of a project that has SQLite, when the user asks whether a migration is safe or can lose data, and when you set up Belay in a project.
---

# SQL claims with Belay

[Belay](https://github.com/vihren-dev/belay) is a Lean library with a model of
SQLite. You state a claim about SQL, a search looks for a database that breaks
the claim, and Lean's kernel checks each proof. The user reviews the claims
and does not read the proofs. Your work is correct claims, proofs without
holes and an honest report.

Paths in this file that start with `.lake/packages/belay/` are in the Belay
repository, which Lake downloads into the project. This file is
`.lake/packages/belay/skills/belay/SKILL.md`, and the templates are in
`templates/` next to it.

## The project

The file `AGENTS.md` or `CLAUDE.md` of the project names three things: the
directory of the SQL files, the directory of the claims and the schema
database. This file uses the names of the templates: `db/`, `Claims/` and
`shop`. Use the names of the project.

If the project has no claims directory with a `Schema.lean`, do
[Set up the project](#set-up-the-project) first.

## Rules

- **SQL stays in its files.** Read a file with
  `sql_file "db/migrations/<name>.sql"`. `sql_file` works only in a file of
  the claims library, so put experiments in a file of `Claims/` also. If a
  library law needs the migration as Lean syntax, prove with `rfl` that the
  syntax is equal to the file.
- **The schema** is the database `shop` of `Claims/Schema.lean`: the database
  that `db/schema.sql` builds, `(Database.empty.run (sql_file "db/schema.sql")).db`.
  It is the schema before the migration that you add. Do not change it in the
  same change as the migration.
- **State a claim for each SQL change, with the schema in the claim.** For a
  migration `M` and each read `Q` of the application:
  `M preserves Q on shop`, and `Succeeds M (·.HasCatalog shop)`. The form
  `M preserves Q`, without `on shop`, is about every database, also one with
  other tables and triggers. For a read with a
  parameter, write `def q (email : Value) : Script := sql r"… ?1" email` and
  the claim `∀ email : Value, …`.
- **Do not make a claim weaker to pass the check.** A `where` guard, a smaller
  schema, a different read or a different premise changes the claim. Report
  each such change.
- **`unknown` is not `proved`.** Only a `theorem` in a file that the build
  compiles is a proof.
- **No `sorry` and no new axiom.** Put `#print axioms <theorem>` for each
  theorem at the end of its file. It shows only `propext`, `Classical.choice`
  and `Quot.sound`. The command of step 4 of the loop prints these lines.

## The loop

1. Change the SQL in its file.
2. Write the claims in a file of `Claims/`, one file for each migration, as
   [`templates/MigrationClaims.lean`](templates/MigrationClaims.lean) shows.
   Add an import of the file to `Claims.lean`.
3. Write `#sql_check` and then the claim itself, not the name of a definition
   that holds it.
4. Read the answers of the file:
   `lake --log-level=error lean Claims/<File>.lean`.
5. Act on each answer, as the next section tells.

## The answers of `#sql_check`

**`proved`:** write the claim as a `theorem` with the proof that the answer
prints after `Add checked proof example`. The check also prints that text for
a theorem of yours that it can prove again. Ignore it there, or put
`set_option sql.check false in` before the theorem.

**`false`:** the answer has a database that breaks the claim, and a script
for the `sqlite3` shell.

1. Keep the database as a `db!` definition. Paste the statements that the
   answer prints after `Construction:`, as printed.
2. If the migration is wrong, fix it, and check the claim again.
3. If the migration is right and a read of the application must change,
   change the read and its claim. Prove `¬ claim` for the old read with
   `sql_refute (db := found)`. Prove the fact about the new read `Q` on that
   database with `decide +kernel`:
   `(found.run Q).outputs = ((found.run M).db.run Q).outputs`.
   Then check the new claim for every database.

**`unknown`:** the search found no proof and no counterexample. This is not
evidence for the claim.

1. Try `theorem … := by sql_auto`. Remove the theorem if the tactic fails.
2. Try the check with more work: put `set_option sql.checkBudget 500000 in`
   before `#sql_check`. A larger budget helps a schema with many tables or a
   migration with many statements. If the answer stays `unknown`, remove the
   option.
3. Look for a library law for the shape of the migration. For `ADD COLUMN`
   with an `UPDATE` that fills the column, see
   [The laws for a filled column](#the-laws-for-a-filled-column).
4. For a claim about the rows that one `SELECT` returns, or about the result
   of an insert or a delete, the tactics `sql_select` and `sql_run` are in
   `.lake/packages/belay/packages/belay/README.md`. They do not prove
   `Migration.QueryPreserves`.
5. For a table rebuild, the proof is by hand. Its pattern starts in
   `.lake/packages/belay/tests/surface/Schema/Tests/RebuildKeeps.lean`, and
   the pattern for `Succeeds` in `RebuildSucceeds.lean` of that directory.
6. If you find no proof, report `unknown`. Do not change the claim to get a
   proof.

### The laws for a filled column

A migration that adds a column and fills it from the other columns of the row
has three laws in `Belay.Sqlite.DerivedColumnMigration`. Each one takes a
check that the kernel evaluates on the catalog of the schema, so the proof is
one line. The migration must be exactly two statements:
`ALTER TABLE t ADD COLUMN c …` and `UPDATE t SET c = value`, with no filter.

```lean
open Belay.Sqlite

theorem named_read_preserved :
    addEmailLower preserves namedCustomers on shop :=
  DerivedColumnMigration.preserves_of_check (by decide +kernel)

theorem lookup_read_preserved : ∀ email : Value,
    addEmailLower preserves (customerIdByEmail email) on shop :=
  DerivedColumnMigration.preserves_of_check_forall customerIdByEmail .null
    (fun _ => rfl) (by decide +kernel)

theorem email_lower_succeeds :
    Succeeds addEmailLower (·.HasCatalog shop) :=
  DerivedColumnMigration.succeeds_of_check (by decide +kernel)
```

- `preserves_of_check` proves a read of the old columns of the table: one
  `SELECT` of the table, with no join, subquery, `*`, grouping, ordering or
  limit. `preserves_of_check_forall` does the same for a read with a value of
  a Lean variable. The third argument proves that the read has the same
  statements for every value; it is `fun _ => rfl` when the variable is only
  a bound value.
- `succeeds_of_check` proves `Succeeds`. Its check is false when the new
  column has a type in a `STRICT` table, or when the value can fail, for
  example with a JSON function.
- The new column has no constraint, and the value reads only old columns of
  the row: no parameter, clock, counter or subquery. A trigger that an
  `UPDATE` of the table fires makes each check false.

When `decide` fails, the check is false. The claim can still be true: it is
outside the laws. Use `#sql_check` for an answer, and report `unknown` if it
gives none. The complete example is
`.lake/packages/belay/tests/surface/Schema/Tests/DerivedColumnOnSchema.lean`.
For a read outside the check, the law `queryPreserves` of the same namespace
takes a `Site` and a `Site.ReadPreserved`. `Site.ofCheck` gives the site, and
you prove the facts of the read by hand.

## Before you finish

1. Replace each `#sql_check` with its theorem, or with a comment that gives
   the claim and its answer.
2. Run `lake build`. It must exit with 0, with no `sorry` warning from the
   files of the project.
3. Run `lake --log-level=error exe belay-sql-check`. It must exit with 0 and
   report `0 stale`. The first run builds the tool. The count of modules in
   the report is the count of files that read SQL files.
4. Read the `#print axioms` lines of each file of claims.

## The report

Report each claim as written, with one of these:

- `proved`, and the name of the theorem;
- `false`, with the counterexample and what you changed;
- `unknown`.

Report each change of a claim and each change of application code. If
`Succeeds` has no theorem, say that the theorems about reads say nothing about
a database on which the migration fails.

## Set up the project

Do this once, when the project has no `Schema.lean` in a claims directory.

1. Find the SQL of the project: the schema file and the directory of the
   migrations. If the project has no schema file, ask the user which SQL
   builds the current schema. Choose a name for the schema database, such as
   the name of the application, and tell the user the three names.
2. Check that `lake` is on the path. If it is not, ask the user to install
   [elan](https://github.com/leanprover/elan).
3. Make the Lake project in the directory of the SQL files or above it. Copy
   [`templates/lakefile.toml`](templates/lakefile.toml), or add its entries to
   the lakefile that exists.
4. Run `lake update`. Then copy `.lake/packages/belay/lean-toolchain` to the
   directory of the lakefile, so that the project and Belay use one version of
   Lean. The first `lake build` compiles Belay and takes minutes.
5. Write `Claims/Schema.lean` from
   [`templates/Schema.lean`](templates/Schema.lean), with the path of the
   schema file, and `Claims.lean` with `import Claims.Schema`. Run
   `lake build`.
6. Add [`templates/AGENTS-stanza.md`](templates/AGENTS-stanza.md) to the
   `AGENTS.md` or `CLAUDE.md` of the project, with the three names. If the
   project has neither file, make `AGENTS.md`.
7. Add `.lake/` to `.gitignore`.

Before `lake update` has run, the templates are at
<https://github.com/vihren-dev/belay/tree/main/skills/belay/templates>.

## Where to read more

- `.lake/packages/belay/docs/guide/agents.md`: the page for the user, with a
  complete session and what the library proves today.
- `.lake/packages/belay/packages/belay/README.md`: the notation, SQL in
  separate files, the tactics and the options of the check.
- `.lake/packages/belay/tests/surface/`: examples that CI compiles. The
  migration examples are in `tests/surface/Schema/Tests/`. You cannot import
  the examples.
