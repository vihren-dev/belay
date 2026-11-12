# SQL claims with Belay

This project proves facts about its SQLite schema and migrations with
[Belay](https://github.com/vihren-dev/belay), a Lean library. The SQL is in
`db/`. The claims are Lean files in `Claims/`. Add an import of each new file
to `Claims.lean`.

- **SQL stays in its files.** Read a file with
  `sql_file "db/migrations/<name>.sql"`. If a library law needs the migration
  as Lean syntax, prove with `rfl` that the syntax is equal to the file.
- **The schema** is the database `shop` of `Claims/Schema.lean`: the text of
  `db/schema.sql` in `db!`, and a theorem that the two are the same database.
  It is the schema before the migration that you add. Do not change it in the
  same change as the migration.
- **State a claim for each SQL change, with the schema in the claim.** For a
  migration `M` and each read `Q` of the application:
  `Migration.QueryPreserves (send M) Q (·.HasCatalog shop)`, and
  `Succeeds M (·.HasCatalog shop)`. The short form `M preserves Q` is about
  every database, also one with other tables and triggers. For a read with a
  parameter, write `def q (email : Value) : Script := sql r"… ?1" email` and
  the claim `∀ email : Value, …`.
- **Check before you prove.** Write `#sql_check` and then the claim itself,
  not the name of a definition that holds it.
  `set_option sql.checkBudget 500000 in` before the command gives the search
  more work. Read the answers of one file with
  `lake --log-level=error lean Claims/<File>.lean`.
- **`proved`:** write the claim as a `theorem` with the proof that the answer
  prints after `Add checked proof example`. Ignore that text when it comes
  after a theorem of yours.
- **`false`:** keep the database of the counterexample as a `db!` definition
  with the statements that the answer prints after `Construction:`. If the
  migration is wrong, fix it. If the migration is right and a read of
  the application must change, change the read and its claim, and prove
  `¬ claim` for the old read with `sql_refute (db := found)`. Then prove the
  new fact on that database with `decide +kernel`.
- **`unknown`** is not `proved`. Try `theorem … := by sql_auto`, and remove
  the theorem if the tactic fails. Then look for a library law
  for the shape of the migration: for `ADD COLUMN` with an `UPDATE` that fills
  the column, `Belay.Sqlite.DerivedColumnMigration.queryPreserves`. If you
  find no proof, report `unknown`.
- **Do not make a claim weaker to pass the check.** A `where` guard, a smaller
  schema, a different read or a different premise changes the claim: report
  each such change.
- **No `sorry` and no new axiom.** Put `#print axioms <theorem>` for each
  theorem at the end of its file. It shows only `propext`, `Classical.choice`
  and `Quot.sound`.
- **Before you finish**, replace each `#sql_check` with its theorem, or with a
  comment that gives the claim and its answer. Then run `lake build` and
  `lake --log-level=error exe belay-sql-check`. Each must exit with 0.
- **Report** each claim as written, with `proved` and the name of the theorem,
  `false` and the counterexample, or `unknown`. Report each change of a claim
  and each change of application code.

The Belay repository is in `.lake/packages/belay/`. Read
`docs/guide/agents.md`, `packages/belay/README.md` and the examples in
`tests/surface/` there. The migration examples are in
`tests/surface/Schema/Tests/`. You cannot import the examples.
