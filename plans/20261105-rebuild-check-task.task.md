# The guide's table rebuild makes the table STRICT

Created: 2026-11-05. Status: DONE (2026-11-05); see the status file.
Audience: the implementation team.
Decided by: the owner, on 2026-11-05, after the launch review found that SQLite
3.53.0 (2026-04-09) adds `ALTER TABLE ... ALTER COLUMN ... SET NOT NULL` and
`ALTER TABLE ... ADD CONSTRAINT ... CHECK (...)`, which do the guide's current task,
"make `customers.name` NOT NULL", and the first replacement, a CHECK constraint, in
one statement each. The example must show a task that no SQLite version can do in
place. The owner chose, on 2026-11-05, to make the table STRICT: SQLite has no
`ALTER TABLE` form for it (<https://www.sqlite.org/syntax/alter-table-stmt.html>),
and sqlite.org prescribes the twelve-step rebuild
(<https://www.sqlite.org/lang_altertable.html#otheralter>).

## What must be true when the task is done

The guide's table rebuild (`tests/surface/RebuildGuide.lean` and the modules that
import it) performs this task: make `customers` a STRICT table, so that SQLite
refuses a value that does not fit the declared type of its column. The rebuilt
table is `CREATE TABLE customers_new (id INTEGER PRIMARY KEY, name TEXT, email TEXT
NOT NULL) STRICT`. The schema of `sample`, its rows, the read `allSessions` and the
order of the nine statements do not change; only the `CREATE TABLE` of the copy
changes, and the names of the scripts and of the premise say what the rebuild does
(`makeStrict`, `makeStrictWrong`, `makeStrictWrongEnforced`, `StrictRows`).

The three claims of the guide hold for the new task, with proofs that pass the
axiom audit of the surface tests:

1. The wrong rebuild on a connection with foreign keys on does not preserve the
   sessions (`sql_refute` on `sample`).
2. The right rebuild preserves `allSessions` on every database whose catalog is the
   schema of `sample` (`Migration.QueryPreserves`).
3. The right rebuild succeeds on every such database in which every customer fits
   the STRICT types of the new table, in every complete environment, on the actual
   run and on every branch. The premise is the model's own test of a row against
   the new table's definition (`LiteralData.typesFit`), so that the theorem says
   exactly what the copy checks: a text or NULL name, a text email, an integer id.
   The definition of the new table in the premise is the one the model builds for
   the `CREATE TABLE` of the copy, taken from the model's run on the sample, and a
   kernel-checked fact in the fixture shows its three STRICT types.

The library law for a copy into an empty table, `InsertFits.copy`, covers a STRICT
target: the copy fits when every source row fits the STRICT types of the target. The
law for a target without STRICT types is the instance in which every column accepts
every value; there is one law, and the surface proof uses it.

The replays agree with pinned SQLite 3.51.0: on a database with a customer whose
email is a blob, the copy fails with the error 19, native SQLite reports `cannot
store BLOB value in TEXT column customers_new.email`, the rebuilt table stays empty,
`PRAGMA foreign_key_check` reports the session, and the commit still runs (checked
on 2026-11-05 with the model and with `sqlite3` 3.51.0). The right rebuild keeps the
session, the wrong one loses it, and the dangling session case is as before.

Every document and test in this repository that names the old scripts or the old
premise uses the new names (`docs/spec-proof-query-observation-targets.md`,
`tests/surface_rebuild_test.py`). The private product repository's guide and launch
outlines are updated in that repository, not here.

## Test suite

`tests/surface_rebuild_test.py`, all five tests: the schema and transaction rules
on `sample`; the four replays against pinned SQLite, with `with-blob` in place of
`without-name` and the expected refusal `cannot store BLOB value in TEXT column`;
`sql_refute` of the wrong rebuild; the two theorems with their axiom audit.
`tests/lean_packages_test.py` for the changed model module. The variation suite of
the launch plan (twelve rebuild variations at the default budget) is a separate
task, because it needs the budget fix of #317 to pass.

## Key points for the implementer

- `InsertFits.copy` (`packages/belay-sqlite-model/Belay/Sqlite/Model/CopyInsertFits.lean`)
  takes `untyped : ∀ column ∈ target.shape.columns, column.strictType = none` and
  discharges the field `typed` with it. Replace that premise with
  `typed : ∀ row ∈ source, LiteralData.typesFit target.shape row = true` and prove
  the field from `LiteralData.typedRows` and `LiteralData.inserted_copy`. The one
  caller is `RebuildSucceedsCopy.copy_continues`.
- `newFacts` (`tests/surface/RebuildCopyFacts.lean`) asserts that no column has a
  STRICT type and that `name` is NOT NULL. The premise of claim 3 must name the
  definition of the new table, so give that definition a name, for example
  `strictShape`, taken from the catalog that the model reaches after the first
  three statements (`reachedAfter 3`, position 2), and let `catalogFacts` assert
  that the table at position 2 is `strictShape` (`CatalogTable` derives
  `DecidableEq`). The properties that the copy proof took from `newFacts` then
  follow from `strictShape` by `decide +kernel`. `copy_resolves` and
  `catalogFacts_reached` show how facts are taken from `reachedAfter 3` by
  evaluation.
- `LiteralData.typesFit shape row` zips the columns of the shape with the cells of
  the row and asks `StrictType.fits` of each column that has a STRICT type; NULL
  fits every type. The old and the new customers have the same three columns with
  the same affinities, so the premise can be stated on the rows of the old table
  with the definition of the new one, and `insertSelectRows_copy` still applies.
  A STRICT TEXT column refuses a blob and accepts an integer (SQLite converts it),
  which is why the failing replay stores a blob and not a number.
- `StrictRows` replaces `NoNullName` (`RebuildSucceeds.lean`), and the premise
  `named` of `copy_continues`, `good_3` and `good_advance`
  (`RebuildSucceedsCopy.lean`, `RebuildSucceedsSteps.lean`, `RebuildSucceedsFinish.lean`)
  becomes the STRICT premise. The NOT NULL case of the copy proof for `name`
  disappears, because `name` stays nullable; the NOT NULL of `email` still comes
  from the valid database. Read the docstrings of `Good`, `Held`, `Kept` and
  `reachedAfter` before editing: they state the facts that every step keeps, and
  the task does not change them.
- `with_unfolding_all rfl` and `decide +kernel` evaluate the model on the sample;
  a changed `CREATE TABLE` changes every such evaluation's input but not its form.
- `RebuildReplays.withoutName` becomes `withBlob`, with a customer whose email is a
  blob literal; the report name and the expected refusal in
  `tests/surface_rebuild_test.py` change with it. The `dangling` replay stays.
- The schema rules fixture `tests/surface/SchemaRuleExamples.lean` imports
  `RebuildGuide.sample` only; it needs no change.
- The repository's rule for replaced code applies: no alias for the old names, no
  second copy law.
