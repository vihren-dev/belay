# The guide's table rebuild adds a CHECK constraint

Created: 2026-11-05. Status: in progress.
Audience: the implementation team.
Decided by: the owner, on 2026-11-05, after the launch review found that SQLite
3.53.0 (2026-04-09) adds `ALTER TABLE ... ALTER COLUMN ... SET NOT NULL`, which
does the guide's current task, "make `customers.name` NOT NULL", in one statement.
The example must show a task that no SQLite version can do in place.

## What must be true when the task is done

The guide's table rebuild (`tests/surface/RebuildGuide.lean` and the modules that
import it) performs this task: every customer's email must contain an `@` after its
first character. The rebuilt table declares
`email TEXT NOT NULL CHECK (instr(email, '@') > 1)`. SQLite's `ALTER TABLE` cannot
add a CHECK constraint, in any version, so the twelve-step rebuild of
<https://www.sqlite.org/lang_altertable.html#otheralter> is the only way. The
schema of `sample`, its rows, the read `allSessions` and the order of the nine
statements do not change; only the `CREATE TABLE` of the copy changes, and the
names of the scripts and of the premise say what the rebuild does
(`requireEmailAt`, `requireEmailAtWrong`, `requireEmailAtWrongEnforced`,
`EmailsHaveAt`).

The three claims of the guide hold for the new task, with proofs that pass the
axiom audit of the surface tests:

1. The wrong rebuild on a connection with foreign keys on does not preserve the
   sessions (`sql_refute` on `sample`).
2. The right rebuild preserves `allSessions` on every database whose catalog is the
   schema of `sample` (`Migration.QueryPreserves`).
3. The right rebuild succeeds on every such database in which every customer passes
   the CHECK, in every complete environment, on the actual run and on every branch.
   The premise is the model's own evaluation of the constraint on the row
   (`LiteralData.checkHolds`), so that the theorem says exactly what the copy
   checks, for every stored value, including a blob in the `email` column.

The library law for a copy into an empty table, `InsertFits.copy`, covers a target
with CHECK constraints: the copy fits when every source row satisfies every CHECK
of the target. The law without CHECK constraints is the instance with no checks;
there is one law, and the surface proof uses it.

The replays agree with pinned SQLite 3.51.0: on a database with a customer whose
email has no `@`, the copy fails with the error 19, native SQLite reports
`CHECK constraint failed`, the rebuilt table stays empty, `PRAGMA
foreign_key_check` reports the session, and the commit still runs. The right
rebuild keeps the session, the wrong one loses it, and the dangling session case
is as before.

Every document and test in this repository that names the old scripts or the old
premise uses the new names (`docs/spec-proof-query-observation-targets.md`,
`tests/surface_rebuild_test.py`). The private product repository's guide and launch
outlines are updated in that repository, not here.

## Test suite

`tests/surface_rebuild_test.py`, all four tests: the schema and transaction rules
on `sample`; the four replays against pinned SQLite, with `without-at` in place of
`without-name` and the expected refusal `CHECK constraint failed`; `sql_refute` of
the wrong rebuild; the two theorems with their axiom audit. `tests/lean_packages_test.py`
for the changed model module. The variation suite of the launch plan (twelve
rebuild variations at the default budget) is a separate task, because it needs the
budget fix of #317 to pass.

## Key points for the implementer

- `InsertFits.copy` (`packages/belay-sqlite-model/Belay/Sqlite/Model/CopyInsertFits.lean`)
  takes `unchecked : target.shape.allChecks = []` and discharges the field
  `checked` with it. Replace that premise with
  `checked : ∀ row ∈ source, ∀ check ∈ target.shape.allChecks, LiteralData.checkHolds row check = true`
  and prove the field from `LiteralData.checkedRows`, `checksHold` and
  `LiteralData.inserted_copy`. The one caller is `RebuildSucceedsCopy.copy_continues`.
- `newFacts` (`tests/surface/RebuildCopyFacts.lean`) asserts
  `shape.allChecks.isEmpty`. It must instead assert the one CHECK of the new table,
  compared with `==` (`CatalogTable` derives `DecidableEq`), so that
  `catalogFacts_reached` still closes by `decide +kernel` and `catalogFacts_unpack`
  hands the constraint to the copy proof. Name the resolved constraint once, for
  example `emailCheck`, as the constraint the model builds for the `CREATE TABLE`
  of the copy; `copy_resolves` and `catalogFacts_reached` show how such facts are
  taken from `reachedAfter 3` by evaluation.
- `LiteralData.checkHolds row check` evaluates `check.condition.eval (.plain 0)
  row.values`, with positions of the new table's columns. The old and the new
  customers have the same three columns in the same order, so the premise of the
  success theorem can be stated on the rows of the old table with the constraint of
  the new one. A NULL result of the condition passes, as in SQLite.
- `EmailsHaveAt` replaces `NoNullName` (`RebuildSucceeds.lean`), and the premise
  `named` of `copy_continues`, `good_3` and `good_advance`
  (`RebuildSucceedsCopy.lean`, `RebuildSucceedsSteps.lean`, `RebuildSucceedsFinish.lean`)
  becomes the CHECK premise. The NOT NULL case of the copy proof for `name`
  disappears; the NOT NULL of `email` still comes from the valid database. Read the
  docstrings of `Good`, `Held`, `Kept` and `reachedAfter` before editing: they state
  the facts that every step keeps, and the task does not change them.
- `with_unfolding_all rfl` and `decide +kernel` evaluate the model on the sample;
  a changed `CREATE TABLE` changes every such evaluation's input but not its form.
  The resolution of the CHECK in `CREATE TABLE` goes through the model's
  `createTable` path; `db!` accepts `instr` and `length` in a CHECK (checked on
  2026-11-05), and refuses `LIKE` and `GLOB` there, so the task uses `instr`.
- `RebuildReplays.withoutName` becomes `withoutAt`, with a customer whose email has
  no `@`; the report name and the expected refusal in `tests/surface_rebuild_test.py`
  change with it. The `dangling` replay stays.
- The schema rules fixture `tests/surface/SchemaRuleExamples.lean` imports
  `RebuildGuide.sample` only; it needs no change beyond the names, if any.
- The repository's rule for replaced code applies: no alias for the old names, no
  second copy law.
