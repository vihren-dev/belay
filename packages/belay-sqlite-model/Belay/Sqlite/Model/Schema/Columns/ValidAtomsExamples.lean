import Belay.Sqlite.Model.Schema.Rows.ValidAtomsTogether
import Belay.Sqlite.Model.Queries.Preparation.ForeignKeyExamples
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.ValidAtomsExamples

open Belay.Sqlite.Model Syntax Resolution.Examples
open Belay.Sqlite.Model.ForeignKeyExamples (keysOn plain deleteOne run)
open Belay.Sqlite.Model.ForeignKeyExamples renaming name → written

/-- {lit}`CREATE TABLE p(id PRIMARY KEY)`, the child
{lit}`c(x INTEGER NOT NULL CHECK (x > 0) REFERENCES p ON DELETE CASCADE) STRICT`, the INSERT of the
rows 1 and 2 of {lit}`p` and 1 of {lit}`c`, then {lit}`BEGIN`, the upsert
{lit}`INSERT INTO p VALUES(1) ON CONFLICT DO NOTHING`, {lit}`DELETE FROM p WHERE id = 1`, which
deletes the row of {lit}`c`, and {lit}`ROLLBACK`. -/
def strictCascadeSyntax : List Syntax.Statement :=
  [.createTable (name! "p") [plain "id" [.primaryKey false]] [],
   .createTable (name! "c")
     [{ name := Identifier.ofString "x", declaredType := some "INTEGER",
        constraints := [.notNull, .check (.compare .gt (written "x") (.numeric "0")) "x > 0",
          .references (name! "p") [] .cascade .noAction] }] [] { strict := true },
   .insert (name! "p") none [[.numeric "1"], [.numeric "2"]] [], .insert (name! "c") none [[.numeric "1"]] [],
   .begin, .insert (name! "p") none [[.numeric "1"]] [{ target := none, action := .nothing }], deleteOne, .rollback]

/-- The resolved statements of {name}`strictCascadeSyntax` from the empty catalog, without values. -/
def strictCascadeScript : List (Resolved.Statement × List Value) :=
  bindValues (statements (migration [] strictCascadeSyntax keysOn)) []

-- The script resolves to its eight statements, and the run succeeds: ROLLBACK restores the row of `c`.
example : strictCascadeScript.length = 8 ∧
    (match runSql strictCascadeScript {} with
      | .success database => (database.rows.getD 1 []).map (·.values) == [[.integer 1]]
      | .failure .. | .pending .. => false) = true := by decide +kernel

/-- {lit}`CREATE TABLE p(id PRIMARY KEY)`, the child
{lit}`c(x NOT NULL REFERENCES p ON DELETE SET NULL)`, the rows 1 and 2 of {lit}`p` and 1 of
{lit}`c`, then {lit}`DELETE FROM p WHERE id = 1`. SET NULL writes NULL into the NOT NULL column. -/
def setNullSyntax : List Syntax.Statement :=
  [.createTable (name! "p") [plain "id" [.primaryKey false]] [],
   .createTable (name! "c") [plain "x" [.notNull, .references (name! "p") [] .setNull .noAction]] [],
   .insert (name! "p") none [[.numeric "1"], [.numeric "2"]] [], .insert (name! "c") none [[.numeric "1"]] [],
   deleteOne]

/-- The resolved statements of {name}`setNullSyntax` from the empty catalog, without values. -/
def setNullScript : List (Resolved.Statement × List Value) :=
  bindValues (statements (migration [] setNullSyntax keysOn)) []

-- The DELETE fails with a constraint error (SQLite 3.51.0: `NOT NULL constraint failed: c.x`) and
-- keeps the database as it was: both rows of `p` and the row of `c`.
example : run setNullSyntax 0 = (some [[.integer 1], [.integer 2]], true) ∧
    run setNullSyntax 1 = (some [[.integer 1]], true) := by decide +kernel

end Belay.Sqlite.Model.ValidAtomsExamples
