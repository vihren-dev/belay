import Belay

/-! A fixture of `tests/surface_guide_test.py`: `sql! db r"..."` (`Belay/Sqlite/SqlBang.lean`,
`Belay/Sqlite/EvalDatabase.lean`) shows an error at the database term when the term has no value
while the file elaborates, and no second error when the term uses a definition with an error.
`#guard_msgs (positions := true)` checks each message and its position as
`@ +line:start...stop`, with the line from the command and columns from 0. The file fails to
elaborate when a message or a position is not the expected one. -/

open Belay.Sqlite

/-- A database with the table `invoices`. -/
def shop : Database := (Database.empty.run (sql r"CREATE TABLE invoices (id INTEGER PRIMARY KEY);")).db

-- A database that is a variable has no value while the file elaborates: an error at the term.
/--
@ +1:48...50
error: sql! resolves against the value of the database, but the database term depends on a variable and has no value while the file elaborates; use sql, which resolves when it runs, or a database defined earlier in the file
-/
#guard_msgs (positions := true) in
def onVariable (db : Database) : Script := sql! db r"SELECT id FROM invoices"

-- A database term that Lean cannot fully know while the file elaborates: an error at the term.
/--
@ +1:28...29
error: sql! needs the database term to be fully known while the file elaborates; use a database defined earlier in the file
-/
#guard_msgs (positions := true) in
def onHole : Script := sql! _ r"SELECT id FROM invoices"

-- A local definition inside the term, and one outside it, have a value.
/--
@ +1:63...67
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def onLocal : Script := sql! (let copy := shop; copy) r"SELECT nmae FROM invoices"

/--
@ +1:66...70
error: no such column: nmae
-/
#guard_msgs (positions := true) in
def onOuterLocal : Script := let copy := shop; sql! copy r"SELECT nmae FROM invoices"

-- A database that Lean cannot compute: an error at the term that names the definition.
noncomputable def chosen : Database := Classical.choice ⟨Database.empty⟩

/--
@ +1:37...43
error: sql! cannot compute the database, because it uses the noncomputable definition chosen; use sql, which resolves when it runs, or a database that Lean can compute
-/
#guard_msgs (positions := true) in
def onNoncomputable : Script := sql! chosen r"SELECT id FROM invoices"

-- A definition with an error shows that error, and `sql!` adds no second error, also when it uses
-- the definition through another definition.
/--
@ +1:40...52
error: Invalid field `missingField`: The environment does not contain `Belay.Sqlite.Database.missingField`, so it is not possible to project the field `missingField` from an expression
  Database.empty
of type `Database`
-/
#guard_msgs (positions := true) in
def failed : Database := Database.empty.missingField

/-- A definition without an error of its own that uses {lit}`failed`. -/
def wrapped : Database := failed

#guard_msgs (positions := true) in
def onFailed : Script := sql! failed r"SELECT id FROM invoices"

#guard_msgs (positions := true) in
def onWrapped : Script := sql! wrapped r"SELECT id FROM invoices"

-- A local definition with an error shows only that error.
/--
@ +1:68...80
error: Invalid field `missingField`: The environment does not contain `Belay.Sqlite.Database.missingField`, so it is not possible to project the field `missingField` from an expression
  Database.empty
of type `Database`
-/
#guard_msgs (positions := true) in
def onFailedLocal : Script := let copy : Database := Database.empty.missingField; sql! copy r"SELECT 1"
