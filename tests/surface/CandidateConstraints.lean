import Belay

open Lean Elab Term Meta Belay.Sqlite

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_search_test.py`: the touched tables of a claim
({lit}`Sampling.touchedNames`) and the rows of the generated candidates that satisfy simple
constraints ({lit}`Sampling.constrainedCells`). -/

namespace CandidateConstraintsFixture

/-- A schema with a foreign key, a trigger that writes another table, NOT NULL and UNIQUE
columns, and a table with a row that no statement of the fixture reads. -/
def schema : Database := db! "
  CREATE TABLE parent(id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE);
  CREATE TABLE child(id INTEGER PRIMARY KEY, parent_id INTEGER NOT NULL REFERENCES parent(id), note TEXT);
  CREATE TABLE audit(entry TEXT);
  CREATE TABLE unrelated(x TEXT);
  CREATE TRIGGER log AFTER DELETE ON child BEGIN INSERT INTO audit VALUES ('deleted'); END;
  INSERT INTO unrelated VALUES ('kept');"

/-- The statement of the fixture's claims: it deletes from the child table. -/
def deleteChild : Script := sql r"DELETE FROM child WHERE id = 1"

/-- Whether the touched tables of the statements are exactly the named tables; for none, whether
every table is touched. -/
def touches (statements : List Model.Syntax.Statement) (expected : Option (List String)) : Bool :=
  match (Sampling.statementsTables statements).bind (Sampling.touchedNames schema.raw.catalog), expected with
  | some names, some expected =>
    names.length == expected.length &&
      expected.all fun name => names.any (·.sameName (Model.Identifier.ofString name))
  | none, none => true
  | _, _ => false

/-- The cells of a column of a table of a candidate, by names. -/
def column (database : Database) (table : String) (position : Nat) : List Value :=
  ((database.rows table).getD []).map (·.getD position .null)

/-- Checks the touched tables of {name}`deleteChild`, that every generated candidate leaves the
untouched table empty, and that the table contents and seeded databases after the targeted
databases satisfy the NOT NULL, UNIQUE and foreign key constraints by construction (a foreign key only
when the parent table has rows), with at least one candidate that has both rows. -/
elab "check_candidate_constraints" : command => Command.liftTermElabM do
  let statements := deleteChild.statements.map (·.1)
  unless touches statements (some ["child", "parent", "audit"]) do
    throwError "the touched tables of the DELETE are not child, its parent and the trigger's table"
  let parentDelete := (sql r"DELETE FROM parent").statements.map (·.1)
  unless touches parentDelete (some ["parent", "child", "audit"]) do
    throwError "a table with a foreign key to a touched table, or its trigger's table, is not touched"
  unless touches ((sql r"ALTER TABLE child ADD COLUMN extra").statements.map (·.1)) none do
    throwError "a statement without named tables does not touch every table"
  let names := (Sampling.statementsTables statements).bind (Sampling.touchedNames schema.raw.catalog)
  let all := Sampling.candidates schema [] names 2 4 0 2 3000
  let targeted := Sampling.touchedTargeted schema [] names 2
  unless all.toList.take targeted.length == targeted do throwError "the targeted databases do not come first"
  for database in all do
    unless column database "unrelated" 0 == [] do throwError "an untouched table has rows"
  for database in all.toList.drop targeted.length do
    let names := column database "parent" 1
    unless !names.any (· matches .null) && names.eraseDups.length == names.length do
      throwError "a parent row breaks NOT NULL or UNIQUE: {names}"
    let parents := column database "parent" 0
    unless parents.isEmpty || (column database "child" 1).all parents.contains do
      throwError "a child row has no parent, although the parent table has rows"
  unless all.any (fun database => column database "child" 0 != [] && column database "parent" 0 != []) do
    throwError "no candidate has a child row and a parent row"
  logInfo m!"candidate constraints passed; {all.size} candidates"

check_candidate_constraints

end CandidateConstraintsFixture
