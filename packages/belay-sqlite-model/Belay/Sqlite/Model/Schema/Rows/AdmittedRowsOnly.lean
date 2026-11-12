import Belay.Sqlite.Model.Schema.Rows.AdmittedEngineLaws
import Belay.Sqlite.Model.Schema.Writes.AdmittedUpsertSummary

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The database after is the database, or the database with other rows at the target, where the
target holds a table: for the given database, target and database after, at least one of these holds:
* the database after is the database;
* the database has a table at the target, and there is a list of rows such that the database after is
  {name}`Database.setRows` of the database with these rows at the target. -/
def Database.RowsOnlyAt (database : Database) (target : Nat) (after : Database) : Prop :=
  after = database ∨ ∃ table rows, database.table target = some table ∧ after = database.setRows target rows

/-- For every database, target and rows: if the database has a table at the target, the database with
other rows at the target is {name}`Database.RowsOnlyAt` of the database. Proof sketch: the second
case of the definition. -/
theorem Database.RowsOnlyAt.setRows {database : Database} {target : Nat} {table : Table}
    (found : database.table target = some table) (rows : List Row) :
    database.RowsOnlyAt target (database.setRows target rows) :=
  .inr ⟨table, rows, found, rfl⟩

/-- For every database, target and database after with {name}`Database.RowsOnlyAt`: the catalog of
the database after is the catalog of the database. Proof sketch: {name}`Database.setRows` keeps the
catalog. -/
theorem Database.RowsOnlyAt.catalog {database : Database} {target : Nat} {after : Database}
    (only : database.RowsOnlyAt target after) : after.catalog = database.catalog := by
  rcases only with rfl | ⟨_, _, _, rfl⟩ <;> rfl

/-- For every shaped database, target and database after with {name}`Database.RowsOnlyAt`: the database
after is shaped. Proof sketch: {name}`Database.RowsShaped.setRows` for the second case. -/
theorem Database.RowsOnlyAt.shaped {database : Database} {target : Nat} {after : Database}
    (only : database.RowsOnlyAt target after) (shaped : database.RowsShaped) : after.RowsShaped := by
  rcases only with rfl | ⟨_, rows, found, rfl⟩
  · exact shaped
  · exact shaped.setRows found rows

/-- For every database, target, keys and result table, {name}`checkedWrite` gives a database that is
{name}`Database.RowsOnlyAt` the database, when the database has a table at the target. Proof sketch:
a passed check stores the rows; a failure keeps the database. -/
theorem checkedWrite_rowsOnly {database : Database} {target : Nat} {table : Table}
    (found : database.table target = some table) (keys : List UniqueKey) (result : Table) :
    database.RowsOnlyAt target (effectDatabase (checkedWrite database target keys result)) := by
  unfold checkedWrite
  split
  · exact .setRows found _
  · exact .inl rfl

/-- For every database, target, keys, table, supplied rows and result table, {name}`insertOutcome`
gives a database that is {name}`Database.RowsOnlyAt` the database, when the database has a table at the
target. Proof sketch: a refused rowid alias keeps the database, and the other case is
{name}`checkedWrite_rowsOnly`. -/
theorem insertOutcome_rowsOnly {database : Database} {target : Nat} {table : Table}
    (found : database.table target = some table) (keys : List UniqueKey) (rows : List (List Value))
    (result : Table) :
    database.RowsOnlyAt target (effectDatabase (insertOutcome database target keys table rows result)) := by
  unfold insertOutcome
  split
  · dsimp only
    split <;> exact .inl rfl
  · exact checkedWrite_rowsOnly found keys result

end Belay.Sqlite.Model
