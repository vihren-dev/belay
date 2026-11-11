import Belay.Sqlite.Model.Schema.Rows.KeysUniqueFrame
import Belay.Sqlite.Model.Schema.Dispatch.StatementStep

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every database, position, table and result table: if the database satisfies
{name}`Database.KeysUnique` and has the table at the position, the effect of
{name}`checkedWrite` of the result over the keys of the position ({name}`Database.keys`)
satisfies {name}`Effect.Satisfies` for {name}`Database.KeysUnique`. Proof sketch: a stored result passed
{name}`LiteralData.constraints` for the keys, so {name}`Table.constraints_iff` gives the atom of
its rows, and {name}`Database.KeysUnique.setRows` stores them; a failure keeps the database. -/
theorem checkedWrite_keysUnique {database : Database} (unique : database.KeysUnique) {target : Nat} {table : Table}
    (found : database.table target = some table) (result : Table) :
    (checkedWrite database target (database.keys target table) result).Satisfies Database.KeysUnique := by
  unfold checkedWrite
  split
  · rename_i passed
    simp only [Bool.and_eq_true] at passed
    have stored := ((Table.constraints_iff _ result).mp passed.1).2.2.2
    exact Effect.satisfies_of_effectDatabase (unique.setRows found (stored.frame rfl fun _ member => member))
  · exact Effect.satisfies_of_database unique rfl

/-- For every database, position, table, rows and result table: if the database satisfies
{name}`Database.KeysUnique` and has the table at the position, the effect of
{name}`insertOutcome` over the keys of the position satisfies {name}`Effect.Satisfies` for {name}`Database.KeysUnique`. Proof
sketch: a refused rowid alias fails with the input database, and every other case is
{name}`checkedWrite_keysUnique`. -/
theorem insertOutcome_keysUnique {database : Database} (unique : database.KeysUnique) {target : Nat} {table : Table}
    (found : database.table target = some table) (rows : List (List Value)) (result : Table) :
    (insertOutcome database target (database.keys target table) table rows result).Satisfies Database.KeysUnique := by
  unfold insertOutcome
  split
  · dsimp only
    split <;> exact Effect.satisfies_of_database unique rfl
  · exact checkedWrite_keysUnique unique found result

end Belay.Sqlite.Model
