import Belay.Sqlite.Model.Schema.Writes.LiteralInsertFits

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every database, target, keys, table and rows that satisfy {name}`InsertFits`: the outcome of the INSERT
({name}`insertOutcome`) succeeds and stores the table with the rows of {name}`LiteralData.inserted` at the target.
In plain words, rows that fit the table insert without an error. Proof sketch: no row fails the alias check, and the
table with all rows satisfies the constraints of the keys and has distinct rowids, so {name}`insertOutcome` takes the
successful branch of {name}`checkedWrite`. -/
theorem insertOutcome_of_fits {database : Database} {target : Nat} {keys : List UniqueKey} {table : Table}
    {values : List (List Value)} (fits : InsertFits keys table values) :
    insertOutcome database target keys table values (LiteralData.inserted table values) =
      .ok (database.setRows target (LiteralData.inserted table values).rows) := by
  have passes : LiteralData.constraints keys (LiteralData.inserted table values) = true := by
    simp [LiteralData.constraints, fits.notNull, fits.typed, fits.checked, fits.keysDistinct]
  have aliases : values.findIdx? (LiteralData.aliasMismatch table.shape) = none := by
    simpa [List.findIdx?_eq_none_iff] using fits.aliasFree
  simp [insertOutcome, aliases, checkedWrite, passes, fits.rowidsDistinct]

/-- For every keys, table and rows that satisfy {name}`InsertFits`: the support check of the INSERT
({name}`LiteralData.insertReady`) passes. In plain words, the model describes the insertion of rows that fit the
table. Proof sketch: every prefix of the inserted rows satisfies the constraints
({name}`LiteralData.constraints_of_appended`), and the other parts of the check are fields of {name}`InsertFits`. -/
theorem insertReady_of_fits {keys : List UniqueKey} {table : Table} {values : List (List Value)}
    (fits : InsertFits keys table values) :
    LiteralData.insertReady keys table values (LiteralData.inserted table values) = true := by
  have passes : LiteralData.constraints keys (LiteralData.inserted table values) = true := by
    simp [LiteralData.constraints, fits.notNull, fits.typed, fits.checked, fits.keysDistinct]
  obtain ⟨added, appended⟩ := LiteralData.inserted_rows_prefix table values
  have before := LiteralData.constraints_of_appended (LiteralData.shape_inserted table values) appended passes
  simp [LiteralData.insertReady, LiteralData.tableReady, before, fits.aliasInteger, fits.stored, fits.rowidsBounded]

end Belay.Sqlite.Model
